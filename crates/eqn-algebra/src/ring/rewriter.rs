use std::num::NonZeroUsize;

use eqn_core::op::Commutative;
use eqn_core::rewriter::Rewriter;
use eqn_core::set::Set;

use super::{Ring, RingExpr, SemiRing, SemiRingExpr};
use crate::flatten;

// ================================================================================
// Normalization engine
// ================================================================================

/// Structural order used for canonical sorting under commutativity. Never
/// compares domain elements: constants tie (at most one constant survives
/// folding, so the tie is harmless), which keeps `Ord` off the domain.
fn cmp_structural<SR: SemiRing>(a: &SemiRingExpr<SR>, b: &SemiRingExpr<SR>) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    const fn rank<SR: SemiRing>(e: &SemiRingExpr<SR>) -> u8 {
        match e {
            SemiRingExpr::Const(_) => 0,
            SemiRingExpr::Symbol(_) => 1,
            SemiRingExpr::Pow { .. } => 2,
            SemiRingExpr::Mul(_) => 3,
            SemiRingExpr::Add(_) => 4,
        }
    }

    match (a, b) {
        (SemiRingExpr::Const(_), SemiRingExpr::Const(_)) => Ordering::Equal,
        (SemiRingExpr::Symbol(s), SemiRingExpr::Symbol(o)) => s.cmp(o),
        (
            SemiRingExpr::Pow {
                base: sb,
                exponent: se,
            },
            SemiRingExpr::Pow {
                base: ob,
                exponent: oe,
            },
        ) => cmp_structural(sb, ob).then(se.cmp(oe)),
        (SemiRingExpr::Mul(s), SemiRingExpr::Mul(o))
        | (SemiRingExpr::Add(s), SemiRingExpr::Add(o)) => s
            .iter()
            .zip(o)
            .map(|(i, j)| cmp_structural(i, j))
            .find(|c| *c != Ordering::Equal)
            .unwrap_or(s.len().cmp(&o.len())),
        (a, b) => rank(a).cmp(&rank(b)),
    }
}

/// Moves the expression out, leaving an allocation-free placeholder behind.
fn take<SR: SemiRing>(expr: &mut SemiRingExpr<SR>) -> SemiRingExpr<SR> {
    std::mem::replace(expr, SemiRingExpr::Add(Vec::new()))
}

fn split_add<SR: SemiRing>(e: SemiRingExpr<SR>) -> Result<Vec<SemiRingExpr<SR>>, SemiRingExpr<SR>> {
    match e {
        SemiRingExpr::Add(inner) => Ok(inner),
        e => Err(e),
    }
}

fn split_mul<SR: SemiRing>(e: SemiRingExpr<SR>) -> Result<Vec<SemiRingExpr<SR>>, SemiRingExpr<SR>> {
    match e {
        SemiRingExpr::Mul(inner) => Ok(inner),
        e => Err(e),
    }
}

/// Coefficient table of a sum: the folded constant term, and each distinct
/// core term with its summed coefficient, in first-appearance order.
type Terms<SR> = (
    <<SR as SemiRing>::Domain as Set>::Element,
    Vec<(SemiRingExpr<SR>, <<SR as SemiRing>::Domain as Set>::Element)>,
);

/// Collects normalized summands: folds *all* constants into one, and gathers
/// structurally equal terms into left coefficients summed in the domain
/// (`x + x -> 2 * x`, `2*x + 3*x -> 5*x`). Needs no commutativity: the
/// coefficient is split off the *left* of a product.
fn collect_terms<SR: SemiRing>(summands: impl Iterator<Item = SemiRingExpr<SR>>) -> Terms<SR> {
    let mut acc = SR::ZERO;
    // Like terms keyed by structural Eq with a linear scan; needs neither
    // Ord nor Hash on elements. Coefficients are summed as domain elements,
    // so cancellation (`x + (-1)*x = 0`) works. The scan is quadratic in
    // the number of distinct terms; a hashed index would need `Hash` on
    // the domain.
    let mut coeffs: Vec<(SemiRingExpr<SR>, <SR::Domain as Set>::Element)> = Vec::new();

    for item in summands {
        let (coeff, core) = match item {
            SemiRingExpr::Const(c) => {
                acc = SR::add(acc, c);
                continue;
            }
            SemiRingExpr::Mul(mut factors)
                if matches!(factors.first(), Some(SemiRingExpr::Const(_))) =>
            {
                let SemiRingExpr::Const(c) = factors.remove(0) else {
                    unreachable!()
                };
                let core = if factors.len() == 1 {
                    factors.pop().unwrap()
                } else {
                    SemiRingExpr::Mul(factors)
                };
                (c, core)
            }
            item => (SR::ONE, item),
        };
        match coeffs.iter_mut().find(|(t, _)| *t == core) {
            Some((_, c)) => *c = SR::add(c.clone(), coeff),
            None => coeffs.push((core, coeff)),
        }
    }

    (acc, coeffs)
}

/// Rebuilds a sum from its coefficient table, dropping zero coefficients.
fn build_sum<SR: SemiRing>((acc, coeffs): Terms<SR>) -> SemiRingExpr<SR> {
    let mut out = Vec::new();
    if coeffs.is_empty() || acc != SR::ZERO {
        out.push(SemiRingExpr::Const(acc));
    }
    for (core, coeff) in coeffs {
        // The coefficient can degenerate to zero (cancellation, or finite
        // characteristic like 2x = 0 in Z/2), hence the checks.
        if coeff == SR::ZERO {
            continue;
        }
        if coeff == SR::ONE {
            out.push(core);
        } else {
            let mut factors = vec![SemiRingExpr::Const(coeff)];
            match core {
                SemiRingExpr::Mul(inner) => factors.extend(inner),
                core => factors.push(core),
            }
            out.push(SemiRingExpr::Mul(factors));
        }
    }

    match out.len() {
        // NOTE: everything cancelled; keep the interface total.
        0 => SemiRingExpr::Const(SR::ZERO),
        1 => out.pop().unwrap(),
        _ => SemiRingExpr::Add(out),
    }
}

/// Order-preserving pass over normalized factors: drops ones and folds
/// *adjacent* constants. `None` when a zero factor annihilates the product.
fn fold_adjacent_factors<SR: SemiRing>(
    factors: impl Iterator<Item = SemiRingExpr<SR>>,
) -> Option<Vec<SemiRingExpr<SR>>> {
    let mut stack: Vec<SemiRingExpr<SR>> = Vec::new();

    for item in factors {
        if item == SemiRingExpr::Const(SR::ONE) {
            continue;
        }
        if item == SemiRingExpr::Const(SR::ZERO) {
            return None;
        }
        match (item, stack.pop()) {
            (SemiRingExpr::Const(s), Some(SemiRingExpr::Const(t))) => {
                let c = SR::multiply(t, s);
                // Re-check identities on the folded constant: 2 * 3 = 6 == 0
                // (mod 6) annihilates, and (-1) * (-1) = 1 drops out.
                if c == SR::ZERO {
                    return None;
                }
                if c != SR::ONE {
                    stack.push(SemiRingExpr::Const(c));
                }
            }
            (item, popped) => {
                stack.extend(popped);
                stack.push(item);
            }
        }
    }

    Some(stack)
}

/// If any factor is a sum, expands the product into a sum of products
/// (cartesian product of terms, factor order kept). The result still needs
/// normalizing; terms of a normalized `Add` are never `Add` themselves, so
/// that recursion terminates.
fn distributed<SR: SemiRing>(factors: &[SemiRingExpr<SR>]) -> Option<SemiRingExpr<SR>> {
    if !factors.iter().any(|f| matches!(f, SemiRingExpr::Add(_))) {
        return None;
    }
    let mut products: Vec<Vec<SemiRingExpr<SR>>> = vec![Vec::new()];
    for factor in factors {
        match factor {
            SemiRingExpr::Add(terms) => {
                products = products
                    .into_iter()
                    .flat_map(|p| {
                        terms
                            .iter()
                            .map(|t| {
                                let mut q = p.clone();
                                q.push(t.clone());
                                q
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect();
            }
            f => {
                for p in &mut products {
                    p.push(f.clone());
                }
            }
        }
    }
    Some(SemiRingExpr::Add(
        products.into_iter().map(SemiRingExpr::Mul).collect(),
    ))
}

/// Commutative only: moves every constant to the front folded into one,
/// collects repeated factors into powers (`x * y * x -> x^2 * y`), and sorts
/// the bases structurally. `None` when the folded constant is zero.
fn collect_factors<SR: SemiRing>(factors: Vec<SemiRingExpr<SR>>) -> Option<Vec<SemiRingExpr<SR>>> {
    let (consts, rest): (Vec<_>, Vec<_>) = factors
        .into_iter()
        .partition(|f| matches!(f, SemiRingExpr::Const(_)));
    let mut c_acc = SR::ONE;
    for c in consts {
        let SemiRingExpr::Const(c) = c else {
            unreachable!()
        };
        c_acc = SR::multiply(c_acc, c);
    }
    if c_acc == SR::ZERO {
        return None;
    }

    let mut pows: Vec<(SemiRingExpr<SR>, usize)> = Vec::new();
    for factor in rest {
        let (base, exp) = match factor {
            SemiRingExpr::Pow { base, exponent } => (*base, exponent.get()),
            factor => (factor, 1),
        };
        match pows.iter_mut().find(|(b, _)| *b == base) {
            Some((_, e)) => *e = e.checked_add(exp).expect("exponent overflow"),
            None => pows.push((base, exp)),
        }
    }
    pows.sort_by(|a, b| cmp_structural(&a.0, &b.0));

    let mut out = Vec::new();
    if c_acc != SR::ONE {
        out.push(SemiRingExpr::Const(c_acc));
    }
    for (base, exp) in pows {
        out.push(if exp == 1 {
            base
        } else {
            SemiRingExpr::Pow {
                base: Box::new(base),
                exponent: NonZeroUsize::new(exp).unwrap(),
            }
        });
    }
    Some(out)
}

fn build_product<SR: SemiRing>(mut factors: Vec<SemiRingExpr<SR>>) -> SemiRingExpr<SR> {
    match factors.len() {
        // NOTE: empty product simplifies to one to keep the interface total.
        0 => SemiRingExpr::Const(SR::ONE),
        1 => factors.pop().unwrap(),
        _ => SemiRingExpr::Mul(factors),
    }
}

/// `expr` is `Pow { base, .. }` with `base` normalized: folds constant bases,
/// collapses exponent 1 and nested powers. Bases are not expanded
/// (`(x + y)^2` stays a power).
fn reduce_pow<SR: SemiRing>(expr: &mut SemiRingExpr<SR>) {
    let SemiRingExpr::Pow { base, exponent } = expr else {
        unreachable!()
    };
    let n = *exponent;
    match take(base) {
        SemiRingExpr::Const(c) => {
            let mut acc = c.clone();
            for _ in 1..n.get() {
                acc = SR::multiply(acc, c.clone());
            }
            *expr = SemiRingExpr::Const(acc);
        }
        b if n.get() == 1 => *expr = b,
        SemiRingExpr::Pow {
            base: inner_base,
            exponent: inner,
        } => match inner.checked_mul(n) {
            // (b^m)^n = b^(m*n), by associativity of multiplication.
            Some(mn) => {
                *expr = SemiRingExpr::Pow {
                    base: inner_base,
                    exponent: mn,
                }
            }
            None => {
                **base = SemiRingExpr::Pow {
                    base: inner_base,
                    exponent: inner,
                }
            }
        },
        b => **base = b,
    }
}

/// Normalizes in place using the semi-ring laws only: sums collect like
/// terms in first-appearance order, products keep factor order. Leaves are
/// untouched, children are normalized where they sit, and only nodes whose
/// shape changes are replaced.
fn normalize<SR: SemiRing>(expr: &mut SemiRingExpr<SR>) {
    match expr {
        SemiRingExpr::Const(_) | SemiRingExpr::Symbol(_) => {}
        SemiRingExpr::Add(exprs) => {
            exprs.iter_mut().for_each(normalize);
            *expr = build_sum(collect_terms(flatten(std::mem::take(exprs), split_add)));
        }
        SemiRingExpr::Mul(exprs) => {
            exprs.iter_mut().for_each(normalize);
            let Some(factors) = fold_adjacent_factors(flatten(std::mem::take(exprs), split_mul))
            else {
                *expr = SemiRingExpr::Const(SR::ZERO);
                return;
            };
            if let Some(sum) = distributed(&factors) {
                *expr = sum;
                normalize(expr);
                return;
            }
            *expr = build_product(factors);
        }
        SemiRingExpr::Pow { base, .. } => {
            normalize(base);
            reduce_pow(expr);
        }
    }
}

/// [`normalize`] plus commutative multiplication: terms sort structurally,
/// and products fold all constants into one leading constant and collect
/// repeated factors into sorted powers.
fn normalize_commutative<SR: SemiRing>(expr: &mut SemiRingExpr<SR>) {
    match expr {
        SemiRingExpr::Const(_) | SemiRingExpr::Symbol(_) => {}
        SemiRingExpr::Add(exprs) => {
            exprs.iter_mut().for_each(normalize_commutative);
            let (acc, mut coeffs) = collect_terms(flatten(std::mem::take(exprs), split_add));
            coeffs.sort_by(|a, b| cmp_structural(&a.0, &b.0));
            *expr = build_sum((acc, coeffs));
        }
        SemiRingExpr::Mul(exprs) => {
            exprs.iter_mut().for_each(normalize_commutative);
            let Some(factors) = fold_adjacent_factors(flatten(std::mem::take(exprs), split_mul))
                .and_then(collect_factors)
            else {
                *expr = SemiRingExpr::Const(SR::ZERO);
                return;
            };
            if let Some(sum) = distributed(&factors) {
                *expr = sum;
                normalize_commutative(expr);
                return;
            }
            *expr = build_product(factors);
        }
        SemiRingExpr::Pow { base, .. } => {
            normalize_commutative(base);
            reduce_pow(expr);
        }
    }
}

// ================================================================================
// Formatters
// ================================================================================

/// Canonicalizes [`SemiRingExpr`]s using the semi-ring laws (see
/// [`normalize`]).
#[derive_where::derive_where(Default)]
pub struct SemiRingRewriter<SR: SemiRing> {
    _semi_ring_marker: std::marker::PhantomData<SR>,
}

impl<SR: SemiRing> SemiRingRewriter<SR> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<SR: SemiRing> Rewriter for SemiRingRewriter<SR> {
    type Expr = SemiRingExpr<SR>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr);
    }
}

/// Canonicalizes [`RingExpr`]s: lowers `Neg` to a `-1` coefficient, runs the
/// semi-ring normalization, and lifts back. The canonical form contains no
/// `Neg` (a negated term shows up as a constant coefficient), and every Neg
/// rule (`--x = x`, `-c` folding, `x + (-x) = 0`) falls out of the ordinary
/// constant folding and coefficient collection.
#[derive_where::derive_where(Default)]
pub struct RingRewriter<R: Ring> {
    _ring_marker: std::marker::PhantomData<R>,
}

impl<R: Ring> RingRewriter<R> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<R: Ring> Rewriter for RingRewriter<R> {
    type Expr = RingExpr<R>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        let mut lowered = SemiRingExpr::from(std::mem::replace(expr, RingExpr::Add(Vec::new())));
        normalize(&mut lowered);
        *expr = lowered.into();
    }
}

/// [`RingRewriter`] for rings whose multiplication is also commutative:
/// additionally folds all constants of a product into one leading constant,
/// collects repeated factors into powers (`x * y * x -> x^2 * y`), and sorts
/// factors and terms into a canonical order.
#[derive_where::derive_where(Default)]
pub struct CommutativeRingRewriter<R: Ring> {
    _ring_marker: std::marker::PhantomData<R>,
}

impl<R: Ring> CommutativeRingRewriter<R> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<R: Ring> Rewriter for CommutativeRingRewriter<R>
where
    R::Multiplication: Commutative,
{
    type Expr = RingExpr<R>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        let mut lowered = SemiRingExpr::from(std::mem::replace(expr, RingExpr::Add(Vec::new())));
        normalize_commutative(&mut lowered);
        *expr = lowered.into();
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::op::{Associative, BinaryOperator};

    use super::*;

    #[derive(Set)]
    #[set(element = i64)]
    struct TestDomain;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, symbol = "+", apply = |a, b| a + b, identity = 0, inverse = |a| -a, inverse_symbol = "-")]
    struct TestAdd;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, symbol = "*", apply = |a, b| a * b, identity = 1)]
    struct TestMul;

    struct TestSemiRing;

    impl SemiRing for TestSemiRing {
        type Domain = TestDomain;
        type Addition = TestAdd;
        type Multiplication = TestMul;
    }

    type Expr = SemiRingExpr<TestSemiRing>;
    type RExpr = RingExpr<TestSemiRing>;

    fn expr(src: &str) -> Expr {
        src.parse().unwrap()
    }

    fn ring(src: &str) -> RExpr {
        src.parse().unwrap()
    }

    fn semi_ring_rewrite(src: &str) -> Expr {
        SemiRingRewriter::new().rewrited_expr(expr(src))
    }

    fn ring_rewrite(src: &str) -> RExpr {
        RingRewriter::new().rewrited_expr(ring(src))
    }

    fn commutative_ring_rewrite(src: &str) -> RExpr {
        CommutativeRingRewriter::new().rewrited_expr(ring(src))
    }

    #[test]
    fn test_simplify_add_mul_pow() {
        assert_eq!(semi_ring_rewrite("1 + 2 * 3 + x + 0 + 2^3"), expr("15 + x"));
    }

    #[test]
    fn test_simplify_mul_annihilation_and_identity() {
        assert_eq!(semi_ring_rewrite("x * 0 * y"), expr("0"));
        assert_eq!(semi_ring_rewrite("1 * x"), expr("x"));
    }

    #[test]
    fn test_distribution_and_collection() {
        assert_eq!(
            semi_ring_rewrite("(1 + x) * (1 + x)"),
            expr("1 + 2 x + x x")
        );
        assert_eq!(semi_ring_rewrite("x + x + y + x"), expr("3 x + y"));
    }

    #[test]
    fn test_coefficient_folding() {
        assert_eq!(semi_ring_rewrite("2 x + 3 x"), expr("5 x"));
    }

    #[test]
    fn test_simplify_pow() {
        assert_eq!(semi_ring_rewrite("(x^2)^3"), expr("x^6"));
        assert_eq!(semi_ring_rewrite("x^1"), expr("x"));
    }

    #[test]
    fn test_ring_rewriter_neg() {
        assert_eq!(ring_rewrite("x + -x"), ring("0"));
        assert_eq!(ring_rewrite("-(-x)"), ring("x"));
        assert_eq!(ring_rewrite("-(3)"), ring("-3"));
        assert_eq!(ring_rewrite("2 x - 5 x"), ring("-3 x"));
    }

    #[test]
    fn test_commutative_ring_rewriter() {
        assert_eq!(commutative_ring_rewrite("x y + y x"), ring("2 x y"));
        assert_eq!(commutative_ring_rewrite("y x 2 x"), ring("2 x^2 y"));
    }

    fn assert_idempotent<R: Rewriter>(rewriter: &R, expr: R::Expr)
    where
        R::Expr: PartialEq + std::fmt::Debug + Clone,
    {
        let once = rewriter.rewrited_expr(expr);
        assert_eq!(rewriter.rewrited_expr(once.clone()), once);
    }

    #[test]
    fn normalize_is_idempotent() {
        let semi_ring_inputs = [
            expr("0"),
            Expr::Add(vec![]),
            expr("x + x + 2"),
            expr("2 (x + y) x"),
            expr("(x + y)^2"),
            expr("x 0"),
        ];
        for expr in semi_ring_inputs {
            assert_idempotent(&SemiRingRewriter::new(), expr);
        }

        let ring_inputs = [
            ring("x + -x"),
            ring("-(-x)"),
            ring("-(3) (x - y) y"),
            ring("(-x)^2"),
        ];
        for expr in ring_inputs {
            assert_idempotent(&RingRewriter::new(), expr.clone());
            assert_idempotent(&CommutativeRingRewriter::new(), expr);
        }
    }
}
