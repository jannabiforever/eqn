use std::num::NonZeroUsize;

use super::{Ring, RingExpr, SemiRing, SemiRingExpr};
use crate::flatten;
use crate::op::Commutative;
use crate::rewriter::Rewriter;
use crate::set::Set;

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

/// The normalization engine shared by every formatter, using the semi-ring
/// laws; `commutative` additionally assumes commutative multiplication.
///
/// - `Add` (commutative monoid): flattens, folds *all* constants into one
///   leading constant, drops zeros, and collects structurally equal terms into
///   left coefficients summed in the domain (`x + x -> 2 * x`, `2*x + 3*x ->
///   5*x`, a zero coefficient cancels the term). Terms keep first-appearance
///   order, or sort structurally when `commutative`.
/// - `Mul` (monoid): flattens, folds *adjacent* constants, drops ones,
///   annihilates the whole product on a zero factor, and distributes over `Add`
///   factors. When `commutative`: folds *all* constants into one leading
///   constant and collects repeated factors into sorted powers (`x * y * x ->
///   x^2 * y`).
/// - `Pow`: folds constant bases, collapses exponent 1 and nested powers. Bases
///   are formatted but not expanded (`(x + y)^2` stays a power).
///
/// Works in place: leaves are untouched, children are normalized where they
/// sit, and only nodes whose shape changes are replaced.
fn normalize<SR: SemiRing>(expr: &mut SemiRingExpr<SR>, commutative: bool) {
    match expr {
        SemiRingExpr::Const(_) | SemiRingExpr::Symbol(_) => {}
        SemiRingExpr::Add(exprs) => {
            exprs.iter_mut().for_each(|e| normalize(e, commutative));
            let split = |e| match e {
                SemiRingExpr::Add(inner) => Ok(inner),
                e => Err(e),
            };

            let mut acc = SR::ZERO;
            // Like terms keyed by structural Eq with a linear scan; needs
            // neither Ord nor Hash on elements. Coefficients are summed as
            // domain elements, so cancellation (`x + (-1)*x = 0`) works.
            // ponytail: O(n^2) in term count; fine for expression trees.
            let mut coeffs: Vec<(SemiRingExpr<SR>, <SR::Domain as Set>::Element)> = Vec::new();

            for item in flatten(std::mem::take(exprs), split) {
                // Split a leading constant off a product as the term's
                // coefficient (left coefficient; needs no commutativity).
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

            if commutative {
                coeffs.sort_by(|a, b| cmp_structural(&a.0, &b.0));
            }

            let mut out = Vec::new();
            if coeffs.is_empty() || acc != SR::ZERO {
                out.push(SemiRingExpr::Const(acc));
            }
            for (core, coeff) in coeffs {
                // The coefficient can degenerate to zero (cancellation, or
                // finite characteristic like 2x = 0 in Z/2), hence the checks.
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

            *expr = match out.len() {
                // NOTE: everything cancelled; keep the interface total.
                0 => SemiRingExpr::Const(SR::ZERO),
                1 => out.pop().unwrap(),
                _ => SemiRingExpr::Add(out),
            };
        }
        SemiRingExpr::Mul(exprs) => {
            exprs.iter_mut().for_each(|e| normalize(e, commutative));
            let split = |e| match e {
                SemiRingExpr::Mul(inner) => Ok(inner),
                e => Err(e),
            };

            let mut stack: Vec<SemiRingExpr<SR>> = Vec::with_capacity(exprs.len());
            for item in flatten(std::mem::take(exprs), split) {
                if item == SemiRingExpr::Const(SR::ONE) {
                    continue;
                }
                // Annihilation: a zero factor kills the whole product.
                if item == SemiRingExpr::Const(SR::ZERO) {
                    *expr = SemiRingExpr::Const(SR::ZERO);
                    return;
                }
                match (item, stack.pop()) {
                    (SemiRingExpr::Const(s), Some(SemiRingExpr::Const(t))) => {
                        let c = SR::multiply(t, s);
                        // Re-check identities on the folded constant:
                        // 2 * 3 = 6 == 0 (mod 6) annihilates, and
                        // (-1) * (-1) = 1 drops out.
                        if c == SR::ZERO {
                            *expr = SemiRingExpr::Const(SR::ZERO);
                            return;
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

            // Distribute over Add factors: expand the cartesian product of
            // terms, keeping factor order (no commutativity assumed), then
            // re-format the resulting sum. Terms of a formatted Add are
            // never Add themselves, so this recursion terminates.
            if stack.iter().any(|f| matches!(f, SemiRingExpr::Add(_))) {
                let mut products: Vec<Vec<SemiRingExpr<SR>>> = vec![Vec::new()];
                for factor in stack {
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
                *expr = SemiRingExpr::Add(products.into_iter().map(SemiRingExpr::Mul).collect());
                normalize(expr, commutative);
                return;
            }

            if commutative {
                // Commute all constants to the front and fold them into one.
                let (consts, factors): (Vec<_>, Vec<_>) = stack
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
                    *expr = SemiRingExpr::Const(SR::ZERO);
                    return;
                }

                // Collect repeated factors into powers: x * x^2 -> x^3.
                // ponytail: exponents summed with plain +; overflow is not a
                // realistic concern for expression trees.
                let mut pows: Vec<(SemiRingExpr<SR>, usize)> = Vec::new();
                for factor in factors {
                    let (base, exp) = match factor {
                        SemiRingExpr::Pow { base, exponent } => (*base, exponent.get()),
                        factor => (factor, 1),
                    };
                    match pows.iter_mut().find(|(b, _)| *b == base) {
                        Some((_, e)) => *e += exp,
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
                stack = out;
            }

            *expr = match stack.len() {
                // NOTE: empty product simplifies to one to keep the interface total.
                0 => SemiRingExpr::Const(SR::ONE),
                1 => stack.pop().unwrap(),
                _ => SemiRingExpr::Mul(stack),
            };
        }
        SemiRingExpr::Pow { base, exponent } => {
            let n = *exponent;
            normalize(base, commutative);
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
        normalize(expr, false);
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
        normalize(&mut lowered, false);
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
        normalize(&mut lowered, true);
        *expr = lowered.into();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{Associative, BinaryOperator};
    use crate::symbol::Symbol;

    #[derive(Set)]
    #[set(element = i64)]
    struct TestDomain;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
    struct TestAdd;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, apply = |a, b| a * b, identity = 1)]
    struct TestMul;

    struct TestSemiRing;

    impl SemiRing for TestSemiRing {
        type Domain = TestDomain;
        type Addition = TestAdd;
        type Multiplication = TestMul;
    }

    type Expr = SemiRingExpr<TestSemiRing>;
    type RExpr = RingExpr<TestSemiRing>;

    fn fmt(expr: Expr) -> Expr {
        SemiRingRewriter::new().rewrited_expr(expr)
    }

    #[test]
    fn test_simplify_add_mul_pow() {
        let x = Symbol::new("x");
        // 1 + (2 * 3) + x + 0 + (2)^3  ==>  15 + x
        let expr = Expr::Add(vec![
            Expr::Const(1),
            Expr::Mul(vec![Expr::Const(2), Expr::Const(3)]),
            Expr::Symbol(x.clone()),
            Expr::Const(0),
            Expr::Pow {
                base: Box::new(Expr::Add(vec![Expr::Const(2)])),
                exponent: NonZeroUsize::new(3).unwrap(),
            },
        ]);

        assert!(fmt(expr) == Expr::Add(vec![Expr::Const(15), Expr::Symbol(x)]));
    }

    #[test]
    fn test_simplify_mul_annihilation_and_identity() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");

        // x * 0 * y ==> 0
        let zero = Expr::Mul(vec![
            Expr::Symbol(x.clone()),
            Expr::Const(0),
            Expr::Symbol(y),
        ]);
        assert!(fmt(zero) == Expr::Const(0));

        // 1 * x ==> x
        let ident = Expr::Mul(vec![Expr::Const(1), Expr::Symbol(x.clone())]);
        assert!(fmt(ident) == Expr::Symbol(x));
    }

    #[test]
    fn test_distribution_and_collection() {
        let x = Symbol::new("x");

        // (1 + x) * (1 + x) ==> 1 + 2*x + x*x
        let expr = Expr::Mul(vec![
            Expr::Add(vec![Expr::Const(1), Expr::Symbol(x.clone())]),
            Expr::Add(vec![Expr::Const(1), Expr::Symbol(x.clone())]),
        ]);

        assert!(
            fmt(expr)
                == Expr::Add(vec![
                    Expr::Const(1),
                    Expr::Mul(vec![Expr::Const(2), Expr::Symbol(x.clone())]),
                    Expr::Mul(vec![Expr::Symbol(x.clone()), Expr::Symbol(x.clone())]),
                ])
        );

        // x + x + y + x ==> 3*x + y
        let y = Symbol::new("y");
        let expr = Expr::Add(vec![
            Expr::Symbol(x.clone()),
            Expr::Symbol(x.clone()),
            Expr::Symbol(y.clone()),
            Expr::Symbol(x.clone()),
        ]);

        assert!(
            fmt(expr)
                == Expr::Add(vec![
                    Expr::Mul(vec![Expr::Const(3), Expr::Symbol(x)]),
                    Expr::Symbol(y),
                ])
        );
    }

    #[test]
    fn test_coefficient_folding() {
        let x = Symbol::new("x");

        // 2*x + 3*x ==> 5*x
        let expr = Expr::Add(vec![
            Expr::Mul(vec![Expr::Const(2), Expr::Symbol(x.clone())]),
            Expr::Mul(vec![Expr::Const(3), Expr::Symbol(x.clone())]),
        ]);
        assert!(fmt(expr) == Expr::Mul(vec![Expr::Const(5), Expr::Symbol(x)]));
    }

    #[test]
    fn test_simplify_pow() {
        let x = Symbol::new("x");

        // (x^2)^3 ==> x^6
        let nested = Expr::Pow {
            base: Box::new(Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: NonZeroUsize::new(2).unwrap(),
            }),
            exponent: NonZeroUsize::new(3).unwrap(),
        };
        assert!(
            fmt(nested)
                == Expr::Pow {
                    base: Box::new(Expr::Symbol(x.clone())),
                    exponent: NonZeroUsize::new(6).unwrap(),
                }
        );

        // x^1 ==> x
        let first = Expr::Pow {
            base: Box::new(Expr::Symbol(x.clone())),
            exponent: NonZeroUsize::new(1).unwrap(),
        };
        assert!(fmt(first) == Expr::Symbol(x));
    }

    #[test]
    fn test_ring_rewriter_neg() {
        let f = RingRewriter::new();
        let x = Symbol::new("x");

        // x + (-x) ==> 0
        let cancel = RExpr::Add(vec![
            RExpr::Symbol(x.clone()),
            RExpr::Neg(Box::new(RExpr::Symbol(x.clone()))),
        ]);
        assert!(f.rewrited_expr(cancel) == RExpr::Const(0));

        // --x ==> x
        let double = RExpr::Neg(Box::new(RExpr::Neg(Box::new(RExpr::Symbol(x.clone())))));
        assert!(f.rewrited_expr(double) == RExpr::Symbol(x.clone()));

        // -(3) ==> -3
        assert!(f.rewrited_expr(RExpr::Neg(Box::new(RExpr::Const(3)))) == RExpr::Const(-3));

        // 2*x + -(5*x) ==> -3*x
        let diff = RExpr::Add(vec![
            RExpr::Mul(vec![RExpr::Const(2), RExpr::Symbol(x.clone())]),
            RExpr::Neg(Box::new(RExpr::Mul(vec![
                RExpr::Const(5),
                RExpr::Symbol(x.clone()),
            ]))),
        ]);
        assert!(f.rewrited_expr(diff) == RExpr::Mul(vec![RExpr::Const(-3), RExpr::Symbol(x)]));
    }

    #[test]
    fn test_commutative_ring_rewriter() {
        let f = CommutativeRingRewriter::new();
        let x = Symbol::new("x");
        let y = Symbol::new("y");

        // x*y + y*x ==> 2*x*y
        let sum = RExpr::Add(vec![
            RExpr::Mul(vec![RExpr::Symbol(x.clone()), RExpr::Symbol(y.clone())]),
            RExpr::Mul(vec![RExpr::Symbol(y.clone()), RExpr::Symbol(x.clone())]),
        ]);
        assert!(
            f.rewrited_expr(sum)
                == RExpr::Mul(vec![
                    RExpr::Const(2),
                    RExpr::Symbol(x.clone()),
                    RExpr::Symbol(y.clone()),
                ])
        );

        // y * x * 2 * x ==> 2 * x^2 * y
        let prod = RExpr::Mul(vec![
            RExpr::Symbol(y.clone()),
            RExpr::Symbol(x.clone()),
            RExpr::Const(2),
            RExpr::Symbol(x.clone()),
        ]);
        assert!(
            f.rewrited_expr(prod)
                == RExpr::Mul(vec![
                    RExpr::Const(2),
                    RExpr::Pow {
                        base: Box::new(RExpr::Symbol(x)),
                        exponent: NonZeroUsize::new(2).unwrap(),
                    },
                    RExpr::Symbol(y),
                ])
        );
    }
}
