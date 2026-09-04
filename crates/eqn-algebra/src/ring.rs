use std::collections::HashSet;
use std::num::NonZeroUsize;

use crate::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
use crate::rewriter::{Expression, Rewriter, flatten};
use crate::set::Set;
use crate::symbol::Symbol;

// ================================================================================
// Ring
// ================================================================================

/// A semi-ring: addition forms a commutative monoid, multiplication forms a
/// monoid. Distributivity and annihilation (`0 * a = 0`) relate the two
/// operators and cannot be encoded as bounds; they are part of the contract.
pub trait SemiRing {
    type Domain: Set;

    /// The addition operator for this semi-ring.
    ///
    /// Should be associative, commutative, and have an identity element.
    type Addition: BinaryOperator<Domain = Self::Domain> + Associative + Commutative + Identity;

    /// The multiplication operator for this semi-ring.
    ///
    /// Should be associative and have an identity element.
    type Multiplication: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    const ZERO: <Self::Domain as Set>::Element = <Self::Addition as Identity>::IDENTITY;

    const ONE: <Self::Domain as Set>::Element = <Self::Multiplication as Identity>::IDENTITY;

    fn add(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Addition as BinaryOperator>::apply(a, b)
    }

    fn multiply(
        a: <Self::Domain as Set>::Element,
        b: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Multiplication as BinaryOperator>::apply(a, b)
    }
}

/// A ring: a semi-ring whose addition also has inverses.
pub trait Ring: SemiRing {
    /// The additive inverse.
    fn negate(a: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element;
}

/// Any semi-ring with invertible addition is a ring for free.
impl<SR: SemiRing> Ring for SR
where
    SR::Addition: Inverse,
{
    fn negate(a: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element {
        <SR::Addition as Inverse>::inverse(a)
    }
}

/// An expression tree over a semi-ring: constants, named symbols, n-ary sums
/// and products, and powers (repeated multiplication, exponent >= 1).
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum SemiRingExpr<SR: SemiRing> {
    Const(<SR::Domain as Set>::Element),
    Symbol(Symbol<SR::Domain>),
    Add(Vec<SemiRingExpr<SR>>),
    Mul(Vec<SemiRingExpr<SR>>),
    Pow {
        base: Box<SemiRingExpr<SR>>,
        exponent: NonZeroUsize,
    },
}

impl<SR: SemiRing> Expression for SemiRingExpr<SR> {
    type Domain = SR::Domain;

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                SemiRingExpr::Const(_) => continue,
                SemiRingExpr::Symbol(symbol) => {
                    visited.insert(symbol);
                }
                SemiRingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                SemiRingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                SemiRingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                SemiRingExpr::Const(_) => continue,
                SemiRingExpr::Symbol(symbol) if *symbol == sym => *e = expr.clone(),
                SemiRingExpr::Symbol(_) => continue,
                SemiRingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                SemiRingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                SemiRingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
    }
}

impl<D: Set, SR: SemiRing<Domain = D>> From<Symbol<D>> for SemiRingExpr<SR> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

// ================================================================================
// Ring expressions
// ================================================================================

/// An expression tree over a ring; `Neg` is the additive inverse, which is
/// what distinguishes it from [`SemiRingExpr`].
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum RingExpr<R: Ring> {
    Const(<R::Domain as Set>::Element),
    Symbol(Symbol<R::Domain>),
    Neg(Box<RingExpr<R>>),
    Add(Vec<RingExpr<R>>),
    Mul(Vec<RingExpr<R>>),
    Pow {
        base: Box<RingExpr<R>>,
        exponent: NonZeroUsize,
    },
}

impl<R: Ring> Expression for RingExpr<R> {
    type Domain = R::Domain;

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                RingExpr::Const(_) => continue,
                RingExpr::Symbol(symbol) => {
                    visited.insert(symbol);
                }
                RingExpr::Neg(e) => to_visit.push(e),
                RingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                RingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter()),
                RingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                RingExpr::Const(_) => continue,
                RingExpr::Symbol(symbol) if *symbol == sym => *e = expr.clone(),
                RingExpr::Symbol(_) => continue,
                RingExpr::Neg(e) => to_visit.push(e),
                RingExpr::Add(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                RingExpr::Mul(semi_ring_exprs) => to_visit.extend(semi_ring_exprs.iter_mut()),
                RingExpr::Pow { base, .. } => to_visit.push(base),
            }
        }
    }
}

impl<R: Ring> From<Symbol<R::Domain>> for RingExpr<R> {
    fn from(sym: Symbol<R::Domain>) -> Self {
        Self::Symbol(sym)
    }
}

// ================================================================================
// Normalization engine
// ================================================================================

/// One level of an expression tree as the engine sees it. `Neg` only appears
/// in the borrowed view; the owned and mutable views lower it to a `-1`
/// coefficient first (see [`SemiRingTree`]).
enum Node<C, S, L, P> {
    Const(C),
    Symbol(S),
    Add(L),
    Mul(L),
    Pow(P, NonZeroUsize),
    Neg(P),
}

type Elem<E> = <<<E as SemiRingTree>::SR as SemiRing>::Domain as Set>::Element;
type Sym<E> = Symbol<<<E as SemiRingTree>::SR as SemiRing>::Domain>;
type Owned<E> = Node<Elem<E>, Sym<E>, Vec<E>, Box<E>>;
type Ref<'a, E> = Node<&'a Elem<E>, &'a Sym<E>, &'a [E], &'a E>;
type Mut<'a, E> = Node<&'a mut Elem<E>, &'a mut Sym<E>, &'a mut Vec<E>, &'a mut Box<E>>;

/// The tree shape shared by [`SemiRingExpr`] and [`RingExpr`], so that one
/// engine serves both without converting between them. Ring trees lower
/// `Neg(x)` to `(-1) * x` (`-1` = the additive inverse of one, central in
/// every ring) as they are viewed, so the engine only ever handles the five
/// semi-ring node kinds.
trait SemiRingTree: Clone + PartialEq + Sized {
    type SR: SemiRing;

    fn node(&self) -> Ref<'_, Self>;
    fn node_mut(&mut self) -> Mut<'_, Self>;
    fn into_node(self) -> Owned<Self>;
    fn from_node(node: Owned<Self>) -> Self;
}

impl<SR: SemiRing> SemiRingTree for SemiRingExpr<SR> {
    type SR = SR;

    fn node(&self) -> Ref<'_, Self> {
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, *exponent),
        }
    }

    fn node_mut(&mut self) -> Mut<'_, Self> {
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, *exponent),
        }
    }

    fn into_node(self) -> Owned<Self> {
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, exponent),
        }
    }

    fn from_node(node: Owned<Self>) -> Self {
        match node {
            Node::Const(c) => Self::Const(c),
            Node::Symbol(s) => Self::Symbol(s),
            Node::Add(v) => Self::Add(v),
            Node::Mul(v) => Self::Mul(v),
            Node::Pow(base, exponent) => Self::Pow { base, exponent },
            Node::Neg(_) => unreachable!("semi-rings have no negation"),
        }
    }
}

impl<R: Ring> SemiRingTree for RingExpr<R> {
    type SR = R;

    fn node(&self) -> Ref<'_, Self> {
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Neg(x) => Node::Neg(x),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, *exponent),
        }
    }

    fn node_mut(&mut self) -> Mut<'_, Self> {
        if let Self::Neg(_) = self {
            let Self::Neg(inner) = std::mem::replace(self, Self::Add(Vec::new())) else {
                unreachable!()
            };
            *self = Self::Mul(vec![Self::Const(R::negate(R::ONE)), *inner]);
        }
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Neg(_) => unreachable!("lowered above"),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, *exponent),
        }
    }

    fn into_node(self) -> Owned<Self> {
        match self {
            Self::Const(c) => Node::Const(c),
            Self::Symbol(s) => Node::Symbol(s),
            Self::Neg(x) => Node::Mul(vec![Self::Const(R::negate(R::ONE)), *x]),
            Self::Add(v) => Node::Add(v),
            Self::Mul(v) => Node::Mul(v),
            Self::Pow { base, exponent } => Node::Pow(base, exponent),
        }
    }

    fn from_node(node: Owned<Self>) -> Self {
        match node {
            Node::Const(c) => Self::Const(c),
            Node::Symbol(s) => Self::Symbol(s),
            Node::Neg(x) => Self::Neg(x),
            Node::Add(v) => Self::Add(v),
            Node::Mul(v) => Self::Mul(v),
            Node::Pow(base, exponent) => Self::Pow { base, exponent },
        }
    }
}

fn constant<E: SemiRingTree>(c: Elem<E>) -> E {
    E::from_node(Node::Const(c))
}

fn is_const<E: SemiRingTree>(e: &E, c: &Elem<E>) -> bool {
    matches!(e.node(), Node::Const(x) if x == c)
}

/// Moves the expression out, leaving an allocation-free placeholder behind.
fn take<E: SemiRingTree>(expr: &mut E) -> E {
    std::mem::replace(expr, E::from_node(Node::Add(Vec::new())))
}

fn split_add<E: SemiRingTree>(e: E) -> Result<Vec<E>, E> {
    match e.into_node() {
        Node::Add(inner) => Ok(inner),
        n => Err(E::from_node(n)),
    }
}

fn split_mul<E: SemiRingTree>(e: E) -> Result<Vec<E>, E> {
    match e.into_node() {
        Node::Mul(inner) => Ok(inner),
        n => Err(E::from_node(n)),
    }
}

/// Structural order used for canonical sorting under commutativity. Never
/// compares domain elements: constants tie (at most one constant survives
/// folding, so the tie is harmless), which keeps `Ord` off the domain.
fn cmp_structural<E: SemiRingTree>(a: &E, b: &E) -> std::cmp::Ordering {
    use std::cmp::Ordering;

    const fn rank<C, S, L, P>(n: &Node<C, S, L, P>) -> u8 {
        match n {
            Node::Const(_) => 0,
            Node::Symbol(_) => 1,
            Node::Pow(..) => 2,
            Node::Mul(_) => 3,
            Node::Add(_) => 4,
            Node::Neg(_) => 5,
        }
    }

    match (a.node(), b.node()) {
        (Node::Const(_), Node::Const(_)) => Ordering::Equal,
        (Node::Symbol(s), Node::Symbol(o)) => s.cmp(o),
        (Node::Pow(sb, se), Node::Pow(ob, oe)) => cmp_structural(sb, ob).then(se.cmp(&oe)),
        (Node::Neg(s), Node::Neg(o)) => cmp_structural(s, o),
        (Node::Mul(s), Node::Mul(o)) | (Node::Add(s), Node::Add(o)) => s
            .iter()
            .zip(o)
            .map(|(i, j)| cmp_structural(i, j))
            .find(|c| *c != Ordering::Equal)
            .unwrap_or(s.len().cmp(&o.len())),
        (a, b) => rank(&a).cmp(&rank(&b)),
    }
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
/// - `Neg` (rings only): lowered to a `-1` coefficient on the way in, so every
///   Neg rule (`--x = x`, `-c` folding, `x + (-x) = 0`) falls out of constant
///   folding and coefficient collection. The canonical form contains no `Neg`.
///
/// Works in place: leaves are untouched, children are normalized where they
/// sit, and only nodes whose shape changes are replaced.
fn normalize<E: SemiRingTree>(expr: &mut E, commutative: bool) {
    match expr.node_mut() {
        Node::Const(_) | Node::Symbol(_) | Node::Neg(_) => {}
        Node::Add(exprs) => {
            exprs.iter_mut().for_each(|e| normalize(e, commutative));

            let mut acc = <E::SR>::ZERO;
            // Like terms keyed by structural Eq with a linear scan; needs
            // neither Ord nor Hash on elements. Coefficients are summed as
            // domain elements, so cancellation (`x + (-1)*x = 0`) works.
            // ponytail: O(n^2) in term count; fine for expression trees.
            let mut coeffs: Vec<(E, Elem<E>)> = Vec::new();

            for item in flatten(std::mem::take(exprs), split_add) {
                // Split a leading constant off a product as the term's
                // coefficient (left coefficient; needs no commutativity).
                let (coeff, core) = match item.into_node() {
                    Node::Const(c) => {
                        acc = <E::SR>::add(acc, c);
                        continue;
                    }
                    Node::Mul(mut factors)
                        if matches!(factors.first().map(E::node), Some(Node::Const(_))) =>
                    {
                        let Node::Const(c) = factors.remove(0).into_node() else {
                            unreachable!()
                        };
                        let core = if factors.len() == 1 {
                            factors.pop().unwrap()
                        } else {
                            E::from_node(Node::Mul(factors))
                        };
                        (c, core)
                    }
                    n => (<E::SR>::ONE, E::from_node(n)),
                };
                match coeffs.iter_mut().find(|(t, _)| *t == core) {
                    Some((_, c)) => *c = <E::SR>::add(c.clone(), coeff),
                    None => coeffs.push((core, coeff)),
                }
            }

            if commutative {
                coeffs.sort_by(|a, b| cmp_structural(&a.0, &b.0));
            }

            let mut out = Vec::new();
            if coeffs.is_empty() || acc != <E::SR>::ZERO {
                out.push(constant(acc));
            }
            for (core, coeff) in coeffs {
                // The coefficient can degenerate to zero (cancellation, or
                // finite characteristic like 2x = 0 in Z/2), hence the checks.
                if coeff == <E::SR>::ZERO {
                    continue;
                }
                if coeff == <E::SR>::ONE {
                    out.push(core);
                } else {
                    let mut factors = vec![constant(coeff)];
                    match core.into_node() {
                        Node::Mul(inner) => factors.extend(inner),
                        n => factors.push(E::from_node(n)),
                    }
                    out.push(E::from_node(Node::Mul(factors)));
                }
            }

            *expr = match out.len() {
                // NOTE: everything cancelled; keep the interface total.
                0 => constant(<E::SR>::ZERO),
                1 => out.pop().unwrap(),
                _ => E::from_node(Node::Add(out)),
            };
        }
        Node::Mul(exprs) => {
            exprs.iter_mut().for_each(|e| normalize(e, commutative));

            let mut stack: Vec<E> = Vec::with_capacity(exprs.len());
            for item in flatten(std::mem::take(exprs), split_mul) {
                if is_const(&item, &<E::SR>::ONE) {
                    continue;
                }
                // Annihilation: a zero factor kills the whole product.
                if is_const(&item, &<E::SR>::ZERO) {
                    *expr = constant(<E::SR>::ZERO);
                    return;
                }
                match (item.into_node(), stack.pop()) {
                    (Node::Const(s), Some(t)) if matches!(t.node(), Node::Const(_)) => {
                        let Node::Const(t) = t.into_node() else {
                            unreachable!()
                        };
                        let c = <E::SR>::multiply(t, s);
                        // Re-check identities on the folded constant:
                        // 2 * 3 = 6 == 0 (mod 6) annihilates, and
                        // (-1) * (-1) = 1 drops out.
                        if c == <E::SR>::ZERO {
                            *expr = constant(<E::SR>::ZERO);
                            return;
                        }
                        if c != <E::SR>::ONE {
                            stack.push(constant(c));
                        }
                    }
                    (n, popped) => {
                        stack.extend(popped);
                        stack.push(E::from_node(n));
                    }
                }
            }

            // Distribute over Add factors: expand the cartesian product of
            // terms, keeping factor order (no commutativity assumed), then
            // re-format the resulting sum. Terms of a formatted Add are
            // never Add themselves, so this recursion terminates.
            if stack.iter().any(|f| matches!(f.node(), Node::Add(_))) {
                let mut products: Vec<Vec<E>> = vec![Vec::new()];
                for factor in stack {
                    match factor.into_node() {
                        Node::Add(terms) => {
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
                        n => {
                            let f = E::from_node(n);
                            for p in &mut products {
                                p.push(f.clone());
                            }
                        }
                    }
                }
                *expr = E::from_node(Node::Add(
                    products
                        .into_iter()
                        .map(|p| E::from_node(Node::Mul(p)))
                        .collect(),
                ));
                normalize(expr, commutative);
                return;
            }

            if commutative {
                // Commute all constants to the front and fold them into one.
                let (consts, factors): (Vec<_>, Vec<_>) = stack
                    .into_iter()
                    .partition(|f| matches!(f.node(), Node::Const(_)));
                let mut c_acc = <E::SR>::ONE;
                for c in consts {
                    let Node::Const(c) = c.into_node() else {
                        unreachable!()
                    };
                    c_acc = <E::SR>::multiply(c_acc, c);
                }
                if c_acc == <E::SR>::ZERO {
                    *expr = constant(<E::SR>::ZERO);
                    return;
                }

                // Collect repeated factors into powers: x * x^2 -> x^3.
                // ponytail: exponents summed with plain +; overflow is not a
                // realistic concern for expression trees.
                let mut pows: Vec<(E, usize)> = Vec::new();
                for factor in factors {
                    let (base, exp) = match factor.into_node() {
                        Node::Pow(base, exponent) => (*base, exponent.get()),
                        n => (E::from_node(n), 1),
                    };
                    match pows.iter_mut().find(|(b, _)| *b == base) {
                        Some((_, e)) => *e += exp,
                        None => pows.push((base, exp)),
                    }
                }
                pows.sort_by(|a, b| cmp_structural(&a.0, &b.0));

                let mut out = Vec::new();
                if c_acc != <E::SR>::ONE {
                    out.push(constant(c_acc));
                }
                for (base, exp) in pows {
                    out.push(if exp == 1 {
                        base
                    } else {
                        E::from_node(Node::Pow(Box::new(base), NonZeroUsize::new(exp).unwrap()))
                    });
                }
                stack = out;
            }

            *expr = match stack.len() {
                // NOTE: empty product simplifies to one to keep the interface total.
                0 => constant(<E::SR>::ONE),
                1 => stack.pop().unwrap(),
                _ => E::from_node(Node::Mul(stack)),
            };
        }
        Node::Pow(base, n) => {
            let base: &mut E = base;
            normalize(base, commutative);
            match take(base).into_node() {
                Node::Const(c) => {
                    let mut acc = c.clone();
                    for _ in 1..n.get() {
                        acc = <E::SR>::multiply(acc, c.clone());
                    }
                    *expr = constant(acc);
                }
                node if n.get() == 1 => *expr = E::from_node(node),
                Node::Pow(inner_base, inner) => match inner.checked_mul(n) {
                    // (b^m)^n = b^(m*n), by associativity of multiplication.
                    Some(mn) => *expr = E::from_node(Node::Pow(inner_base, mn)),
                    None => *base = E::from_node(Node::Pow(inner_base, inner)),
                },
                node => *base = E::from_node(node),
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

/// Canonicalizes [`RingExpr`]s using the ring laws (see [`normalize`]). The
/// canonical form contains no `Neg`: a negated term shows up as a constant
/// coefficient.
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
        normalize(expr, false);
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
        normalize(expr, true);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{Associative, BinaryOperator};

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
