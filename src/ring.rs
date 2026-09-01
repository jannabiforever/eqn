use std::num::NonZeroUsize;

use crate::domain::Domain;
use crate::op::{
    AssociativeOperator, BinaryOperator, CommutativeOperator, IdentityOperator, InverseOperator,
};
use crate::symbol::Symbol;

/// A semi-ring: addition forms a commutative monoid, multiplication forms a
/// monoid. Distributivity and annihilation (`0 * a = 0`) relate the two
/// operators and cannot be encoded as bounds; they are part of the contract.
pub trait SemiRing {
    type Domain: Domain;

    /// The addition operator for this semi-ring.
    ///
    /// Should be associative, commutative, and have an identity element.
    type Addition: AssociativeOperator<Self::Domain>
        + CommutativeOperator<Self::Domain>
        + IdentityOperator<Self::Domain>;

    /// The multiplication operator for this semi-ring.
    ///
    /// Should be associative and have an identity element.
    type Multiplication: AssociativeOperator<Self::Domain> + IdentityOperator<Self::Domain>;
}

/// An expression tree over a semi-ring: constants, named symbols, n-ary sums
/// and products, and powers (repeated multiplication, exponent >= 1).
pub enum SemiRingExpr<SR: SemiRing> {
    Const(<SR::Domain as Domain>::Element),
    Symbol(Symbol<SR::Domain>),
    Add(Vec<SemiRingExpr<SR>>),
    Mul(Vec<SemiRingExpr<SR>>),
    Pow {
        base: Box<SemiRingExpr<SR>>,
        exponent: NonZeroUsize,
    },
}

impl<D: Domain, SR: SemiRing<Domain = D>> From<Symbol<D>> for SemiRingExpr<SR> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

impl<SR: SemiRing> Clone for SemiRingExpr<SR> {
    fn clone(&self) -> Self {
        match self {
            Self::Const(c) => Self::Const(c.clone()),
            Self::Symbol(s) => Self::Symbol(s.clone()),
            Self::Add(v) => Self::Add(v.clone()),
            Self::Mul(v) => Self::Mul(v.clone()),
            Self::Pow { base, exponent } => Self::Pow {
                base: base.clone(),
                exponent: *exponent,
            },
        }
    }
}

/// Structural equality; no algebraic normalization (simplify first for that).
impl<SR: SemiRing> PartialEq for SemiRingExpr<SR> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(s), Self::Const(o)) => s == o,
            (Self::Symbol(s), Self::Symbol(o)) => s == o,
            (Self::Add(s), Self::Add(o)) => s == o,
            (Self::Mul(s), Self::Mul(o)) => s == o,
            (
                Self::Pow {
                    base: sb,
                    exponent: se,
                },
                Self::Pow {
                    base: ob,
                    exponent: oe,
                },
            ) => se == oe && sb == ob,
            _ => false,
        }
    }
}

impl<SR: SemiRing> Eq for SemiRingExpr<SR> {}

impl<SR: SemiRing> PartialOrd for SemiRingExpr<SR>
where
    <SR::Domain as Domain>::Element: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Structural total order (variant rank, then contents); exists so
/// expressions can key a `BTreeMap` and sort into canonical forms.
impl<SR: SemiRing> Ord for SemiRingExpr<SR>
where
    <SR::Domain as Domain>::Element: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        const fn rank<SR: SemiRing>(e: &SemiRingExpr<SR>) -> u8 {
            match e {
                SemiRingExpr::Const(_) => 0,
                SemiRingExpr::Symbol(_) => 1,
                SemiRingExpr::Add(_) => 2,
                SemiRingExpr::Mul(_) => 3,
                SemiRingExpr::Pow { .. } => 4,
            }
        }

        match (self, other) {
            (Self::Const(s), Self::Const(o)) => Ord::cmp(s, o),
            (Self::Symbol(s), Self::Symbol(o)) => s.cmp(o),
            (Self::Add(s), Self::Add(o)) => s.cmp(o),
            (Self::Mul(s), Self::Mul(o)) => s.cmp(o),
            (
                Self::Pow {
                    base: sb,
                    exponent: se,
                },
                Self::Pow {
                    base: ob,
                    exponent: oe,
                },
            ) => sb.cmp(ob).then(se.cmp(oe)),
            (s, o) => rank(s).cmp(&rank(o)),
        }
    }
}

impl<SR: SemiRing> SemiRingExpr<SR> {
    /// Wraps a domain element as a constant expression.
    #[inline]
    pub const fn constant(value: <SR::Domain as Domain>::Element) -> Self {
        Self::Const(value)
    }

    /// The additive identity.
    #[inline]
    const fn zero() -> <SR::Domain as Domain>::Element {
        <SR::Addition as IdentityOperator<SR::Domain>>::IDENTITY
    }

    /// The multiplicative identity.
    #[inline]
    const fn one() -> <SR::Domain as Domain>::Element {
        <SR::Multiplication as IdentityOperator<SR::Domain>>::IDENTITY
    }

    #[inline]
    fn add(
        a: <SR::Domain as Domain>::Element,
        b: <SR::Domain as Domain>::Element,
    ) -> <SR::Domain as Domain>::Element {
        <SR::Addition as BinaryOperator<SR::Domain>>::apply(a, b)
    }

    #[inline]
    fn mul(
        a: <SR::Domain as Domain>::Element,
        b: <SR::Domain as Domain>::Element,
    ) -> <SR::Domain as Domain>::Element {
        <SR::Multiplication as BinaryOperator<SR::Domain>>::apply(a, b)
    }

    /// The count `n` as a domain element: `1 + 1 + ... + 1` (n times, n >= 1).
    // ponytail: O(n) sum of ones; fine for expression multiplicities.
    fn count_as_element(n: usize) -> <SR::Domain as Domain>::Element {
        let mut acc = Self::one();
        for _ in 1..n {
            acc = Self::add(acc, Self::one());
        }
        acc
    }
}
impl<SR: SemiRing> SemiRingExpr<SR>
where
    <SR::Domain as Domain>::Element: Ord,
{
    /// Simplifies using the semi-ring laws, mirroring [`crate::monoid`]:
    /// - `Add` (commutative monoid): flattens, folds *all* constants into one
    ///   leading constant, drops zeros, and collects structurally equal terms
    ///   into left coefficients (`x + x -> 2 * x`); terms sort canonically.
    /// - `Mul` (monoid): flattens, folds *adjacent* constants, drops ones,
    ///   annihilates the whole product on a zero factor, and distributes over
    ///   `Add` factors.
    /// - `Pow`: folds constant bases, collapses exponent 1 and nested powers.
    ///   Bases are simplified but not expanded (`(x + y)^2` stays a power).
    pub fn simplify(self) -> Self {
        match self {
            Self::Const(_) | Self::Symbol(_) => self,
            Self::Add(exprs) => {
                let mut acc = Self::zero();
                let mut counts = std::collections::BTreeMap::new();

                for expr in exprs {
                    let items = match expr.simplify() {
                        Self::Add(inner) => inner,
                        e => vec![e],
                    };
                    for item in items {
                        match item {
                            Self::Const(c) => acc = Self::add(acc, c),
                            item => *counts.entry(item).or_insert(0usize) += 1,
                        }
                    }
                }

                let mut out = Vec::new();
                if counts.is_empty() || acc != Self::zero() {
                    out.push(Self::Const(acc));
                }
                for (term, n) in counts {
                    // n * x as a left coefficient: (1 + ... + 1) * x, by
                    // distributivity. The coefficient can degenerate in finite
                    // characteristic (e.g. 2x = 0 in Z/2), hence the checks.
                    let coeff = Self::count_as_element(n);
                    if coeff == Self::zero() {
                        continue;
                    }
                    if coeff == Self::one() {
                        out.push(term);
                    } else {
                        out.push(Self::Mul(vec![Self::Const(coeff), term]));
                    }
                }

                if out.len() == 1 {
                    out.into_iter().next().unwrap()
                } else {
                    Self::Add(out)
                }
            }
            Self::Mul(exprs) => {
                let mut stack: Vec<Self> = Vec::new();

                for expr in exprs {
                    let items = match expr.simplify() {
                        Self::Mul(inner) => inner,
                        e => vec![e],
                    };
                    for item in items {
                        if item == Self::Const(Self::one()) {
                            continue;
                        }
                        // Annihilation: a zero factor kills the whole product.
                        // ponytail: only literal zero factors are caught; a fold
                        // *producing* zero (zero divisors) is not re-checked.
                        if item == Self::Const(Self::zero()) {
                            return Self::Const(Self::zero());
                        }
                        match (item, stack.pop()) {
                            (Self::Const(s), Some(Self::Const(t))) => {
                                stack.push(Self::Const(Self::mul(t, s)))
                            }
                            (item, popped) => {
                                if let Some(p) = popped {
                                    stack.push(p);
                                }
                                stack.push(item);
                            }
                        }
                    }
                }

                // Distribute over Add factors: expand the cartesian product of
                // terms, keeping factor order (no commutativity assumed), then
                // re-simplify the resulting sum. Terms of a simplified Add are
                // never Add themselves, so this recursion terminates.
                if stack.iter().any(|f| matches!(f, Self::Add(_))) {
                    let mut products: Vec<Vec<Self>> = vec![Vec::new()];
                    for factor in stack {
                        match factor {
                            Self::Add(terms) => {
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
                    return Self::Add(products.into_iter().map(Self::Mul).collect()).simplify();
                }

                match stack.len() {
                    // NOTE: empty product simplifies to one to keep the interface total.
                    0 => Self::Const(Self::one()),
                    1 => stack.pop().unwrap(),
                    _ => Self::Mul(stack),
                }
            }
            Self::Pow { base, exponent } => match (base.simplify(), exponent) {
                (Self::Const(c), n) => {
                    let mut acc = c.clone();
                    for _ in 1..n.get() {
                        acc = Self::mul(acc, c.clone());
                    }
                    Self::Const(acc)
                }
                (base, n) if n.get() == 1 => base,
                (
                    Self::Pow {
                        base,
                        exponent: inner,
                    },
                    n,
                ) => match inner.checked_mul(n) {
                    // (b^m)^n = b^(m*n), by associativity of multiplication.
                    Some(mn) => Self::Pow { base, exponent: mn },
                    None => Self::Pow {
                        base: Box::new(Self::Pow {
                            base,
                            exponent: inner,
                        }),
                        exponent: n,
                    },
                },
                (base, n) => Self::Pow {
                    base: Box::new(base),
                    exponent: n,
                },
            },
        }
    }
}

/// A ring: a semi-ring whose addition also has inverses.
pub trait Ring {
    type Domain: Domain;

    /// The addition operator for this ring.
    ///
    /// Should be associative, commutative, and have an identity element, and an
    /// inverse operator.
    type Addition: AssociativeOperator<Self::Domain>
        + CommutativeOperator<Self::Domain>
        + IdentityOperator<Self::Domain>
        + InverseOperator<Self::Domain>;

    /// The multiplication operator for this ring.
    ///
    /// Should be associative and have an identity element.
    type Multiplication: AssociativeOperator<Self::Domain> + IdentityOperator<Self::Domain>;
}

/// Any semi-ring with invertible addition is a ring for free.
impl<SR: SemiRing> Ring for SR
where
    SR::Addition: InverseOperator<SR::Domain>,
{
    type Domain = SR::Domain;
    type Addition = SR::Addition;
    type Multiplication = SR::Multiplication;
}

/// An expression tree over a ring; `Neg` is the additive inverse, which is
/// what distinguishes it from [`SemiRingExpr`].
// ponytail: simplify for RingExpr is not written yet; it mirrors the
// SemiRingExpr one plus Neg rules (--x = x, Neg(Const(c)) = Const(inverse(c)),
// Neg pushed through Add/Mul). Implement when a Ring is actually used.
pub enum RingExpr<R: Ring> {
    Const(<R::Domain as Domain>::Element),
    Symbol(Symbol<R::Domain>),
    Neg(Box<RingExpr<R>>),
    Add(Vec<RingExpr<R>>),
    Mul(Vec<RingExpr<R>>),
    Pow {
        base: Box<RingExpr<R>>,
        exponent: NonZeroUsize,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestDomain;

    impl Domain for TestDomain {
        type Element = i64;
    }

    struct TestAdd;

    impl BinaryOperator<TestDomain> for TestAdd {
        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }

    impl AssociativeOperator<TestDomain> for TestAdd {}
    impl CommutativeOperator<TestDomain> for TestAdd {}
    impl IdentityOperator<TestDomain> for TestAdd {
        const IDENTITY: i64 = 0;
    }

    struct TestMul;

    impl BinaryOperator<TestDomain> for TestMul {
        fn apply(a: i64, b: i64) -> i64 {
            a * b
        }
    }

    impl AssociativeOperator<TestDomain> for TestMul {}
    impl IdentityOperator<TestDomain> for TestMul {
        const IDENTITY: i64 = 1;
    }

    struct TestSemiRing;

    impl SemiRing for TestSemiRing {
        type Domain = TestDomain;
        type Addition = TestAdd;
        type Multiplication = TestMul;
    }

    type Expr = SemiRingExpr<TestSemiRing>;

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

        assert!(expr.simplify() == Expr::Add(vec![Expr::Const(15), Expr::Symbol(x)]));
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
        assert!(zero.simplify() == Expr::Const(0));

        // 1 * x ==> x
        let ident = Expr::Mul(vec![Expr::Const(1), Expr::Symbol(x.clone())]);
        assert!(ident.simplify() == Expr::Symbol(x));
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
            expr.simplify()
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
            expr.simplify()
                == Expr::Add(vec![
                    Expr::Mul(vec![Expr::Const(3), Expr::Symbol(x)]),
                    Expr::Symbol(y),
                ])
        );
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
            nested.simplify()
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
        assert!(first.simplify() == Expr::Symbol(x));
    }
}
