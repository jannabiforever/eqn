// mgca: `FiniteExtension<M>` hold `M::DIM` coordinates.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ops::{Add, Mul, Neg};

use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::{CommutativeRing, DifferentialRing, RingElem, RingExpr, SemiRing};
use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

mod finite_field;

pub use finite_field::{
    CompatibleFiniteField, CompatibleFiniteFieldElement, CompatibleFiniteFieldEmbedding,
    DefiningPolynomial, FiniteField, FiniteFieldAdd, FiniteFieldElement, FiniteFieldElements,
    FiniteFieldMul, FirstCompatible, FirstIrreducible, FirstPrimitive, Fq, FqElement,
    IrreduciblePolynomial, PrimitiveFiniteField, PrimitiveFiniteFieldElement, UnivariatePolynomial,
};

// ================================================================================
// Monomial
// ================================================================================

/// A product of symbols of `D` with positive exponents; the empty product is
/// `1`.
#[derive_where::derive_where(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Monomial<D: Set>(BTreeMap<Symbol<D>, NonZeroUsize>);

impl<D: Set> Monomial<D> {
    pub const ONE: Self = Self(BTreeMap::new());

    pub fn is_one(&self) -> bool {
        self.0.is_empty()
    }

    /// `\partial_s` as a monomial: the exponent of `s` and the monomial with
    /// that exponent lowered by one, or `None` when `s` does not occur.
    fn derive(mut self, s: &Symbol<D>) -> Option<(usize, Self)> {
        let exponent = self.0.remove(s)?.get();
        if let Some(reduced) = NonZeroUsize::new(exponent - 1) {
            self.0.insert(s.clone(), reduced);
        }
        Some((exponent, self))
    }
}

impl<D: Set> From<Symbol<D>> for Monomial<D> {
    fn from(s: Symbol<D>) -> Self {
        Self(BTreeMap::from([(s, NonZeroUsize::MIN)]))
    }
}

impl<D: Set> Mul for Monomial<D> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self {
        for (s, e) in rhs.0 {
            self.0
                .entry(s)
                .and_modify(|total| *total = total.checked_add(e.get()).expect("exponent overflow"))
                .or_insert(e);
        }
        self
    }
}

// ================================================================================
// Polynomial
// ================================================================================

/// An element of `R[x_1, ..., x_n]` on the symbols of `R`'s domain: a finite
/// sum of monomials with nonzero coefficients, so equality is equality of
/// polynomials.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; RingElem<R>)]
pub struct Polynomial<R: CommutativeRing> {
    constant: RingElem<R>,
    terms: BTreeMap<Monomial<R::Domain>, RingElem<R>>,
}

impl<R: CommutativeRing> Polynomial<R> {
    pub const ZERO: Self = Self {
        constant: R::ZERO,
        terms: BTreeMap::new(),
    };

    pub const ONE: Self = Self {
        constant: R::ONE,
        terms: BTreeMap::new(),
    };

    pub fn constant(value: RingElem<R>) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }

    // ponytail: repeated multiplication, square-and-multiply if exponents grow
    pub fn pow(self, exponent: NonZeroUsize) -> Self {
        (1..exponent.get()).fold(self.clone(), |acc, _| acc * self.clone())
    }

    fn into_terms(self) -> impl Iterator<Item = (Monomial<R::Domain>, RingElem<R>)> {
        std::iter::once((Monomial::ONE, self.constant)).chain(self.terms)
    }
}

/// Collects like terms and drops zero coefficients.
impl<R: CommutativeRing> FromIterator<(Monomial<R::Domain>, RingElem<R>)> for Polynomial<R> {
    fn from_iter<I: IntoIterator<Item = (Monomial<R::Domain>, RingElem<R>)>>(iter: I) -> Self {
        let mut polynomial = Self::ZERO;
        for (monomial, coefficient) in iter {
            if monomial.is_one() {
                polynomial.constant = R::add(polynomial.constant, coefficient);
                continue;
            }
            match polynomial.terms.entry(monomial) {
                Entry::Vacant(slot) => {
                    slot.insert(coefficient);
                }
                Entry::Occupied(mut slot) => {
                    *slot.get_mut() = R::add(slot.get().clone(), coefficient);
                }
            }
        }
        polynomial
            .terms
            .retain(|_, coefficient| *coefficient != R::ZERO);
        polynomial
    }
}

impl<R: CommutativeRing> From<Symbol<R::Domain>> for Polynomial<R> {
    fn from(s: Symbol<R::Domain>) -> Self {
        [(Monomial::from(s), R::ONE)].into_iter().collect()
    }
}

/// Evaluation of the free ring expression: the unique ring map sending each
/// symbol to itself.
impl<R: CommutativeRing> From<RingExpr<R>> for Polynomial<R> {
    fn from(expr: RingExpr<R>) -> Self {
        match expr {
            RingExpr::Const(c) => Self::constant(c),
            RingExpr::Symbol(s) => Self::from(s),
            RingExpr::Neg(inner) => -Self::from(*inner),
            RingExpr::Add(v) => v.into_iter().map(Self::from).fold(Self::ZERO, Add::add),
            RingExpr::Mul(v) => v.into_iter().map(Self::from).fold(Self::ONE, Mul::mul),
            RingExpr::Pow { base, exponent } => Self::from(*base).pow(exponent),
        }
    }
}

impl<R: CommutativeRing> Add for Polynomial<R> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.into_terms().chain(rhs.into_terms()).collect()
    }
}

impl<R: CommutativeRing> Neg for Polynomial<R> {
    type Output = Self;

    fn neg(self) -> Self {
        self.into_terms()
            .map(|(monomial, coefficient)| (monomial, R::negate(coefficient)))
            .collect()
    }
}

impl<R: CommutativeRing> Mul for Polynomial<R> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let rhs: Vec<_> = rhs.into_terms().collect();
        self.into_terms()
            .flat_map(|(m, a)| {
                rhs.iter()
                    .map(move |(n, b)| (m.clone() * n.clone(), R::multiply(a.clone(), b.clone())))
            })
            .collect()
    }
}

// ================================================================================
// PolynomialRing
// ================================================================================

/// The set of polynomials over `R`.
#[derive(Set)]
#[set(element = Polynomial<R>)]
pub struct Polynomials<R: CommutativeRing>(PhantomData<R>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    apply = Add::add,
    identity = Polynomial::ZERO,
    inverse = Neg::neg
)]
pub struct PolyAdd<R: CommutativeRing>(PhantomData<R>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Polynomials<R>, apply = Mul::mul, identity = Polynomial::ONE)]
pub struct PolyMul<R: CommutativeRing>(PhantomData<R>);

/// The commutative ring of polynomials over `R`.
///
/// A newtype rather than the `(Polynomials, PolyAdd, PolyMul)` tuple so this
/// crate can implement foreign traits like [`DifferentialRing`] on it.
pub struct PolynomialRing<R: CommutativeRing>(PhantomData<R>);

impl<R: CommutativeRing> SemiRing for PolynomialRing<R> {
    type Domain = Polynomials<R>;
    type Addition = PolyAdd<R>;
    type Multiplication = PolyMul<R>;
}

impl<R: CommutativeRing> Module for PolynomialRing<R> {
    type Scalars = R;
    type Domain = Polynomials<R>;
    type Addition = PolyAdd<R>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        Polynomial::constant(scalar) * value
    }
}

/// The free commutative `R`-algebra on its symbols, with `\partial/\partial s`.
impl<R: CommutativeRing> DifferentialRing for PolynomialRing<R> {
    type Index = Symbol<R::Domain>;

    fn derive(a: RingElem<Self>, s: &Self::Index) -> RingElem<Self> {
        a.terms
            .into_iter()
            .filter_map(|(monomial, coefficient)| {
                let (exponent, reduced) = monomial.derive(s)?;
                Some((reduced, R::multiply(R::from_usize(exponent), coefficient)))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::algebra::Algebra;
    use eqn_algebra::operator_impl::{ZAdd, ZMul};
    use eqn_core::set::Z;

    use super::*;

    type R = (Z, ZAdd, ZMul);
    type P = Polynomial<R>;
    type Poly = PolynomialRing<R>;

    fn c(i: i64) -> P {
        P::constant(i)
    }

    fn xs() -> Symbol<Z> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Z> {
        Symbol::new("y")
    }

    fn x() -> P {
        P::from(xs())
    }

    fn y() -> P {
        P::from(ys())
    }

    fn pow(base: P, exponent: usize) -> P {
        base.pow(NonZeroUsize::new(exponent).unwrap())
    }

    #[test]
    fn equality_is_equality_of_polynomials() {
        assert_eq!(x() + y(), y() + x());
        assert_eq!(x() + -x(), P::ZERO);
        assert_eq!((x() + c(1)) * (x() + c(-1)), pow(x(), 2) + c(-1));
        assert_eq!(c(0) * x(), P::ZERO);
        assert_ne!(x(), y());
    }

    #[test]
    fn ring_laws_hold_on_representatives() {
        let samples = [c(0), c(3), x(), y() + c(-1), x() * y() + pow(x(), 2)];
        for a in &samples {
            for b in &samples {
                assert_eq!(a.clone() * b.clone(), b.clone() * a.clone());
                for d in &samples {
                    assert_eq!(
                        (a.clone() * b.clone()) * d.clone(),
                        a.clone() * (b.clone() * d.clone())
                    );
                    assert_eq!(
                        a.clone() * (b.clone() + d.clone()),
                        a.clone() * b.clone() + a.clone() * d.clone()
                    );
                }
            }
        }
    }

    #[test]
    fn polynomial_ring_is_commutative() {
        fn assert_commutative_ring<R: CommutativeRing>() {}
        assert_commutative_ring::<Poly>();
    }

    #[test]
    fn polynomial_ring_is_an_algebra_over_its_coefficients() {
        fn assert_algebra<A: Algebra>() {}

        assert_algebra::<Poly>();
        assert_eq!(Poly::scale(3, x()), c(3) * x());
        assert_eq!(Poly::from_scalar(4), c(4));
    }

    #[test]
    fn coefficient_action_satisfies_the_algebra_laws() {
        let p = x() + c(2);
        let q = y() + c(-3);

        assert_eq!(Poly::scale(0, p.clone()), P::ZERO);
        assert_eq!(Poly::scale(1, p.clone()), p);
        assert_eq!(
            Poly::scale(2 + 3, p.clone()),
            Poly::scale(2, p.clone()) + Poly::scale(3, p.clone())
        );
        assert_eq!(
            Poly::scale(2 * 3, p.clone()),
            Poly::scale(2, Poly::scale(3, p.clone()))
        );
        assert_eq!(
            Poly::scale(2, p.clone() + q.clone()),
            Poly::scale(2, p.clone()) + Poly::scale(2, q.clone())
        );
        assert_eq!(
            Poly::scale(2, p.clone() * q.clone()),
            Poly::scale(2, p.clone()) * q.clone()
        );
        assert_eq!(Poly::scale(2, p.clone() * q.clone()), p * Poly::scale(2, q));
    }

    #[test]
    fn ring_expressions_evaluate_to_polynomials() {
        let expr = RingExpr::<R>::Pow {
            base: Box::new(RingExpr::Add(vec![
                RingExpr::Symbol(xs()),
                RingExpr::Const(1),
            ])),
            exponent: NonZeroUsize::new(2).unwrap(),
        };
        assert_eq!(P::from(expr), pow(x(), 2) + c(2) * x() + c(1));
    }

    #[test]
    fn derive_of_a_power() {
        assert_eq!(Poly::derive(pow(x(), 2), &xs()), c(2) * x());
    }

    #[test]
    fn derive_of_a_product() {
        assert_eq!(Poly::derive(x() * y(), &xs()), y());
    }

    #[test]
    fn derive_of_a_sum_only_sees_its_own_variable() {
        assert_eq!(Poly::derive(pow(x(), 3) + y(), &ys()), c(1));
    }

    #[test]
    fn derive_of_a_constant_is_zero() {
        assert_eq!(Poly::derive(c(5), &xs()), P::ZERO);
    }

    #[test]
    fn derivations_commute_and_satisfy_leibniz() {
        let p = pow(x(), 2) * y() + x();
        let q = x() * pow(y(), 3) + c(-2);
        assert_eq!(
            Poly::derive(Poly::derive(p.clone(), &xs()), &ys()),
            Poly::derive(Poly::derive(p.clone(), &ys()), &xs())
        );
        assert_eq!(
            Poly::derive(p.clone() * q.clone(), &xs()),
            Poly::derive(p.clone(), &xs()) * q.clone() + p * Poly::derive(q, &xs())
        );
    }
}
