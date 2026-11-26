//! Polynomials in one indeterminate over a field, `F[x]`.
//!
//! Unlike the free algebra [`Polynomial<R>`] on any number of symbols, `F[x]`
//! is a Euclidean domain: it has division with remainder and a gcd.

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ops::{Add, Mul, Neg, Rem, Sub};

use eqn_algebra::field::Field;
use eqn_algebra::ring::{RingElem, SemiRing};
use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

use crate::{Monomial, Polynomial};

/// An element of `F[x]` over a field `F`: its coefficients from the constant
/// term to the leading one, which is never zero, so equality is equality of
/// polynomials.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; RingElem<F>)]
#[derive_where(Default)]
pub struct Univariate<F: Field>(Vec<RingElem<F>>);

impl<F: Field> Univariate<F> {
    /// The polynomial with these coefficients, from the constant term up.
    pub fn new(coefficients: Vec<RingElem<F>>) -> Self {
        let mut polynomial = Self(coefficients);
        polynomial.trim();
        polynomial
    }

    pub fn zero() -> Self {
        Self(Vec::new())
    }

    pub fn one() -> Self {
        Self(vec![F::one()])
    }

    /// The indeterminate `x`.
    pub fn x() -> Self {
        Self(vec![F::zero(), F::one()])
    }

    pub fn coefficients(&self) -> &[RingElem<F>] {
        &self.0
    }

    pub fn into_coefficients(self) -> Vec<RingElem<F>> {
        self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    /// The degree, or `None` for the zero polynomial.
    pub fn degree(&self) -> Option<usize> {
        self.0.len().checked_sub(1)
    }

    /// The leading coefficient, or `None` for the zero polynomial.
    pub fn leading(&self) -> Option<&RingElem<F>> {
        self.0.last()
    }

    /// The image under the ring map `F[x] \to F` that sends `x` to `point`.
    pub fn eval(&self, point: RingElem<F>) -> RingElem<F> {
        self.0.iter().rev().fold(F::zero(), |value, coefficient| {
            F::add(F::multiply(value, point.clone()), coefficient.clone())
        })
    }

    /// The formal derivative, `\sum_i i c_i x^{i - 1}` of `\sum_i c_i x^i`.
    pub fn derive(self) -> Self {
        Self::new(
            self.0
                .into_iter()
                .enumerate()
                .skip(1)
                .map(|(i, coefficient)| F::multiply(F::from_usize(i), coefficient))
                .collect(),
        )
    }

    /// The monic greatest common divisor, with `gcd(0, 0) = 0`.
    pub fn gcd(self, other: Self) -> Self {
        let (mut a, mut b) = (self, other);
        while !b.is_zero() {
            let remainder = a % &b;
            a = b;
            b = remainder;
        }
        let Some(leading) = a.leading() else {
            return a;
        };
        let scale = F::invert(leading.clone());
        Self::new(
            a.0.into_iter()
                .map(|coefficient| F::multiply(coefficient, scale.clone()))
                .collect(),
        )
    }

    /// `self^exponent` reduced modulo `modulus`.
    pub fn pow_mod(mut self, mut exponent: u128, modulus: &Self) -> Self {
        let mut result = Self::one() % modulus;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = &result * &self % modulus;
            }
            exponent >>= 1;
            if exponent > 0 {
                self = &self * &self % modulus;
            }
        }
        result
    }

    /// Division with remainder: `(q, r)` with `self = q * divisor + r` and
    /// `deg r < deg divisor`. Panics when `divisor` is zero.
    pub fn div_rem(mut self, divisor: &Self) -> (Self, Self) {
        let leading = divisor.leading().expect("division by the zero polynomial");
        if self.0.len() < divisor.0.len() {
            return (Self::zero(), self);
        }

        let leading_inverse = F::invert(leading.clone());
        let mut quotient = vec![F::zero(); self.0.len() - divisor.0.len() + 1];
        while self.0.len() >= divisor.0.len() {
            let shift = self.0.len() - divisor.0.len();
            let coefficient =
                F::multiply(self.0[self.0.len() - 1].clone(), leading_inverse.clone());
            for (i, divisor_coefficient) in divisor.0.iter().enumerate() {
                let product = F::multiply(coefficient.clone(), divisor_coefficient.clone());
                self.0[i + shift] = F::add(self.0[i + shift].clone(), F::negate(product));
            }
            quotient[shift] = coefficient;
            self.trim();
        }
        (Self::new(quotient), self)
    }

    fn trim(&mut self) {
        let zero = F::zero();
        while self.0.last() == Some(&zero) {
            self.0.pop();
        }
    }
}

impl<F: Field> Add for Univariate<F> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self {
        self.0.resize(self.0.len().max(rhs.0.len()), F::zero());
        for (target, coefficient) in self.0.iter_mut().zip(rhs.0) {
            *target = F::add(target.clone(), coefficient);
        }
        Self::new(self.0)
    }
}

impl<F: Field> Sub for Univariate<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}

impl<F: Field> Neg for Univariate<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.into_iter().map(F::negate).collect())
    }
}

impl<F: Field> Mul for &Univariate<F> {
    type Output = Univariate<F>;

    fn mul(self, rhs: Self) -> Univariate<F> {
        if self.is_zero() || rhs.is_zero() {
            return Univariate::zero();
        }
        let mut product = vec![F::zero(); self.0.len() + rhs.0.len() - 1];
        for (i, a) in self.0.iter().enumerate() {
            for (j, b) in rhs.0.iter().enumerate() {
                product[i + j] = F::add(product[i + j].clone(), F::multiply(a.clone(), b.clone()));
            }
        }
        Univariate::new(product)
    }
}

impl<F: Field> Mul for Univariate<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        &self * &rhs
    }
}

impl<F: Field> Rem<&Univariate<F>> for Univariate<F> {
    type Output = Self;

    fn rem(self, modulus: &Self) -> Self {
        self.div_rem(modulus).1
    }
}

impl<F: Field> Set for Univariate<F> {}

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Univariate<F>,
    symbol = F::ADD_SYMBOL,
    apply = Add::add,
    identity = Univariate::zero(),
    inverse = Neg::neg,
    inverse_symbol = F::SUB_SYMBOL
)]
pub struct UnivariateAdd<F: Field>(PhantomData<F>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Univariate<F>,
    symbol = F::MUL_SYMBOL,
    apply = Mul::mul,
    identity = Univariate::one()
)]
pub struct UnivariateMul<F: Field>(PhantomData<F>);

/// The commutative ring `F[x]` over a field `F`.
///
/// A newtype rather than the `(UnivariateAdd, UnivariateMul)` tuple so this
/// crate can implement foreign traits on it.
pub struct UnivariateRing<F: Field>(PhantomData<F>);

impl<F: Field> SemiRing for UnivariateRing<F> {
    type Domain = Univariate<F>;
    type Addition = UnivariateAdd<F>;
    type Multiplication = UnivariateMul<F>;
}

/// The same polynomial, in the symbol `x`.
impl<F: Field> From<Univariate<F>> for Polynomial<F> {
    fn from(univariate: Univariate<F>) -> Self {
        let x = Symbol::new("x");
        univariate
            .0
            .into_iter()
            .enumerate()
            .map(|(exponent, coefficient)| {
                let monomial = NonZeroUsize::new(exponent).map_or(Monomial::ONE, |exponent| {
                    Monomial(BTreeMap::from([(x.clone(), exponent)]))
                });
                (monomial, coefficient)
            })
            .collect()
    }
}

/// A polynomial in at most one symbol, read as a polynomial in that symbol.
/// One in two or more symbols is refused with the second of them in the order
/// symbols sort.
impl<F: Field> TryFrom<Polynomial<F>> for Univariate<F> {
    type Error = Symbol<F::Domain>;

    fn try_from(polynomial: Polynomial<F>) -> Result<Self, Self::Error> {
        let symbols: BTreeSet<_> = polynomial
            .terms
            .keys()
            .flat_map(|monomial| monomial.0.keys())
            .collect();
        if let Some(second) = symbols.into_iter().nth(1) {
            return Err(second.clone());
        }

        let mut coefficients = Vec::new();
        for (monomial, coefficient) in polynomial.into_terms() {
            let exponent = monomial.0.into_values().next().map_or(0, NonZeroUsize::get);
            if coefficients.len() <= exponent {
                coefficients.resize(exponent + 1, F::zero());
            }
            coefficients[exponent] = coefficient;
        }
        Ok(Self::new(coefficients))
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{Fp, PrimeField};
    use eqn_algebra::ring::Ring;

    use super::*;

    type F = PrimeField<3>;
    type P = Univariate<F>;
    type Poly = UnivariateRing<F>;

    fn poly<const N: usize>(coefficients: [u64; N]) -> P {
        P::new(coefficients.map(Fp::new).to_vec())
    }

    fn below_degree(bound: u32) -> Vec<P> {
        (0..3u64.pow(bound))
            .map(|i| P::new((0..bound).map(|k| Fp::new(i / 3u64.pow(k))).collect()))
            .collect()
    }

    #[test]
    fn addition_and_multiplication_are_associative_and_commutative() {
        let samples = below_degree(3);
        for a in &samples {
            for b in &samples {
                assert_eq!(
                    Poly::add(a.clone(), b.clone()),
                    Poly::add(b.clone(), a.clone())
                );
                assert_eq!(
                    Poly::multiply(a.clone(), b.clone()),
                    Poly::multiply(b.clone(), a.clone())
                );
                for c in &samples {
                    assert_eq!(
                        Poly::add(Poly::add(a.clone(), b.clone()), c.clone()),
                        Poly::add(a.clone(), Poly::add(b.clone(), c.clone()))
                    );
                    assert_eq!(
                        Poly::multiply(Poly::multiply(a.clone(), b.clone()), c.clone()),
                        Poly::multiply(a.clone(), Poly::multiply(b.clone(), c.clone()))
                    );
                }
            }
        }
    }

    #[test]
    fn zero_and_one_are_identities_and_negation_is_the_additive_inverse() {
        for a in below_degree(3) {
            assert_eq!(Poly::add(a.clone(), Poly::zero()), a);
            assert_eq!(Poly::multiply(a.clone(), Poly::one()), a);
            assert_eq!(Poly::add(a.clone(), Poly::negate(a)), Poly::zero());
        }
    }

    #[test]
    fn multiplication_distributes_over_addition() {
        let samples = below_degree(3);
        for a in &samples {
            for b in &samples {
                for c in &samples {
                    assert_eq!(
                        Poly::multiply(a.clone(), Poly::add(b.clone(), c.clone())),
                        Poly::add(
                            Poly::multiply(a.clone(), b.clone()),
                            Poly::multiply(a.clone(), c.clone())
                        )
                    );
                }
            }
        }
    }

    #[test]
    fn division_recovers_the_dividend_with_a_remainder_of_lower_degree() {
        let divisors: Vec<_> = below_degree(3)
            .into_iter()
            .filter(|b| !b.is_zero())
            .collect();
        for a in below_degree(4) {
            for b in &divisors {
                let (quotient, remainder) = a.clone().div_rem(b);
                assert!(remainder.degree() < b.degree());
                assert_eq!(Poly::add(Poly::multiply(quotient, b.clone()), remainder), a);
            }
        }
    }

    #[test]
    fn gcd_is_the_shared_factor_made_monic() {
        let shared = poly([1, 1]);
        let a = &shared * &poly([2, 1]);
        let b = &shared * &poly([0, 2]);

        assert_eq!(a.clone().gcd(b), shared);
        assert_eq!(a.clone().gcd(P::zero()), a.clone().gcd(a));
        assert_eq!(P::zero().gcd(P::zero()), P::zero());
    }

    #[test]
    fn evaluation_is_a_ring_map_that_finds_roots() {
        let points = [0, 1, 2].map(Fp::new);
        let samples = below_degree(3);
        for a in &samples {
            for b in &samples {
                for point in points {
                    assert_eq!(
                        (a.clone() + b.clone()).eval(point),
                        a.eval(point) + b.eval(point)
                    );
                    assert_eq!((a * b).eval(point), a.eval(point) * b.eval(point));
                }
            }
        }

        let x_squared_minus_one = poly([2, 0, 1]);
        assert_eq!(x_squared_minus_one.eval(Fp::new(1)), Fp::zero());
        assert_eq!(x_squared_minus_one.eval(Fp::new(2)), Fp::zero());
        assert_ne!(x_squared_minus_one.eval(Fp::new(0)), Fp::zero());
    }

    #[test]
    fn formal_derivative_satisfies_leibniz_and_vanishes_on_x_cubed() {
        let samples = below_degree(3);
        for a in &samples {
            for b in &samples {
                assert_eq!(
                    (a * b).derive(),
                    &a.clone().derive() * b + a * &b.clone().derive()
                );
            }
        }
        assert_eq!(poly([0, 0, 0, 1]).derive(), P::zero());
    }

    #[test]
    fn conversion_to_a_polynomial_in_x_and_back_is_the_identity() {
        assert_eq!(
            Polynomial::from(poly([1, 2, 1])),
            "x^2 + 2 x + 1".parse::<Polynomial<F>>().unwrap()
        );
        for a in below_degree(3) {
            assert_eq!(P::try_from(Polynomial::from(a.clone())), Ok(a));
        }
        let in_t: Polynomial<F> = "t^2 + 1".parse().unwrap();
        assert_eq!(P::try_from(in_t), Ok(poly([1, 0, 1])));
    }

    #[test]
    fn a_polynomial_in_two_symbols_is_refused_with_the_second_symbol() {
        let refused = |src: &str| P::try_from(src.parse::<Polynomial<F>>().unwrap());

        assert_eq!(refused("x y + 1"), Err(Symbol::new("y")));
        assert_eq!(refused("z + y + x"), Err(Symbol::new("y")));
        assert_eq!(refused("y^2 + z"), Err(Symbol::new("z")));
    }
}
