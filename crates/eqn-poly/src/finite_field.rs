use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::{Mutex, OnceLock};

use eqn_algebra::algebra::Algebra;
use eqn_algebra::field::{FieldExtension, FiniteExtension, Fp, PrimeField};
use eqn_algebra::group::quotient::QuotientOp;
use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::SemiRing;
use eqn_algebra::ring::ideal::{Ideal, MaximalIdeal};
use eqn_algebra::ring::quotient::QuotientMul;
use eqn_core::map::Map;
use eqn_core::quotient::{Congruence, NormalForm, Quotient};

use crate::univariate::{Univariate, UnivariateAdd, UnivariateMul, UnivariateRing};

/// A monic degree-`N` polynomial over `F_P`, stored from constant to leading
/// coefficient.
pub trait DefiningPolynomial<const P: u64, const N: usize> {
    fn coefficients() -> Vec<Fp<P>>;
}

/// A defining polynomial known to be irreducible over `F_P`.
pub trait IrreduciblePolynomial<const P: u64, const N: usize>: DefiningPolynomial<P, N> {}

/// Selects the first irreducible polynomial in base-`P` coefficient order.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstIrreducible;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstIrreducible {
    fn coefficients() -> Vec<Fp<P>> {
        PolynomialSelection::Irreducible
            .generate(N)
            .into_coefficients()
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstIrreducible {}

/// Selects the first primitive polynomial in base-`P` coefficient order.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstPrimitive;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstPrimitive {
    fn coefficients() -> Vec<Fp<P>> {
        PolynomialSelection::Primitive
            .generate(N)
            .into_coefficients()
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstPrimitive {}

/// Selects a deterministic primitive polynomial compatible across divisor
/// degrees, following the pseudo-Conway construction.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstCompatible;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstCompatible {
    fn coefficients() -> Vec<Fp<P>> {
        PolynomialSelection::Compatible
            .generate(N)
            .into_coefficients()
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstCompatible {}

/// The principal ideal `(M)` of `F_p[x]`, presented by the normal form that
/// takes the remainder modulo `M`.
pub struct Modulus<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M: DefiningPolynomial<P, N>> Modulus<P, N, M> {
    /// The defining polynomial `M`. Panics unless it is monic of degree `N`.
    pub fn polynomial() -> Univariate<PrimeField<P>> {
        const { Fp::<P>::assert_valid() };
        let coefficients = M::coefficients();
        assert_eq!(
            coefficients.len(),
            N + 1,
            "defining polynomial must have degree N"
        );
        assert_eq!(
            coefficients.last(),
            Some(&Fp::one()),
            "defining polynomial must be monic"
        );
        Univariate::new(coefficients)
    }
}

impl<const P: u64, const N: usize, M: DefiningPolynomial<P, N>>
    NormalForm<Univariate<PrimeField<P>>> for Modulus<P, N, M>
{
    fn reduce(polynomial: Univariate<PrimeField<P>>) -> Univariate<PrimeField<P>> {
        const { assert!(N > 0, "a field extension must have positive degree") };
        if polynomial.coefficients().len() <= N {
            return polynomial;
        }
        polynomial % &Self::polynomial()
    }
}

impl<const P: u64, const N: usize, M: DefiningPolynomial<P, N>>
    Congruence<UnivariateAdd<PrimeField<P>>> for Modulus<P, N, M>
{
}

impl<const P: u64, const N: usize, M: DefiningPolynomial<P, N>>
    Congruence<UnivariateMul<PrimeField<P>>> for Modulus<P, N, M>
{
}

impl<const P: u64, const N: usize, M: DefiningPolynomial<P, N>> Ideal for Modulus<P, N, M> {
    type Ring = UnivariateRing<PrimeField<P>>;
}

/// `(M)` is maximal because `M` is irreducible.
impl<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N>> MaximalIdeal
    for Modulus<P, N, M>
{
    fn inverse(element: Univariate<PrimeField<P>>) -> Univariate<PrimeField<P>> {
        let remainder = Self::reduce(element);
        assert!(!remainder.is_zero(), "zero has no multiplicative inverse");

        let mut old_r = Self::polynomial();
        let mut r = remainder;
        let mut old_t = Univariate::zero();
        let mut t = Univariate::one();

        while !r.is_zero() {
            let (quotient, next_r) = old_r.div_rem(&r);
            let next_t = old_t - &quotient * &t;
            old_r = r;
            r = next_r;
            old_t = t;
            t = next_t;
        }

        assert_eq!(
            old_r.coefficients().len(),
            1,
            "defining polynomial must be irreducible"
        );
        let scale = old_r.coefficients()[0].inverse();
        Univariate::new(
            old_t
                .into_coefficients()
                .into_iter()
                .map(|coefficient| coefficient * scale)
                .collect(),
        )
    }
}

/// The finite field `F_(p^n)` as a set, the quotient `F_p[x] / (M)`.
/// [`FiniteField<P, N, M>`] is its field structure.
pub type Fq<const P: u64, const N: usize, M = FirstIrreducible> =
    Quotient<Univariate<PrimeField<P>>, Modulus<P, N, M>>;

/// The quotient field `F_P[x] / (M)` of degree `N`.
pub struct FiniteField<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    pub fn modulus() -> Univariate<PrimeField<P>> {
        Modulus::<P, N, M>::polynomial()
    }

    pub fn modulus_is_irreducible() -> bool {
        Self::modulus().is_irreducible()
    }

    pub fn from_values(values: [u64; N]) -> Fq<P, N, M> {
        Quotient::new(Univariate::new(values.map(Fp::new).to_vec()))
    }

    pub fn generator() -> Fq<P, N, M> {
        Quotient::new(Univariate::x())
    }

    pub fn pow(mut base: Fq<P, N, M>, mut exponent: u128) -> Fq<P, N, M> {
        let mut result = Self::one();
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = Self::multiply(result, base.clone());
            }
            exponent >>= 1;
            if exponent > 0 {
                base = Self::multiply(base.clone(), base);
            }
        }
        result
    }

    pub fn evaluate_base_polynomial(
        polynomial: &Univariate<PrimeField<P>>,
        value: Fq<P, N, M>,
    ) -> Fq<P, N, M> {
        polynomial
            .coefficients()
            .iter()
            .rev()
            .fold(Self::zero(), |result, &coefficient| {
                Self::add(
                    Self::multiply(result, value.clone()),
                    Self::from_scalar(coefficient),
                )
            })
    }

    pub fn roots_of_defining_polynomial() -> Vec<Fq<P, N, M>> {
        let mut root = Self::generator();
        let mut roots = Vec::with_capacity(N);
        for _ in 0..N {
            roots.push(root.clone());
            root = Self::pow(root, u128::from(P));
        }
        roots
    }
}

impl<const P: u64, const N: usize, M> SemiRing for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Domain = Fq<P, N, M>;
    type Addition = QuotientOp<Modulus<P, N, M>>;
    type Multiplication = QuotientMul<Modulus<P, N, M>>;
}

impl<const P: u64, const N: usize, M> Module for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Scalars = PrimeField<P>;
    type Domain = Fq<P, N, M>;
    type Addition = QuotientOp<Modulus<P, N, M>>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        Quotient::new(&Univariate::new(vec![scalar]) * value.representative())
    }
}

impl<const P: u64, const N: usize, M> FieldExtension for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type BaseField = PrimeField<P>;
}

impl<const P: u64, const N: usize, M> FiniteExtension for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    const DEGREE: usize = N;
}

/// `F_(P^N)` whose power-basis generator is multiplicatively primitive.
pub type PrimitiveFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstPrimitive>;

/// A deterministic pseudo-Conway-style finite field.
pub type CompatibleFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstCompatible>;

#[derive(Clone, Debug)]
pub struct CompatibleFiniteFieldEmbedding<
    const P: u64,
    const SOURCE_DEGREE: usize,
    const TARGET_DEGREE: usize,
> {
    generator_image: Fq<P, TARGET_DEGREE, FirstCompatible>,
}

impl<const P: u64, const SOURCE_DEGREE: usize, const TARGET_DEGREE: usize>
    CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    pub fn new() -> Self {
        const {
            Fp::<P>::assert_valid();
            assert!(
                SOURCE_DEGREE > 0
                    && TARGET_DEGREE > 0
                    && TARGET_DEGREE.is_multiple_of(SOURCE_DEGREE),
                "source degree must divide target degree"
            );
        };
        let source_order = Univariate::<PrimeField<P>>::extension_order(SOURCE_DEGREE)
            .expect("finite-field order is too large");
        let target_order = Univariate::<PrimeField<P>>::extension_order(TARGET_DEGREE)
            .expect("finite-field order is too large");
        let generator_image = CompatibleFiniteField::<P, TARGET_DEGREE>::pow(
            CompatibleFiniteField::<P, TARGET_DEGREE>::generator(),
            (target_order - 1) / (source_order - 1),
        );
        Self { generator_image }
    }

    pub fn embed(
        &self,
        value: Fq<P, SOURCE_DEGREE, FirstCompatible>,
    ) -> Fq<P, TARGET_DEGREE, FirstCompatible> {
        self.map(value)
    }

    pub const fn generator_image(&self) -> &Fq<P, TARGET_DEGREE, FirstCompatible> {
        &self.generator_image
    }
}

impl<const P: u64, const SOURCE_DEGREE: usize, const TARGET_DEGREE: usize> Default
    for CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const P: u64, const SOURCE_DEGREE: usize, const TARGET_DEGREE: usize>
    Map<Fq<P, SOURCE_DEGREE, FirstCompatible>, Fq<P, TARGET_DEGREE, FirstCompatible>>
    for CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    fn map(
        &self,
        value: Fq<P, SOURCE_DEGREE, FirstCompatible>,
    ) -> Fq<P, TARGET_DEGREE, FirstCompatible> {
        CompatibleFiniteField::<P, TARGET_DEGREE>::evaluate_base_polynomial(
            value.representative(),
            self.generator_image.clone(),
        )
    }
}

impl<const P: u64> Univariate<PrimeField<P>> {
    /// Every monic polynomial of the given degree, in base-`P` coefficient
    /// order.
    fn monic(degree: usize) -> impl Iterator<Item = Self> {
        let mut lower = Some(vec![0u64; degree]);
        std::iter::from_fn(move || {
            let digits = lower.as_mut()?;
            let mut coefficients: Vec<_> = digits.iter().copied().map(Fp::new).collect();
            coefficients.push(Fp::one());

            let mut overflowed = true;
            for digit in digits.iter_mut() {
                *digit += 1;
                if *digit < P {
                    overflowed = false;
                    break;
                }
                *digit = 0;
            }
            if overflowed {
                lower = None;
            }
            Some(Self::new(coefficients))
        })
    }

    /// `P^degree`, the order of the degree-`degree` extension of `F_P`.
    fn extension_order(degree: usize) -> Option<u128> {
        let mut order = 1u128;
        for _ in 0..degree {
            order = order.checked_mul(u128::from(P))?;
        }
        Some(order)
    }

    pub fn is_irreducible(&self) -> bool {
        if !Fp::<P>::is_valid() {
            return false;
        }
        let Some(degree) = self.degree().filter(|&degree| degree > 0) else {
            return false;
        };
        (1..=degree / 2).all(|d| Self::monic(d).all(|divisor| !(self.clone() % &divisor).is_zero()))
    }

    pub fn is_primitive(&self) -> bool {
        fn prime_factors(mut value: u128) -> Vec<u128> {
            let mut factors = Vec::new();
            let mut divisor = 2;
            while divisor <= value / divisor {
                if value.is_multiple_of(divisor) {
                    factors.push(divisor);
                    while value.is_multiple_of(divisor) {
                        value /= divisor;
                    }
                }
                divisor += 1;
            }
            if value > 1 {
                factors.push(value);
            }
            factors
        }

        if self.leading() != Some(&Fp::one()) || !self.is_irreducible() {
            return false;
        }
        let Some(order) = self
            .degree()
            .and_then(Self::extension_order)
            .map(|order| order - 1)
        else {
            return false;
        };
        let generator = Self::x() % self;
        if generator.is_zero() || generator.clone().pow_mod(order, self) != Self::one() {
            return false;
        }
        prime_factors(order)
            .into_iter()
            .all(|factor| generator.clone().pow_mod(order / factor, self) != Self::one())
    }

    fn is_compatible(&self) -> bool {
        if !self.is_primitive() {
            return false;
        }
        let degree = self
            .degree()
            .expect("a primitive polynomial has positive degree");
        let order = Self::extension_order(degree).expect("finite-field order is too large");
        let generator = Self::x() % self;

        (1..degree).filter(|d| degree.is_multiple_of(*d)).all(|d| {
            let subfield_order = Self::extension_order(d).unwrap();
            let subfield_generator = generator
                .clone()
                .pow_mod((order - 1) / (subfield_order - 1), self);
            subfield_generator.minimal_polynomial(d, self)
                == Some(PolynomialSelection::Compatible.generate(d))
        })
    }

    /// The minimal polynomial over `F_P` of `self` as an element of
    /// `F_P[x] / (modulus)`, if it has the given degree.
    fn minimal_polynomial(self, degree: usize, modulus: &Self) -> Option<Self> {
        let mut polynomial = vec![Self::one()];
        let mut conjugate = self;

        for _ in 0..degree {
            let mut product = vec![Self::zero(); polynomial.len() + 1];
            for (i, coefficient) in polynomial.into_iter().enumerate() {
                let constant = &coefficient * &-conjugate.clone() % modulus;
                product[i] = std::mem::take(&mut product[i]) + constant;
                product[i + 1] = std::mem::take(&mut product[i + 1]) + coefficient;
            }
            polynomial = product;
            conjugate = conjugate.pow_mod(u128::from(P), modulus);
        }

        polynomial
            .into_iter()
            .map(|coefficient| match coefficient.coefficients() {
                [] => Some(Fp::zero()),
                [constant] => Some(*constant),
                _ => None,
            })
            .collect::<Option<_>>()
            .map(Self::new)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PolynomialSelection {
    Irreducible,
    Primitive,
    Compatible,
}

impl PolynomialSelection {
    /// The first monic polynomial of the given degree matching this selection,
    /// in base-`P` coefficient order.
    fn generate<const P: u64>(self, degree: usize) -> Univariate<PrimeField<P>> {
        static CACHE: OnceLock<Mutex<HashMap<(u64, usize, PolynomialSelection), Vec<u64>>>> =
            OnceLock::new();
        let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));

        if let Some(coefficients) = cache.lock().unwrap().get(&(P, degree, self)).cloned() {
            return Univariate::new(coefficients.into_iter().map(Fp::new).collect());
        }

        assert!(degree > 0, "a field extension must have positive degree");
        const { Fp::<P>::assert_valid() };

        let polynomial = Univariate::<PrimeField<P>>::monic(degree)
            .find(|candidate| match self {
                PolynomialSelection::Irreducible => candidate.is_irreducible(),
                PolynomialSelection::Primitive => candidate.is_primitive(),
                PolynomialSelection::Compatible => candidate.is_compatible(),
            })
            .expect("no defining polynomial found");

        cache.lock().unwrap().insert(
            (P, degree, self),
            polynomial
                .coefficients()
                .iter()
                .map(|coefficient| coefficient.value())
                .collect(),
        );
        polynomial
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::Field;
    use eqn_algebra::group::quotient::Modulo;
    use eqn_algebra::ring::Ring;
    use eqn_core::quotient::Equivalence;

    use super::*;

    struct X2PlusOne;

    impl DefiningPolynomial<3, 2> for X2PlusOne {
        fn coefficients() -> Vec<Fp<3>> {
            [1, 0, 1].map(Fp::new).to_vec()
        }
    }

    impl IrreduciblePolynomial<3, 2> for X2PlusOne {}

    #[test]
    fn generated_modulus_is_deterministic_and_irreducible() {
        let expected = Univariate::new([1, 1, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<2, 2>::modulus(), expected);
        assert!(FiniteField::<2, 2>::modulus_is_irreducible());
        assert_eq!(
            FiniteField::<2, 2>::modulus(),
            FiniteField::<2, 2>::modulus()
        );

        let expected = Univariate::new([1, 1, 0, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<2, 3>::modulus(), expected);
        assert!(FiniteField::<2, 3>::modulus_is_irreducible());

        let expected = Univariate::new([1, 0, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<3, 2>::modulus(), expected);

        let expected = Univariate::new([1, 1, 0, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<5, 3>::modulus(), expected);
    }

    #[test]
    fn primitive_modulus_gives_a_multiplicative_generator() {
        type F9 = PrimitiveFiniteField<3, 2>;

        let modulus = F9::modulus();
        let generator = F9::from_values([0, 1]);
        assert!(modulus.is_primitive());
        assert_eq!(F9::pow(generator.clone(), 8), F9::one());
        assert_ne!(F9::pow(generator, 4), F9::one());

        let irreducible = Univariate::new([1, 0, 1].map(Fp::<3>::new).to_vec());
        assert!(irreducible.is_irreducible());
        assert!(!irreducible.is_primitive());
    }

    #[test]
    fn explicit_modulus_defines_multiplication() {
        type F9 = FiniteField<3, 2, X2PlusOne>;

        let alpha = F9::from_values([0, 1]);
        assert_eq!(F9::multiply(alpha.clone(), alpha), F9::from_values([2, 0]));
        assert!(F9::modulus_is_irreducible());
    }

    #[test]
    fn defining_polynomial_splits_into_frobenius_conjugates() {
        type F9 = FiniteField<3, 2, X2PlusOne>;

        let alpha = F9::generator();
        let roots = F9::roots_of_defining_polynomial();
        assert_eq!(roots, vec![alpha.clone(), F9::pow(alpha, 3)]);
        assert_ne!(roots[0], roots[1]);
        for root in roots {
            assert_eq!(
                F9::evaluate_base_polynomial(&F9::modulus(), root),
                F9::zero()
            );
        }
    }

    #[test]
    fn compatible_fields_form_a_tower() {
        type F4 = CompatibleFiniteField<2, 2>;
        type F16 = CompatibleFiniteField<2, 4>;

        let target_generator = F16::generator();
        let subfield_generator = F16::pow(target_generator, 5);
        assert_eq!(
            F16::evaluate_base_polynomial(&F4::modulus(), subfield_generator),
            F16::zero()
        );
    }

    #[test]
    fn compatible_embedding_preserves_field_operations() {
        type F4 = CompatibleFiniteField<2, 2>;
        type F16 = CompatibleFiniteField<2, 4>;

        let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
        assert_eq!(embedding.embed(F4::zero()), F16::zero());
        assert_eq!(embedding.embed(F4::one()), F16::one());
        assert_eq!(
            embedding.embed(F4::generator()),
            F16::pow(F16::generator(), 5)
        );
        let elements: Vec<_> = (0..2)
            .flat_map(|a| (0..2).map(move |b| F4::from_values([a, b])))
            .collect();

        for a in &elements {
            for b in &elements {
                assert_eq!(
                    embedding.embed(F4::add(a.clone(), b.clone())),
                    F16::add(embedding.embed(a.clone()), embedding.embed(b.clone()))
                );
                assert_eq!(
                    embedding.embed(F4::multiply(a.clone(), b.clone())),
                    F16::multiply(embedding.embed(a.clone()), embedding.embed(b.clone()))
                );
            }
        }
    }

    #[test]
    fn compatible_embeddings_compose_across_towers() {
        type F4 = CompatibleFiniteField<2, 2>;

        let into_f16 = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
        let into_f256 = CompatibleFiniteFieldEmbedding::<2, 4, 8>::new();
        let direct = CompatibleFiniteFieldEmbedding::<2, 2, 8>::new();

        for a in 0..2 {
            for b in 0..2 {
                let value = F4::from_values([a, b]);
                assert_eq!(
                    direct.embed(value.clone()),
                    into_f256.embed(into_f16.embed(value))
                );
            }
        }
    }

    #[test]
    fn every_nonzero_element_of_f4_is_invertible() {
        type F4 = FiniteField<2, 2>;

        for a in 0..2 {
            for b in 0..2 {
                let value = F4::from_values([a, b]);
                if value != F4::zero() {
                    assert_eq!(F4::multiply(value.clone(), F4::invert(value)), F4::one());
                }
            }
        }
    }

    #[test]
    fn every_nonzero_element_of_explicit_f9_is_invertible() {
        type F9 = FiniteField<3, 2, X2PlusOne>;

        for a in 0..3 {
            for b in 0..3 {
                let value = F9::from_values([a, b]);
                if value != F9::zero() {
                    assert_eq!(F9::multiply(value.clone(), F9::invert(value)), F9::one());
                }
            }
        }
    }

    #[test]
    fn rejects_reducible_polynomials() {
        let reducible = Univariate::new([0, 1, 1].map(Fp::<2>::new).to_vec());
        assert!(!reducible.is_irreducible());
    }

    #[test]
    fn extension_arithmetic_satisfies_field_laws() {
        type F4 = FiniteField<2, 2>;

        let elements: Vec<_> = (0..2)
            .flat_map(|a| (0..2).map(move |b| F4::from_values([a, b])))
            .collect();

        for a in &elements {
            assert_eq!(F4::add(a.clone(), F4::zero()), *a);
            assert_eq!(F4::multiply(a.clone(), F4::one()), *a);
            assert_eq!(F4::add(a.clone(), F4::negate(a.clone())), F4::zero());
            for b in &elements {
                for c in &elements {
                    assert_eq!(
                        F4::add(F4::add(a.clone(), b.clone()), c.clone()),
                        F4::add(a.clone(), F4::add(b.clone(), c.clone()))
                    );
                    assert_eq!(
                        F4::multiply(F4::multiply(a.clone(), b.clone()), c.clone()),
                        F4::multiply(a.clone(), F4::multiply(b.clone(), c.clone()))
                    );
                    assert_eq!(
                        F4::multiply(a.clone(), F4::add(b.clone(), c.clone())),
                        F4::add(
                            F4::multiply(a.clone(), b.clone()),
                            F4::multiply(a.clone(), c.clone())
                        )
                    );
                }
            }
        }
    }

    #[test]
    fn reduction_by_the_defining_polynomial_is_a_congruence_for_both_ring_operations() {
        type F9Modulus = Modulus<3, 2>;
        type F3x = UnivariateRing<PrimeField<3>>;

        let polynomials =
            || (0..27u64).map(|i| Univariate::new([i % 3, i / 3 % 3, i / 9].map(Fp::new).to_vec()));

        for a in polynomials() {
            for b in polynomials() {
                let (a_reduced, b_reduced) =
                    (F9Modulus::reduce(a.clone()), F9Modulus::reduce(b.clone()));

                assert_eq!(
                    F9Modulus::reduce(F3x::add(a.clone(), b.clone())),
                    F9Modulus::reduce(F3x::add(a_reduced.clone(), b_reduced.clone()))
                );
                assert_eq!(
                    F9Modulus::reduce(F3x::multiply(a.clone(), b)),
                    F9Modulus::reduce(F3x::multiply(a_reduced, b_reduced))
                );
            }
        }
    }

    #[test]
    fn classes_are_equal_exactly_when_the_coset_relation_holds() {
        let modulus = FiniteField::<3, 2>::modulus();
        let residues = || (0..9u64).map(|i| Univariate::new([i % 3, i / 3].map(Fp::new).to_vec()));

        for a in residues() {
            for b in residues().map(|residue| residue + modulus.clone()) {
                assert_eq!(
                    Fq::<3, 2>::new(a.clone()) == Fq::<3, 2>::new(b.clone()),
                    Modulo::<Modulus<3, 2>>::equivalent(&a, &b)
                );
            }
        }
    }
}
