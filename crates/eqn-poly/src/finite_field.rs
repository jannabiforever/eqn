use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::sync::{Mutex, OnceLock};

use eqn_algebra::field::{
    FieldExtension, FieldHomomorphism, FiniteExtension, NormalExtension, PrimeField,
    PrimeFieldElement, SeparableExtension, SplittingField,
};
use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::SemiRing;
use eqn_core::map::Map;
use eqn_core::op::{Associative, BinaryOperator, Commutative, Inverse};
use eqn_core::set::Set;

/// A monic degree-`N` polynomial over `F_P`, stored from constant to leading
/// coefficient.
pub trait DefiningPolynomial<const P: u64, const N: usize> {
    fn coefficients() -> Vec<PrimeFieldElement<P>>;
}

/// A defining polynomial known to be irreducible over `F_P`.
pub trait IrreduciblePolynomial<const P: u64, const N: usize>: DefiningPolynomial<P, N> {}

/// Selects the first irreducible polynomial in base-`P` coefficient order.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstIrreducible;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstIrreducible {
    fn coefficients() -> Vec<PrimeFieldElement<P>> {
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
    fn coefficients() -> Vec<PrimeFieldElement<P>> {
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
    fn coefficients() -> Vec<PrimeFieldElement<P>> {
        PolynomialSelection::Compatible
            .generate(N)
            .into_coefficients()
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstCompatible {}

/// A canonical power-basis representative of a finite-field element.
#[derive_where::derive_where(Clone, Copy, Eq, PartialEq)]
pub struct FiniteFieldElement<const P: u64, const N: usize, M = FirstIrreducible> {
    coefficients: [PrimeFieldElement<P>; N],
    modulus: PhantomData<M>,
}

impl<const P: u64, const N: usize, M> FiniteFieldElement<P, N, M> {
    pub const ZERO: Self = Self {
        coefficients: [PrimeFieldElement::ZERO; N],
        modulus: PhantomData,
    };

    pub const ONE: Self = {
        let mut coefficients = [PrimeFieldElement::ZERO; N];
        if N > 0 {
            coefficients[0] = PrimeFieldElement::ONE;
        }
        Self {
            coefficients,
            modulus: PhantomData,
        }
    };

    pub const fn from_coefficients(coefficients: [PrimeFieldElement<P>; N]) -> Self {
        assert!(N > 0, "a field extension must have positive degree");
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    pub fn from_values(values: [u64; N]) -> Self {
        Self::from_coefficients(values.map(PrimeFieldElement::new))
    }

    pub const fn coefficients(&self) -> &[PrimeFieldElement<P>; N] {
        &self.coefficients
    }

    pub const fn into_coefficients(self) -> [PrimeFieldElement<P>; N] {
        self.coefficients
    }

    pub fn is_zero(self) -> bool {
        self.coefficients
            .iter()
            .all(|coefficient| coefficient.is_zero())
    }

    pub fn pow(self, mut exponent: u128) -> Self
    where
        M: IrreduciblePolynomial<P, N>,
    {
        let mut result = Self::ONE;
        let mut base = self;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = FiniteFieldMul::apply(result, base);
            }
            exponent >>= 1;
            if exponent > 0 {
                base = FiniteFieldMul::apply(base, base);
            }
        }
        result
    }

    /// The multiplicative inverse, by the extended Euclidean algorithm on
    /// `F_P[x]`. Panics on zero.
    pub fn inverse(self) -> Self
    where
        M: IrreduciblePolynomial<P, N>,
    {
        let modulus = FiniteField::<P, N, M>::modulus();
        let remainder = self.into_polynomial();
        assert!(!remainder.is_zero(), "zero has no multiplicative inverse");

        let mut old_r = modulus.clone();
        let mut r = remainder;
        let mut old_t = UnivariatePolynomial::zero();
        let mut t = UnivariatePolynomial::one();

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
        let scaled = UnivariatePolynomial::new(
            old_t
                .into_coefficients()
                .into_iter()
                .map(|coefficient| coefficient * scale)
                .collect(),
        );
        Self::from_polynomial(scaled % &modulus)
    }

    /// The element `value \cdot 1`.
    fn from_constant(value: PrimeFieldElement<P>) -> Self {
        let mut coefficients = [PrimeFieldElement::ZERO; N];
        assert!(N > 0, "a field extension must have positive degree");
        coefficients[0] = value;
        Self::from_coefficients(coefficients)
    }

    /// The power-basis element of a polynomial of degree below `N`.
    fn from_polynomial(polynomial: UnivariatePolynomial<P>) -> Self {
        let mut coefficients = [PrimeFieldElement::ZERO; N];
        for (target, coefficient) in coefficients.iter_mut().zip(polynomial.into_coefficients()) {
            *target = coefficient;
        }
        Self::from_coefficients(coefficients)
    }

    fn into_polynomial(self) -> UnivariatePolynomial<P> {
        UnivariatePolynomial::new(self.coefficients.to_vec())
    }
}

impl<const P: u64, const N: usize, M> Add for FiniteFieldElement<P, N, M> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        FiniteFieldElement::from_coefficients(std::array::from_fn(|i| {
            self.coefficients[i] + rhs.coefficients[i]
        }))
    }
}

impl<const P: u64, const N: usize, M> Sub for FiniteFieldElement<P, N, M> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        FiniteFieldAdd::apply(self, FiniteFieldAdd::inverse(rhs))
    }
}

impl<const P: u64, const N: usize, M> Mul for FiniteFieldElement<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let modulus = FiniteField::<P, N, M>::modulus();
        Self::from_polynomial(&self.into_polynomial() * &rhs.into_polynomial() % &modulus)
    }
}

impl<const P: u64, const N: usize, M> Div for FiniteFieldElement<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Mul::mul(self, rhs.inverse())
    }
}

impl<const P: u64, const N: usize, M> std::ops::Neg for FiniteFieldElement<P, N, M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        FiniteFieldElement::from_coefficients(self.coefficients.map(Neg::neg))
    }
}

impl<const P: u64, const N: usize, M> fmt::Debug for FiniteFieldElement<P, N, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FiniteFieldElement")
            .field(&self.coefficients)
            .finish()
    }
}

#[derive(Set)]
#[set(element = FiniteFieldElement<P, N, M>)]
pub struct FiniteFieldElements<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = FiniteFieldElements<P, N, M>, apply = FiniteFieldElement::add, identity = FiniteFieldElement::ZERO, inverse = Neg::neg)]
pub struct FiniteFieldAdd<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = FiniteFieldElements<P, N, M>, apply = Mul::mul, identity = FiniteFieldElement::ONE, inverse = |a| a.inverse())]
pub struct FiniteFieldMul<
    const P: u64,
    const N: usize,
    M: IrreduciblePolynomial<P, N> = FirstIrreducible,
>(PhantomData<M>);

/// The quotient field `F_P[x] / (M)` of degree `N`.
pub struct FiniteField<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    pub fn modulus() -> UnivariatePolynomial<P> {
        assert!(
            PrimeField::<P>::is_valid(),
            "finite-field characteristic must be prime"
        );
        let coefficients = M::coefficients();
        assert_eq!(
            coefficients.len(),
            N + 1,
            "defining polynomial must have degree N"
        );
        assert_eq!(
            coefficients.last(),
            Some(&PrimeFieldElement::ONE),
            "defining polynomial must be monic"
        );
        UnivariatePolynomial::new(coefficients)
    }

    pub fn modulus_is_irreducible() -> bool {
        Self::modulus().is_irreducible()
    }

    pub fn generator() -> FiniteFieldElement<P, N, M> {
        FiniteFieldElement::from_polynomial(UnivariatePolynomial::x() % &Self::modulus())
    }

    pub fn evaluate_base_polynomial(
        polynomial: &UnivariatePolynomial<P>,
        value: FiniteFieldElement<P, N, M>,
    ) -> FiniteFieldElement<P, N, M> {
        polynomial
            .coefficients()
            .iter()
            .rev()
            .fold(FiniteFieldElement::ZERO, |result, &coefficient| {
                result * value + FiniteFieldElement::from_constant(coefficient)
            })
    }

    pub fn roots_of_defining_polynomial() -> Vec<FiniteFieldElement<P, N, M>> {
        let mut root = Self::generator();
        let mut roots = Vec::with_capacity(N);
        for _ in 0..N {
            roots.push(root);
            root = root.pow(u128::from(P));
        }
        roots
    }
}

impl<const P: u64, const N: usize, M> SemiRing for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Domain = FiniteFieldElements<P, N, M>;
    type Addition = FiniteFieldAdd<P, N, M>;
    type Multiplication = FiniteFieldMul<P, N, M>;
}

impl<const P: u64, const N: usize, M> Module for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Scalars = PrimeField<P>;
    type Domain = FiniteFieldElements<P, N, M>;
    type Addition = FiniteFieldAdd<P, N, M>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        FiniteFieldElement::from_coefficients(
            value.coefficients.map(|coefficient| scalar * coefficient),
        )
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
    type const DEGREE: usize = N;
}

impl<const P: u64, const N: usize, M> NormalExtension for FiniteField<P, N, M> where
    M: IrreduciblePolynomial<P, N>
{
}

impl<const P: u64, const N: usize, M> SeparableExtension for FiniteField<P, N, M> where
    M: IrreduciblePolynomial<P, N>
{
}

impl<const P: u64, const N: usize, M> SplittingField<M> for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    fn roots() -> Vec<FiniteFieldElement<P, N, M>> {
        Self::roots_of_defining_polynomial()
    }
}

/// `F_(P^N)` using the deterministic default defining polynomial.
pub type Fq<const P: u64, const N: usize> = FiniteField<P, N, FirstIrreducible>;
pub type FqElement<const P: u64, const N: usize> = FiniteFieldElement<P, N, FirstIrreducible>;

/// `F_(P^N)` whose power-basis generator is multiplicatively primitive.
pub type PrimitiveFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstPrimitive>;
pub type PrimitiveFiniteFieldElement<const P: u64, const N: usize> =
    FiniteFieldElement<P, N, FirstPrimitive>;

/// A deterministic pseudo-Conway-style finite field.
pub type CompatibleFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstCompatible>;
pub type CompatibleFiniteFieldElement<const P: u64, const N: usize> =
    FiniteFieldElement<P, N, FirstCompatible>;

#[derive(Clone, Copy, Debug)]
pub struct CompatibleFiniteFieldEmbedding<
    const P: u64,
    const SOURCE_DEGREE: usize,
    const TARGET_DEGREE: usize,
> {
    generator_image: CompatibleFiniteFieldElement<P, TARGET_DEGREE>,
}

impl<const P: u64, const SOURCE_DEGREE: usize, const TARGET_DEGREE: usize>
    CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    pub fn new() -> Self {
        assert!(
            PrimeField::<P>::is_valid(),
            "finite-field characteristic must be prime"
        );
        assert!(
            SOURCE_DEGREE > 0 && TARGET_DEGREE > 0 && TARGET_DEGREE.is_multiple_of(SOURCE_DEGREE),
            "source degree must divide target degree"
        );
        let source_order = UnivariatePolynomial::<P>::extension_order(SOURCE_DEGREE)
            .expect("finite-field order is too large");
        let target_order = UnivariatePolynomial::<P>::extension_order(TARGET_DEGREE)
            .expect("finite-field order is too large");
        let generator_image = CompatibleFiniteField::<P, TARGET_DEGREE>::generator()
            .pow((target_order - 1) / (source_order - 1));
        Self { generator_image }
    }

    pub fn embed(
        &self,
        value: CompatibleFiniteFieldElement<P, SOURCE_DEGREE>,
    ) -> CompatibleFiniteFieldElement<P, TARGET_DEGREE> {
        self.map(value)
    }

    pub const fn generator_image(&self) -> CompatibleFiniteFieldElement<P, TARGET_DEGREE> {
        self.generator_image
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
    Map<
        FiniteFieldElements<P, SOURCE_DEGREE, FirstCompatible>,
        FiniteFieldElements<P, TARGET_DEGREE, FirstCompatible>,
    > for CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    fn map(
        &self,
        value: CompatibleFiniteFieldElement<P, SOURCE_DEGREE>,
    ) -> CompatibleFiniteFieldElement<P, TARGET_DEGREE> {
        value.coefficients.iter().rev().fold(
            CompatibleFiniteFieldElement::ZERO,
            |result, &coefficient| {
                result * self.generator_image
                    + CompatibleFiniteFieldElement::from_constant(coefficient)
            },
        )
    }
}

impl<const P: u64, const SOURCE_DEGREE: usize, const TARGET_DEGREE: usize>
    FieldHomomorphism<
        CompatibleFiniteField<P, SOURCE_DEGREE>,
        CompatibleFiniteField<P, TARGET_DEGREE>,
    > for CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
}

/// A polynomial in one variable over `F_P`, stored from constant to leading
/// coefficient with no trailing zeros, so the zero polynomial is empty.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UnivariatePolynomial<const P: u64>(Vec<PrimeFieldElement<P>>);

impl<const P: u64> UnivariatePolynomial<P> {
    pub fn new(coefficients: Vec<PrimeFieldElement<P>>) -> Self {
        let mut polynomial = Self(coefficients);
        polynomial.trim();
        polynomial
    }

    pub fn zero() -> Self {
        Self(Vec::new())
    }

    pub fn one() -> Self {
        Self(vec![PrimeFieldElement::ONE])
    }

    /// The indeterminate `x`.
    pub fn x() -> Self {
        Self(vec![PrimeFieldElement::ZERO, PrimeFieldElement::ONE])
    }

    pub fn coefficients(&self) -> &[PrimeFieldElement<P>] {
        &self.0
    }

    pub fn into_coefficients(self) -> Vec<PrimeFieldElement<P>> {
        self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn trim(&mut self) {
        while self.0.last() == Some(&PrimeFieldElement::ZERO) {
            self.0.pop();
        }
    }

    /// Every monic polynomial of the given degree, in base-`P` coefficient
    /// order.
    fn monic(degree: usize) -> impl Iterator<Item = Self> {
        let mut lower = Some(vec![0u64; degree]);
        std::iter::from_fn(move || {
            let digits = lower.as_mut()?;
            let mut coefficients: Vec<_> =
                digits.iter().copied().map(PrimeFieldElement::new).collect();
            coefficients.push(PrimeFieldElement::ONE);

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
            Some(Self(coefficients))
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
        if !PrimeField::<P>::is_valid() || self.0.len() < 2 {
            return false;
        }
        let degree = self.0.len() - 1;
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

        if self.0.last() != Some(&PrimeFieldElement::ONE) || !self.is_irreducible() {
            return false;
        }
        let Some(order) = Self::extension_order(self.0.len() - 1).map(|order| order - 1) else {
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
        let degree = self.0.len() - 1;
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

    fn pow_mod(mut self, mut exponent: u128, modulus: &Self) -> Self {
        let mut result = Self::one();
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

        let mut coefficients = Vec::with_capacity(polynomial.len());
        for coefficient in polynomial {
            if coefficient.0.len() > 1 {
                return None;
            }
            coefficients.push(
                coefficient
                    .0
                    .first()
                    .copied()
                    .unwrap_or(PrimeFieldElement::ZERO),
            );
        }
        Some(Self::new(coefficients))
    }

    fn div_rem(mut self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "division by the zero polynomial");
        if self.0.len() < divisor.0.len() {
            return (Self::zero(), self);
        }

        let mut quotient = vec![PrimeFieldElement::ZERO; self.0.len() - divisor.0.len() + 1];
        let leading_inverse = divisor.0.last().copied().unwrap().inverse();
        while self.0.len() >= divisor.0.len() {
            let shift = self.0.len() - divisor.0.len();
            let coefficient = self.0.last().copied().unwrap() * leading_inverse;
            quotient[shift] = coefficient;
            for (i, &divisor_coefficient) in divisor.0.iter().enumerate() {
                self.0[i + shift] = self.0[i + shift] - coefficient * divisor_coefficient;
            }
            self.trim();
        }
        (Self::new(quotient), self)
    }
}

impl<const P: u64> Add for UnivariatePolynomial<P> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self {
        self.0
            .resize(self.0.len().max(rhs.0.len()), PrimeFieldElement::ZERO);
        for (i, coefficient) in rhs.0.into_iter().enumerate() {
            self.0[i] = self.0[i] + coefficient;
        }
        Self::new(self.0)
    }
}

impl<const P: u64> Sub for UnivariatePolynomial<P> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self {
        self.0
            .resize(self.0.len().max(rhs.0.len()), PrimeFieldElement::ZERO);
        for (i, coefficient) in rhs.0.into_iter().enumerate() {
            self.0[i] = self.0[i] - coefficient;
        }
        Self::new(self.0)
    }
}

impl<const P: u64> Neg for UnivariatePolynomial<P> {
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.into_iter().map(Neg::neg).collect())
    }
}

impl<const P: u64> Mul for &UnivariatePolynomial<P> {
    type Output = UnivariatePolynomial<P>;

    fn mul(self, rhs: Self) -> UnivariatePolynomial<P> {
        if self.is_zero() || rhs.is_zero() {
            return UnivariatePolynomial::zero();
        }
        let mut product = vec![PrimeFieldElement::ZERO; self.0.len() + rhs.0.len() - 1];
        for (i, &a) in self.0.iter().enumerate() {
            for (j, &b) in rhs.0.iter().enumerate() {
                product[i + j] = product[i + j] + a * b;
            }
        }
        UnivariatePolynomial::new(product)
    }
}

impl<const P: u64> Rem<&UnivariatePolynomial<P>> for UnivariatePolynomial<P> {
    type Output = Self;

    fn rem(self, modulus: &Self) -> Self {
        self.div_rem(modulus).1
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
    fn generate<const P: u64>(self, degree: usize) -> UnivariatePolynomial<P> {
        static CACHE: OnceLock<Mutex<HashMap<(u64, usize, PolynomialSelection), Vec<u64>>>> =
            OnceLock::new();
        let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));

        if let Some(coefficients) = cache.lock().unwrap().get(&(P, degree, self)).cloned() {
            return UnivariatePolynomial::new(
                coefficients
                    .into_iter()
                    .map(PrimeFieldElement::new)
                    .collect(),
            );
        }

        assert!(degree > 0, "a field extension must have positive degree");
        assert!(
            PrimeField::<P>::is_valid(),
            "finite-field characteristic must be prime"
        );

        let polynomial = UnivariatePolynomial::<P>::monic(degree)
            .find(|candidate| match self {
                PolynomialSelection::Irreducible => candidate.is_irreducible(),
                PolynomialSelection::Primitive => candidate.is_primitive(),
                PolynomialSelection::Compatible => candidate.is_compatible(),
            })
            .expect("no defining polynomial found");

        cache.lock().unwrap().insert(
            (P, degree, self),
            polynomial
                .0
                .iter()
                .map(|coefficient| coefficient.value())
                .collect(),
        );
        polynomial
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::algebra::Algebra;
    use eqn_algebra::field::{
        AlgebraicExtension, Field, FieldEmbedding, GaloisExtension, SplittingField,
    };
    use eqn_algebra::ring::{Ring, SemiRing};

    use super::*;

    struct X2PlusOne;

    impl DefiningPolynomial<3, 2> for X2PlusOne {
        fn coefficients() -> Vec<PrimeFieldElement<3>> {
            [1, 0, 1].map(PrimeFieldElement::new).to_vec()
        }
    }

    impl IrreduciblePolynomial<3, 2> for X2PlusOne {}

    struct CompositeCharacteristicModulus;

    impl DefiningPolynomial<4, 1> for CompositeCharacteristicModulus {
        fn coefficients() -> Vec<PrimeFieldElement<4>> {
            vec![PrimeFieldElement::ZERO, PrimeFieldElement::ONE]
        }
    }

    impl IrreduciblePolynomial<4, 1> for CompositeCharacteristicModulus {}

    #[test]
    fn generated_modulus_is_deterministic_and_irreducible() {
        let expected = UnivariatePolynomial::new([1, 1, 1].map(PrimeFieldElement::new).to_vec());
        assert_eq!(Fq::<2, 2>::modulus(), expected);
        assert!(Fq::<2, 2>::modulus_is_irreducible());
        assert_eq!(Fq::<2, 2>::modulus(), Fq::<2, 2>::modulus());

        let expected = UnivariatePolynomial::new([1, 1, 0, 1].map(PrimeFieldElement::new).to_vec());
        assert_eq!(Fq::<2, 3>::modulus(), expected);
        assert!(Fq::<2, 3>::modulus_is_irreducible());
    }

    #[test]
    fn primitive_modulus_gives_a_multiplicative_generator() {
        type F9 = PrimitiveFiniteField<3, 2>;
        type E = PrimitiveFiniteFieldElement<3, 2>;

        let modulus = F9::modulus();
        let generator = E::from_values([0, 1]);
        assert!(modulus.is_primitive());
        assert_eq!(generator.pow(8), E::ONE);
        assert_ne!(generator.pow(4), E::ONE);

        let irreducible =
            UnivariatePolynomial::new([1, 0, 1].map(PrimeFieldElement::<3>::new).to_vec());
        assert!(irreducible.is_irreducible());
        assert!(!irreducible.is_primitive());
    }

    #[test]
    fn explicit_modulus_defines_multiplication() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = FiniteFieldElement<3, 2, X2PlusOne>;

        let alpha = E::from_values([0, 1]);
        assert_eq!(F9::multiply(alpha, alpha), E::from_values([2, 0]));
        assert!(F9::modulus_is_irreducible());
    }

    #[test]
    fn defining_polynomial_splits_into_frobenius_conjugates() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = FiniteFieldElement<3, 2, X2PlusOne>;

        fn assert_splitting_field<F: SplittingField<X2PlusOne>>() {}
        assert_splitting_field::<F9>();

        let alpha = F9::generator();
        let roots = <F9 as SplittingField<X2PlusOne>>::roots();
        assert_eq!(roots, vec![alpha, alpha.pow(3)]);
        assert_ne!(roots[0], roots[1]);
        for root in roots {
            assert_eq!(F9::evaluate_base_polynomial(&F9::modulus(), root), E::ZERO);
        }
    }

    #[test]
    fn compatible_fields_form_a_tower() {
        type F4 = CompatibleFiniteField<2, 2>;
        type F16 = CompatibleFiniteField<2, 4>;

        let target_generator = F16::generator();
        let subfield_generator = target_generator.pow(5);
        assert_eq!(
            F16::evaluate_base_polynomial(&F4::modulus(), subfield_generator),
            CompatibleFiniteFieldElement::ZERO
        );
    }

    #[test]
    fn compatible_embedding_preserves_field_operations() {
        type F4 = CompatibleFiniteField<2, 2>;
        type F16 = CompatibleFiniteField<2, 4>;
        type E4 = CompatibleFiniteFieldElement<2, 2>;
        type E16 = CompatibleFiniteFieldElement<2, 4>;

        fn assert_embedding<E: FieldEmbedding<F4, F16>>() {}
        assert_embedding::<CompatibleFiniteFieldEmbedding<2, 2, 4>>();

        let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
        assert_eq!(embedding.embed(E4::ZERO), E16::ZERO);
        assert_eq!(embedding.embed(E4::ONE), E16::ONE);
        assert_eq!(embedding.embed(F4::generator()), F16::generator().pow(5));
        let elements: Vec<_> = (0..2)
            .flat_map(|a| (0..2).map(move |b| E4::from_values([a, b])))
            .collect();

        for &a in &elements {
            for &b in &elements {
                assert_eq!(
                    embedding.embed(a + b),
                    embedding.embed(a) + embedding.embed(b)
                );
                assert_eq!(
                    embedding.embed(a * b),
                    embedding.embed(a) * embedding.embed(b)
                );
            }
        }
    }

    #[test]
    fn compatible_embeddings_compose_across_towers() {
        type E4 = CompatibleFiniteFieldElement<2, 2>;

        let into_f16 = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
        let into_f256 = CompatibleFiniteFieldEmbedding::<2, 4, 8>::new();
        let direct = CompatibleFiniteFieldEmbedding::<2, 2, 8>::new();

        for a in 0..2 {
            for b in 0..2 {
                let value = E4::from_values([a, b]);
                assert_eq!(direct.embed(value), into_f256.embed(into_f16.embed(value)));
            }
        }
    }

    #[test]
    #[should_panic(expected = "source degree must divide target degree")]
    fn compatible_embedding_rejects_non_divisor_degrees() {
        CompatibleFiniteFieldEmbedding::<2, 2, 3>::new();
    }

    #[test]
    fn every_nonzero_element_of_f4_is_invertible() {
        type F4 = Fq<2, 2>;
        type E = FqElement<2, 2>;

        for a in 0..2 {
            for b in 0..2 {
                let value = E::from_values([a, b]);
                if value != E::ZERO {
                    assert_eq!(F4::multiply(value, F4::invert(value)), F4::ONE);
                }
            }
        }
    }

    #[test]
    fn every_nonzero_element_of_explicit_f9_is_invertible() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = FiniteFieldElement<3, 2, X2PlusOne>;

        for a in 0..3 {
            for b in 0..3 {
                let value = E::from_values([a, b]);
                if value != E::ZERO {
                    assert_eq!(F9::multiply(value, F9::invert(value)), F9::ONE);
                }
            }
        }
    }

    #[test]
    fn finite_fields_expose_the_extension_structure() {
        fn assert_field<F: Field>() {}
        fn assert_algebra<A: Algebra<Scalars = PrimeField<2>>>() {}
        fn assert_extension<
            E: FieldExtension + FiniteExtension + AlgebraicExtension + GaloisExtension,
        >() {
        }

        assert_field::<Fq<2, 3>>();
        assert_algebra::<Fq<2, 3>>();
        assert_extension::<Fq<2, 3>>();
        assert_eq!(<Fq<2, 3> as FiniteExtension>::DEGREE, 3);
    }

    #[test]
    fn rejects_reducible_polynomials() {
        let reducible =
            UnivariatePolynomial::new([0, 1, 1].map(PrimeFieldElement::<2>::new).to_vec());
        assert!(!reducible.is_irreducible());
    }

    #[test]
    #[should_panic(expected = "finite-field characteristic must be prime")]
    fn explicit_extensions_reject_composite_characteristics() {
        FiniteField::<4, 1, CompositeCharacteristicModulus>::modulus();
    }

    #[test]
    fn extension_arithmetic_satisfies_field_laws() {
        type F4 = Fq<2, 2>;
        type E = FqElement<2, 2>;

        let elements: Vec<_> = (0..2)
            .flat_map(|a| (0..2).map(move |b| E::from_values([a, b])))
            .collect();

        for &a in &elements {
            assert_eq!(F4::add(a, F4::ZERO), a);
            assert_eq!(F4::multiply(a, F4::ONE), a);
            assert_eq!(F4::add(a, F4::negate(a)), F4::ZERO);
            for &b in &elements {
                for &c in &elements {
                    assert_eq!(F4::add(F4::add(a, b), c), F4::add(a, F4::add(b, c)));
                    assert_eq!(
                        F4::multiply(F4::multiply(a, b), c),
                        F4::multiply(a, F4::multiply(b, c))
                    );
                    assert_eq!(
                        F4::multiply(a, F4::add(b, c)),
                        F4::add(F4::multiply(a, b), F4::multiply(a, c))
                    );
                }
            }
        }
    }
}
