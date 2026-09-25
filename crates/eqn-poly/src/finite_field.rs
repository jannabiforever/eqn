use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
use std::sync::{Mutex, OnceLock};

use eqn_algebra::field::{
    FieldExtension, FieldHomomorphism, FiniteExtension, Fp, NormalExtension, PrimeField,
    SeparableExtension, SplittingField,
};
use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::SemiRing;
use eqn_core::map::Map;
use eqn_core::op::{Associative, BinaryOperator, Commutative, Inverse};
use eqn_core::set::Set;

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

/// The finite field `F_(P^N)` as a set: a value is a canonical power-basis
/// representative of an element. [`FiniteField<P, N, M>`] is its field
/// structure.
#[derive_where::derive_where(Clone, Copy, Eq, PartialEq)]
pub struct Fq<const P: u64, const N: usize, M = FirstIrreducible> {
    coefficients: [Fp<P>; N],
    modulus: PhantomData<M>,
}

impl<const P: u64, const N: usize, M> Fq<P, N, M> {
    pub const fn zero() -> Self {
        const { assert!(N > 0, "a field extension must have positive degree") };
        Self {
            coefficients: [Fp::zero(); N],
            modulus: PhantomData,
        }
    }

    pub const fn one() -> Self {
        const { assert!(N > 0, "a field extension must have positive degree") };
        let mut coefficients = [Fp::zero(); N];
        coefficients[0] = Fp::one();
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    pub const fn from_coefficients(coefficients: [Fp<P>; N]) -> Self {
        const { assert!(N > 0, "a field extension must have positive degree") };
        Self {
            coefficients,
            modulus: PhantomData,
        }
    }

    pub fn from_values(values: [u64; N]) -> Self {
        Self::from_coefficients(values.map(Fp::new))
    }

    pub const fn coefficients(&self) -> &[Fp<P>; N] {
        &self.coefficients
    }

    pub const fn into_coefficients(self) -> [Fp<P>; N] {
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
        let mut result = Self::one();
        let mut base = self;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = FqMul::apply(result, base);
            }
            exponent >>= 1;
            if exponent > 0 {
                base = FqMul::apply(base, base);
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
    fn from_constant(value: Fp<P>) -> Self {
        let mut coefficients = [Fp::zero(); N];
        coefficients[0] = value;
        Self::from_coefficients(coefficients)
    }

    /// The power-basis element of a polynomial of degree below `N`.
    fn from_polynomial(polynomial: UnivariatePolynomial<P>) -> Self {
        let mut coefficients = [Fp::zero(); N];
        for (target, coefficient) in coefficients.iter_mut().zip(polynomial.into_coefficients()) {
            *target = coefficient;
        }
        Self::from_coefficients(coefficients)
    }

    fn into_polynomial(self) -> UnivariatePolynomial<P> {
        UnivariatePolynomial::new(self.coefficients.to_vec())
    }
}

impl<const P: u64, const N: usize, M> Add for Fq<P, N, M> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Fq::from_coefficients(std::array::from_fn(|i| {
            self.coefficients[i] + rhs.coefficients[i]
        }))
    }
}

impl<const P: u64, const N: usize, M> Sub for Fq<P, N, M> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        FqAdd::apply(self, FqAdd::inverse(rhs))
    }
}

impl<const P: u64, const N: usize, M> Mul for Fq<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let modulus = FiniteField::<P, N, M>::modulus();
        Self::from_polynomial(&self.into_polynomial() * &rhs.into_polynomial() % &modulus)
    }
}

impl<const P: u64, const N: usize, M> Div for Fq<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Mul::mul(self, rhs.inverse())
    }
}

impl<const P: u64, const N: usize, M> std::ops::Neg for Fq<P, N, M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Fq::from_coefficients(self.coefficients.map(Neg::neg))
    }
}

impl<const P: u64, const N: usize, M> fmt::Debug for Fq<P, N, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Fq").field(&self.coefficients).finish()
    }
}

impl<const P: u64, const N: usize, M> Set for Fq<P, N, M> {}

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Fq<P, N, M>,
    symbol = "+",
    apply = Add::add,
    identity = Fq::zero(),
    inverse = Neg::neg,
    inverse_symbol = "-"
)]
pub struct FqAdd<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Fq<P, N, M>,
    symbol = "*",
    apply = Mul::mul,
    identity = Fq::one(),
    inverse = |a| a.inverse(),
    inverse_symbol = "/"
)]
pub struct FqMul<const P: u64, const N: usize, M: IrreduciblePolynomial<P, N> = FirstIrreducible>(
    PhantomData<M>,
);

/// The quotient field `F_P[x] / (M)` of degree `N`.
pub struct FiniteField<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    pub fn modulus() -> UnivariatePolynomial<P> {
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
        UnivariatePolynomial::new(coefficients)
    }

    pub fn modulus_is_irreducible() -> bool {
        Self::modulus().is_irreducible()
    }

    pub fn generator() -> Fq<P, N, M> {
        Fq::from_polynomial(UnivariatePolynomial::x() % &Self::modulus())
    }

    pub fn evaluate_base_polynomial(
        polynomial: &UnivariatePolynomial<P>,
        value: Fq<P, N, M>,
    ) -> Fq<P, N, M> {
        polynomial
            .coefficients()
            .iter()
            .rev()
            .fold(Fq::zero(), |result, &coefficient| {
                result * value + Fq::from_constant(coefficient)
            })
    }

    pub fn roots_of_defining_polynomial() -> Vec<Fq<P, N, M>> {
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
    type Domain = Fq<P, N, M>;
    type Addition = FqAdd<P, N, M>;
    type Multiplication = FqMul<P, N, M>;
}

impl<const P: u64, const N: usize, M> Module for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Scalars = PrimeField<P>;
    type Domain = Fq<P, N, M>;
    type Addition = FqAdd<P, N, M>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        Fq::from_coefficients(value.coefficients.map(|coefficient| scalar * coefficient))
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
    fn roots() -> Vec<Fq<P, N, M>> {
        Self::roots_of_defining_polynomial()
    }
}

/// `F_(P^N)` whose power-basis generator is multiplicatively primitive.
pub type PrimitiveFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstPrimitive>;

/// A deterministic pseudo-Conway-style finite field.
pub type CompatibleFiniteField<const P: u64, const N: usize> = FiniteField<P, N, FirstCompatible>;

#[derive(Clone, Copy, Debug)]
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
        value: Fq<P, SOURCE_DEGREE, FirstCompatible>,
    ) -> Fq<P, TARGET_DEGREE, FirstCompatible> {
        self.map(value)
    }

    pub const fn generator_image(&self) -> Fq<P, TARGET_DEGREE, FirstCompatible> {
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
    Map<Fq<P, SOURCE_DEGREE, FirstCompatible>, Fq<P, TARGET_DEGREE, FirstCompatible>>
    for CompatibleFiniteFieldEmbedding<P, SOURCE_DEGREE, TARGET_DEGREE>
{
    fn map(
        &self,
        value: Fq<P, SOURCE_DEGREE, FirstCompatible>,
    ) -> Fq<P, TARGET_DEGREE, FirstCompatible> {
        value
            .coefficients
            .iter()
            .rev()
            .fold(Fq::zero(), |result, &coefficient| {
                result * self.generator_image + Fq::from_constant(coefficient)
            })
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
pub struct UnivariatePolynomial<const P: u64>(Vec<Fp<P>>);

impl<const P: u64> Set for UnivariatePolynomial<P> {}

impl<const P: u64> UnivariatePolynomial<P> {
    pub fn new(coefficients: Vec<Fp<P>>) -> Self {
        let mut polynomial = Self(coefficients);
        polynomial.trim();
        polynomial
    }

    pub fn zero() -> Self {
        Self(Vec::new())
    }

    pub fn one() -> Self {
        Self(vec![Fp::one()])
    }

    /// The indeterminate `x`.
    pub fn x() -> Self {
        Self(vec![Fp::zero(), Fp::one()])
    }

    pub fn coefficients(&self) -> &[Fp<P>] {
        &self.0
    }

    pub fn into_coefficients(self) -> Vec<Fp<P>> {
        self.0
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn trim(&mut self) {
        while self.0.last() == Some(&Fp::zero()) {
            self.0.pop();
        }
    }

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
        if !Fp::<P>::is_valid() || self.0.len() < 2 {
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

        if self.0.last() != Some(&Fp::one()) || !self.is_irreducible() {
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
            coefficients.push(coefficient.0.first().copied().unwrap_or(Fp::zero()));
        }
        Some(Self::new(coefficients))
    }

    fn div_rem(mut self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "division by the zero polynomial");
        if self.0.len() < divisor.0.len() {
            return (Self::zero(), self);
        }

        let mut quotient = vec![Fp::zero(); self.0.len() - divisor.0.len() + 1];
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
        self.0.resize(self.0.len().max(rhs.0.len()), Fp::zero());
        for (i, coefficient) in rhs.0.into_iter().enumerate() {
            self.0[i] = self.0[i] + coefficient;
        }
        Self::new(self.0)
    }
}

impl<const P: u64> Sub for UnivariatePolynomial<P> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self {
        self.0.resize(self.0.len().max(rhs.0.len()), Fp::zero());
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
        let mut product = vec![Fp::zero(); self.0.len() + rhs.0.len() - 1];
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
            return UnivariatePolynomial::new(coefficients.into_iter().map(Fp::new).collect());
        }

        assert!(degree > 0, "a field extension must have positive degree");
        const { Fp::<P>::assert_valid() };

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
    use eqn_algebra::field::{Field, SplittingField};
    use eqn_algebra::group::Subgroup;
    use eqn_algebra::monoid::Submonoid;
    use eqn_algebra::ring::ideal::Ideal;
    use eqn_algebra::ring::quotient::QuotientRing;
    use eqn_algebra::ring::{Ring, SemiRing};
    use eqn_core::quotient::{NormalForm, Quotient};
    use eqn_core::set::Subset;

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
        let expected = UnivariatePolynomial::new([1, 1, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<2, 2>::modulus(), expected);
        assert!(FiniteField::<2, 2>::modulus_is_irreducible());
        assert_eq!(
            FiniteField::<2, 2>::modulus(),
            FiniteField::<2, 2>::modulus()
        );

        let expected = UnivariatePolynomial::new([1, 1, 0, 1].map(Fp::new).to_vec());
        assert_eq!(FiniteField::<2, 3>::modulus(), expected);
        assert!(FiniteField::<2, 3>::modulus_is_irreducible());
    }

    #[test]
    fn primitive_modulus_gives_a_multiplicative_generator() {
        type F9 = PrimitiveFiniteField<3, 2>;
        type E = Fq<3, 2, FirstPrimitive>;

        let modulus = F9::modulus();
        let generator = E::from_values([0, 1]);
        assert!(modulus.is_primitive());
        assert_eq!(generator.pow(8), E::one());
        assert_ne!(generator.pow(4), E::one());

        let irreducible = UnivariatePolynomial::new([1, 0, 1].map(Fp::<3>::new).to_vec());
        assert!(irreducible.is_irreducible());
        assert!(!irreducible.is_primitive());
    }

    #[test]
    fn explicit_modulus_defines_multiplication() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = Fq<3, 2, X2PlusOne>;

        let alpha = E::from_values([0, 1]);
        assert_eq!(F9::multiply(alpha, alpha), E::from_values([2, 0]));
        assert!(F9::modulus_is_irreducible());
    }

    #[test]
    fn defining_polynomial_splits_into_frobenius_conjugates() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = Fq<3, 2, X2PlusOne>;

        let alpha = F9::generator();
        let roots = <F9 as SplittingField<X2PlusOne>>::roots();
        assert_eq!(roots, vec![alpha, alpha.pow(3)]);
        assert_ne!(roots[0], roots[1]);
        for root in roots {
            assert_eq!(
                F9::evaluate_base_polynomial(&F9::modulus(), root),
                E::zero()
            );
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
            Fq::zero()
        );
    }

    #[test]
    fn compatible_embedding_preserves_field_operations() {
        type F4 = CompatibleFiniteField<2, 2>;
        type F16 = CompatibleFiniteField<2, 4>;
        type E4 = Fq<2, 2, FirstCompatible>;
        type E16 = Fq<2, 4, FirstCompatible>;

        let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
        assert_eq!(embedding.embed(E4::zero()), E16::zero());
        assert_eq!(embedding.embed(E4::one()), E16::one());
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
        type E4 = Fq<2, 2, FirstCompatible>;

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
    fn every_nonzero_element_of_f4_is_invertible() {
        type F4 = FiniteField<2, 2>;
        type E = Fq<2, 2>;

        for a in 0..2 {
            for b in 0..2 {
                let value = E::from_values([a, b]);
                if value != E::zero() {
                    assert_eq!(F4::multiply(value, F4::invert(value)), F4::one());
                }
            }
        }
    }

    #[test]
    fn every_nonzero_element_of_explicit_f9_is_invertible() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = Fq<3, 2, X2PlusOne>;

        for a in 0..3 {
            for b in 0..3 {
                let value = E::from_values([a, b]);
                if value != E::zero() {
                    assert_eq!(F9::multiply(value, F9::invert(value)), F9::one());
                }
            }
        }
    }

    #[test]
    fn rejects_reducible_polynomials() {
        let reducible = UnivariatePolynomial::new([0, 1, 1].map(Fp::<2>::new).to_vec());
        assert!(!reducible.is_irreducible());
    }

    #[test]
    fn extension_arithmetic_satisfies_field_laws() {
        type F4 = FiniteField<2, 2>;
        type E = Fq<2, 2>;

        let elements: Vec<_> = (0..2)
            .flat_map(|a| (0..2).map(move |b| E::from_values([a, b])))
            .collect();

        for &a in &elements {
            assert_eq!(F4::add(a, F4::zero()), a);
            assert_eq!(F4::multiply(a, F4::one()), a);
            assert_eq!(F4::add(a, F4::negate(a)), F4::zero());
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

    // ================================================================================
    // The generic quotient F_3[x] / (M) against the hand-rolled F_9
    // ================================================================================

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = UnivariatePolynomial<P>, symbol = "+", apply = Add::add, identity = UnivariatePolynomial::zero(), inverse = Neg::neg, inverse_symbol = "-")]
    struct PolynomialAdd<const P: u64>;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = UnivariatePolynomial<P>, symbol = "*", apply = |a, b| &a * &b, identity = UnivariatePolynomial::one())]
    struct PolynomialMul<const P: u64>;

    type Polynomials<const P: u64> = (PolynomialAdd<P>, PolynomialMul<P>);

    /// The principal ideal generated by the defining polynomial of `F_9`.
    struct DefiningIdeal;

    impl DefiningIdeal {
        fn modulus() -> UnivariatePolynomial<3> {
            FiniteField::<3, 2>::modulus()
        }
    }

    impl Subset for DefiningIdeal {
        type Superset = UnivariatePolynomial<3>;

        fn contains(polynomial: &UnivariatePolynomial<3>) -> bool {
            (polynomial.clone() % &Self::modulus()).is_zero()
        }
    }

    impl Submonoid for DefiningIdeal {
        type Parent = (PolynomialAdd<3>,);
    }

    impl Subgroup for DefiningIdeal {}

    impl NormalForm<UnivariatePolynomial<3>> for DefiningIdeal {
        fn reduce(polynomial: UnivariatePolynomial<3>) -> UnivariatePolynomial<3> {
            polynomial % &Self::modulus()
        }
    }

    impl Ideal for DefiningIdeal {
        type Ring = Polynomials<3>;
    }

    #[test]
    fn the_quotient_by_the_defining_polynomial_is_the_finite_field() {
        type ModM = QuotientRing<DefiningIdeal>;
        type F9 = Fq<3, 2>;

        let class = |values: [u64; 2]| {
            Quotient::<UnivariatePolynomial<3>, DefiningIdeal>::new(UnivariatePolynomial::new(
                values.map(Fp::new).to_vec(),
            ))
        };
        let as_field = |class: Quotient<UnivariatePolynomial<3>, DefiningIdeal>| {
            F9::from_polynomial(class.into_representative())
        };
        let elements = || (0..9u64).map(|i| [i % 3, i / 3]);

        for a in elements() {
            assert_eq!(as_field(ModM::negate(class(a))), -F9::from_values(a));

            for b in elements() {
                assert_eq!(
                    as_field(ModM::add(class(a), class(b))),
                    F9::from_values(a) + F9::from_values(b)
                );
                assert_eq!(
                    as_field(ModM::multiply(class(a), class(b))),
                    F9::from_values(a) * F9::from_values(b)
                );
            }
        }

        assert_eq!(as_field(ModM::zero()), F9::zero());
        assert_eq!(as_field(ModM::one()), F9::one());
    }
}
