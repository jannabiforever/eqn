use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Sub};
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
        generated_polynomial::<P>(N, PolynomialSelection::Irreducible)
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstIrreducible {}

/// Selects the first primitive polynomial in base-`P` coefficient order.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstPrimitive;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstPrimitive {
    fn coefficients() -> Vec<PrimeFieldElement<P>> {
        generated_polynomial::<P>(N, PolynomialSelection::Primitive)
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstPrimitive {}

/// Selects a deterministic primitive polynomial compatible across divisor
/// degrees, following the pseudo-Conway construction.
#[derive(Clone, Copy, Debug, Default)]
pub struct FirstCompatible;

impl<const P: u64, const N: usize> DefiningPolynomial<P, N> for FirstCompatible {
    fn coefficients() -> Vec<PrimeFieldElement<P>> {
        generated_polynomial::<P>(N, PolynomialSelection::Compatible)
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
        let modulus = modulus::<P, N, M>();
        let mut remainder = self.coefficients.to_vec();
        trim(&mut remainder);
        assert!(!remainder.is_empty(), "zero has no multiplicative inverse");

        let mut old_r = modulus.clone();
        let mut r = remainder;
        let mut old_t = Vec::new();
        let mut t = vec![PrimeFieldElement::ONE];

        while !r.is_empty() {
            let (quotient, next_r) = poly_div_rem(old_r, r.clone());
            let next_t = poly_sub(old_t, poly_mul(&quotient, &t));
            old_r = r;
            r = next_r;
            old_t = t;
            t = next_t;
        }

        assert_eq!(old_r.len(), 1, "defining polynomial must be irreducible");
        let scale = old_r[0].inverse();
        let scaled = old_t
            .into_iter()
            .map(|coefficient| coefficient * scale)
            .collect();
        let (_, inverse) = poly_div_rem(scaled, modulus);
        element_from_poly(inverse)
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
        let modulus = modulus::<P, N, M>();
        let product = poly_mul(&self.coefficients, &rhs.coefficients);
        let (_, remainder) = poly_div_rem(product, modulus);
        element_from_poly(remainder)
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
    pub fn modulus() -> Vec<PrimeFieldElement<P>> {
        modulus::<P, N, M>()
    }

    pub fn modulus_is_irreducible() -> bool {
        is_irreducible(&Self::modulus())
    }

    pub fn generator() -> FiniteFieldElement<P, N, M> {
        let (_, generator) = poly_div_rem(
            vec![PrimeFieldElement::ZERO, PrimeFieldElement::ONE],
            Self::modulus(),
        );
        element_from_poly(generator)
    }

    pub fn evaluate_base_polynomial(
        polynomial: &[PrimeFieldElement<P>],
        value: FiniteFieldElement<P, N, M>,
    ) -> FiniteFieldElement<P, N, M> {
        polynomial
            .iter()
            .rev()
            .fold(FiniteFieldElement::ZERO, |result, &coefficient| {
                result * value + constant_element(coefficient)
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
        assert_compatible_degrees::<P, SOURCE_DEGREE, TARGET_DEGREE>();
        let source_order = field_order(P, SOURCE_DEGREE).expect("finite-field order is too large");
        let target_order = field_order(P, TARGET_DEGREE).expect("finite-field order is too large");
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
            |result, &coefficient| result * self.generator_image + constant_element(coefficient),
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

pub fn is_irreducible<const P: u64>(polynomial: &[PrimeFieldElement<P>]) -> bool {
    if !is_prime(P) {
        return false;
    }

    let mut polynomial = polynomial.to_vec();
    trim(&mut polynomial);
    if polynomial.len() < 2 {
        return false;
    }

    let degree = polynomial.len() - 1;
    for divisor_degree in 1..=degree / 2 {
        let mut lower = vec![0; divisor_degree];
        loop {
            let mut divisor: Vec<_> = lower.iter().copied().map(PrimeFieldElement::new).collect();
            divisor.push(PrimeFieldElement::ONE);
            if poly_div_rem(polynomial.clone(), divisor).1.is_empty() {
                return false;
            }
            if !increment(&mut lower, P) {
                break;
            }
        }
    }
    true
}

pub fn is_primitive<const P: u64>(polynomial: &[PrimeFieldElement<P>]) -> bool {
    let mut polynomial = polynomial.to_vec();
    trim(&mut polynomial);
    if polynomial.last() != Some(&PrimeFieldElement::ONE) || !is_irreducible(&polynomial) {
        return false;
    }

    let Some(order) = field_order(P, polynomial.len() - 1).map(|order| order - 1) else {
        return false;
    };
    let generator = poly_div_rem(
        vec![PrimeFieldElement::ZERO, PrimeFieldElement::ONE],
        polynomial.clone(),
    )
    .1;
    if generator.is_empty()
        || poly_pow_mod(generator.clone(), order, &polynomial) != vec![PrimeFieldElement::ONE]
    {
        return false;
    }

    prime_factors(order).into_iter().all(|factor| {
        poly_pow_mod(generator.clone(), order / factor, &polynomial) != vec![PrimeFieldElement::ONE]
    })
}

fn is_compatible<const P: u64>(polynomial: &[PrimeFieldElement<P>]) -> bool {
    if !is_primitive(polynomial) {
        return false;
    }

    let degree = polynomial.len() - 1;
    let order = field_order(P, degree).expect("finite-field order is too large");
    let generator = poly_div_rem(
        vec![PrimeFieldElement::ZERO, PrimeFieldElement::ONE],
        polynomial.to_vec(),
    )
    .1;

    (1..degree).filter(|d| degree.is_multiple_of(*d)).all(|d| {
        let subfield_order = field_order(P, d).unwrap();
        let subfield_generator = poly_pow_mod(
            generator.clone(),
            (order - 1) / (subfield_order - 1),
            polynomial,
        );
        minimal_polynomial(subfield_generator, d, polynomial)
            == Some(generated_polynomial::<P>(
                d,
                PolynomialSelection::Compatible,
            ))
    })
}

fn modulus<const P: u64, const N: usize, M>() -> Vec<PrimeFieldElement<P>>
where
    M: IrreduciblePolynomial<P, N>,
{
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
    coefficients
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum PolynomialSelection {
    Irreducible,
    Primitive,
    Compatible,
}

fn generated_polynomial<const P: u64>(
    degree: usize,
    selection: PolynomialSelection,
) -> Vec<PrimeFieldElement<P>> {
    static CACHE: OnceLock<Mutex<HashMap<(u64, usize, PolynomialSelection), Vec<u64>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));

    if let Some(coefficients) = cache.lock().unwrap().get(&(P, degree, selection)).cloned() {
        return coefficients
            .into_iter()
            .map(PrimeFieldElement::new)
            .collect();
    }

    assert!(degree > 0, "a field extension must have positive degree");
    assert!(is_prime(P), "finite-field characteristic must be prime");

    let mut lower = vec![0; degree];
    let polynomial = loop {
        let mut candidate: Vec<_> = lower.iter().copied().map(PrimeFieldElement::new).collect();
        candidate.push(PrimeFieldElement::ONE);
        let matches = match selection {
            PolynomialSelection::Irreducible => is_irreducible(&candidate),
            PolynomialSelection::Primitive => is_primitive(&candidate),
            PolynomialSelection::Compatible => is_compatible(&candidate),
        };
        if matches {
            break candidate;
        }
        assert!(increment(&mut lower, P), "no defining polynomial found");
    };

    cache.lock().unwrap().insert(
        (P, degree, selection),
        polynomial
            .iter()
            .map(|coefficient| coefficient.value())
            .collect(),
    );
    polynomial
}

fn poly_pow_mod<const P: u64>(
    mut base: Vec<PrimeFieldElement<P>>,
    mut exponent: u128,
    modulus: &[PrimeFieldElement<P>],
) -> Vec<PrimeFieldElement<P>> {
    let mut result = vec![PrimeFieldElement::ONE];
    while exponent > 0 {
        if exponent & 1 == 1 {
            result = poly_div_rem(poly_mul(&result, &base), modulus.to_vec()).1;
        }
        exponent >>= 1;
        if exponent > 0 {
            base = poly_div_rem(poly_mul(&base, &base), modulus.to_vec()).1;
        }
    }
    result
}

fn field_order(characteristic: u64, degree: usize) -> Option<u128> {
    let mut order = 1u128;
    for _ in 0..degree {
        order = order.checked_mul(u128::from(characteristic))?;
    }
    Some(order)
}

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

fn minimal_polynomial<const P: u64>(
    element: Vec<PrimeFieldElement<P>>,
    degree: usize,
    modulus: &[PrimeFieldElement<P>],
) -> Option<Vec<PrimeFieldElement<P>>> {
    let mut polynomial = vec![vec![PrimeFieldElement::ONE]];
    let mut conjugate = element;

    for _ in 0..degree {
        let mut product = vec![Vec::new(); polynomial.len() + 1];
        for (i, coefficient) in polynomial.into_iter().enumerate() {
            let constant = quotient_mul(&coefficient, &quotient_neg(conjugate.clone()), modulus);
            product[i] = quotient_add(product[i].clone(), constant);
            product[i + 1] = quotient_add(product[i + 1].clone(), coefficient);
        }
        polynomial = product;
        conjugate = poly_pow_mod(conjugate, u128::from(P), modulus);
    }

    let mut coefficients = Vec::with_capacity(polynomial.len());
    for mut coefficient in polynomial {
        trim(&mut coefficient);
        if coefficient.len() > 1 {
            return None;
        }
        coefficients.push(
            coefficient
                .first()
                .copied()
                .unwrap_or(PrimeFieldElement::ZERO),
        );
    }
    trim(&mut coefficients);
    Some(coefficients)
}

fn quotient_add<const P: u64>(
    mut lhs: Vec<PrimeFieldElement<P>>,
    rhs: Vec<PrimeFieldElement<P>>,
) -> Vec<PrimeFieldElement<P>> {
    lhs.resize(lhs.len().max(rhs.len()), PrimeFieldElement::ZERO);
    for (i, coefficient) in rhs.into_iter().enumerate() {
        lhs[i] = lhs[i] + coefficient;
    }
    trim(&mut lhs);
    lhs
}

fn quotient_neg<const P: u64>(mut value: Vec<PrimeFieldElement<P>>) -> Vec<PrimeFieldElement<P>> {
    value
        .iter_mut()
        .for_each(|coefficient| *coefficient = -*coefficient);
    trim(&mut value);
    value
}

fn quotient_mul<const P: u64>(
    lhs: &[PrimeFieldElement<P>],
    rhs: &[PrimeFieldElement<P>],
    modulus: &[PrimeFieldElement<P>],
) -> Vec<PrimeFieldElement<P>> {
    poly_div_rem(poly_mul(lhs, rhs), modulus.to_vec()).1
}

fn assert_compatible_degrees<
    const P: u64,
    const SOURCE_DEGREE: usize,
    const TARGET_DEGREE: usize,
>() {
    assert!(
        PrimeField::<P>::is_valid(),
        "finite-field characteristic must be prime"
    );
    assert!(
        SOURCE_DEGREE > 0 && TARGET_DEGREE > 0 && TARGET_DEGREE.is_multiple_of(SOURCE_DEGREE),
        "source degree must divide target degree"
    );
}

fn constant_element<const P: u64, const N: usize, M>(
    value: PrimeFieldElement<P>,
) -> FiniteFieldElement<P, N, M> {
    let mut coefficients = [PrimeFieldElement::ZERO; N];
    assert!(N > 0, "a field extension must have positive degree");
    coefficients[0] = value;
    FiniteFieldElement::from_coefficients(coefficients)
}

fn element_from_poly<const P: u64, const N: usize, M>(
    polynomial: Vec<PrimeFieldElement<P>>,
) -> FiniteFieldElement<P, N, M> {
    let mut coefficients = [PrimeFieldElement::ZERO; N];
    for (target, coefficient) in coefficients.iter_mut().zip(polynomial) {
        *target = coefficient;
    }
    FiniteFieldElement::from_coefficients(coefficients)
}

fn poly_sub<const P: u64>(
    mut lhs: Vec<PrimeFieldElement<P>>,
    rhs: Vec<PrimeFieldElement<P>>,
) -> Vec<PrimeFieldElement<P>> {
    lhs.resize(rhs.len().max(lhs.len()), PrimeFieldElement::ZERO);
    for (i, coefficient) in rhs.into_iter().enumerate() {
        lhs[i] = lhs[i] - coefficient;
    }
    trim(&mut lhs);
    lhs
}

fn poly_mul<const P: u64>(
    lhs: &[PrimeFieldElement<P>],
    rhs: &[PrimeFieldElement<P>],
) -> Vec<PrimeFieldElement<P>> {
    if lhs.is_empty() || rhs.is_empty() {
        return Vec::new();
    }

    let mut product = vec![PrimeFieldElement::ZERO; lhs.len() + rhs.len() - 1];
    for (i, &a) in lhs.iter().enumerate() {
        for (j, &b) in rhs.iter().enumerate() {
            product[i + j] = product[i + j] + a * b;
        }
    }
    trim(&mut product);
    product
}

fn poly_div_rem<const P: u64>(
    mut dividend: Vec<PrimeFieldElement<P>>,
    mut divisor: Vec<PrimeFieldElement<P>>,
) -> (Vec<PrimeFieldElement<P>>, Vec<PrimeFieldElement<P>>) {
    trim(&mut dividend);
    trim(&mut divisor);
    assert!(!divisor.is_empty(), "division by the zero polynomial");

    if dividend.len() < divisor.len() {
        return (Vec::new(), dividend);
    }

    let mut quotient = vec![PrimeFieldElement::ZERO; dividend.len() - divisor.len() + 1];
    let leading_inverse = divisor.last().copied().unwrap().inverse();
    while dividend.len() >= divisor.len() {
        let shift = dividend.len() - divisor.len();
        let coefficient = dividend.last().copied().unwrap() * leading_inverse;
        quotient[shift] = coefficient;
        for (i, &divisor_coefficient) in divisor.iter().enumerate() {
            dividend[i + shift] = dividend[i + shift] - coefficient * divisor_coefficient;
        }
        trim(&mut dividend);
    }
    trim(&mut quotient);
    (quotient, dividend)
}

fn trim<const P: u64>(polynomial: &mut Vec<PrimeFieldElement<P>>) {
    while polynomial.last() == Some(&PrimeFieldElement::ZERO) {
        polynomial.pop();
    }
}

fn increment(digits: &mut [u64], base: u64) -> bool {
    for digit in digits {
        *digit += 1;
        if *digit < base {
            return true;
        }
        *digit = 0;
    }
    false
}

const fn is_prime(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    let mut divisor = 2;
    while divisor <= value / divisor {
        if value.is_multiple_of(divisor) {
            return false;
        }
        divisor += 1;
    }
    true
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
        let expected = [1, 1, 1].map(PrimeFieldElement::new).to_vec();
        assert_eq!(Fq::<2, 2>::modulus(), expected);
        assert!(Fq::<2, 2>::modulus_is_irreducible());
        assert_eq!(Fq::<2, 2>::modulus(), Fq::<2, 2>::modulus());

        let expected = [1, 1, 0, 1].map(PrimeFieldElement::new).to_vec();
        assert_eq!(Fq::<2, 3>::modulus(), expected);
        assert!(Fq::<2, 3>::modulus_is_irreducible());
    }

    #[test]
    fn primitive_modulus_gives_a_multiplicative_generator() {
        type F9 = PrimitiveFiniteField<3, 2>;
        type E = PrimitiveFiniteFieldElement<3, 2>;

        let modulus = F9::modulus();
        let generator = E::from_values([0, 1]);
        assert!(is_primitive(&modulus));
        assert_eq!(generator.pow(8), E::ONE);
        assert_ne!(generator.pow(4), E::ONE);

        let irreducible = [1, 0, 1].map(PrimeFieldElement::<3>::new);
        assert!(is_irreducible(&irreducible));
        assert!(!is_primitive(&irreducible));
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
        let reducible = [0, 1, 1].map(PrimeFieldElement::<2>::new);
        assert!(!is_irreducible(&reducible));
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
