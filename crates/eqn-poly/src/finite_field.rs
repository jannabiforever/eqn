use std::collections::HashMap;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::sync::{Mutex, OnceLock};

use eqn_algebra::field::{FieldExtension, FiniteExtension, PrimeField, PrimeFieldElement};
use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::SemiRing;
use eqn_core::op::{Associative, BinaryOperator, Commutative, Identity, Inverse};
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
        generated_modulus::<P>(N)
    }
}

impl<const P: u64, const N: usize> IrreduciblePolynomial<P, N> for FirstIrreducible {}

/// A canonical power-basis representative of a finite-field element.
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
}

impl<const P: u64, const N: usize, M> Copy for FiniteFieldElement<P, N, M> {}

impl<const P: u64, const N: usize, M> Clone for FiniteFieldElement<P, N, M> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<const P: u64, const N: usize, M> fmt::Debug for FiniteFieldElement<P, N, M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("FiniteFieldElement")
            .field(&self.coefficients)
            .finish()
    }
}

impl<const P: u64, const N: usize, M> PartialEq for FiniteFieldElement<P, N, M> {
    fn eq(&self, other: &Self) -> bool {
        self.coefficients == other.coefficients
    }
}

impl<const P: u64, const N: usize, M> Eq for FiniteFieldElement<P, N, M> {}

pub struct FiniteFieldElements<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> Set for FiniteFieldElements<P, N, M> {
    type Element = FiniteFieldElement<P, N, M>;
}

pub struct FiniteFieldAdd<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> BinaryOperator for FiniteFieldAdd<P, N, M> {
    type Domain = FiniteFieldElements<P, N, M>;

    fn apply(
        lhs: FiniteFieldElement<P, N, M>,
        rhs: FiniteFieldElement<P, N, M>,
    ) -> FiniteFieldElement<P, N, M> {
        FiniteFieldElement::from_coefficients(std::array::from_fn(|i| {
            lhs.coefficients[i] + rhs.coefficients[i]
        }))
    }
}

impl<const P: u64, const N: usize, M> Associative for FiniteFieldAdd<P, N, M> {}
impl<const P: u64, const N: usize, M> Commutative for FiniteFieldAdd<P, N, M> {}

impl<const P: u64, const N: usize, M> Identity for FiniteFieldAdd<P, N, M> {
    const IDENTITY: FiniteFieldElement<P, N, M> = FiniteFieldElement::ZERO;
}

impl<const P: u64, const N: usize, M> Inverse for FiniteFieldAdd<P, N, M> {
    fn inverse(value: FiniteFieldElement<P, N, M>) -> FiniteFieldElement<P, N, M> {
        FiniteFieldElement::from_coefficients(value.coefficients.map(Neg::neg))
    }
}

pub struct FiniteFieldMul<const P: u64, const N: usize, M = FirstIrreducible>(PhantomData<M>);

impl<const P: u64, const N: usize, M> BinaryOperator for FiniteFieldMul<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Domain = FiniteFieldElements<P, N, M>;

    fn apply(
        lhs: FiniteFieldElement<P, N, M>,
        rhs: FiniteFieldElement<P, N, M>,
    ) -> FiniteFieldElement<P, N, M> {
        let modulus = modulus::<P, N, M>();
        let product = poly_mul(&lhs.coefficients, &rhs.coefficients);
        let (_, remainder) = poly_div_rem(product, modulus);
        element_from_poly(remainder)
    }
}

impl<const P: u64, const N: usize, M> Associative for FiniteFieldMul<P, N, M> where
    M: IrreduciblePolynomial<P, N>
{
}

impl<const P: u64, const N: usize, M> Commutative for FiniteFieldMul<P, N, M> where
    M: IrreduciblePolynomial<P, N>
{
}

impl<const P: u64, const N: usize, M> Identity for FiniteFieldMul<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    const IDENTITY: FiniteFieldElement<P, N, M> = FiniteFieldElement::ONE;
}

impl<const P: u64, const N: usize, M> Inverse for FiniteFieldMul<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    fn inverse(value: FiniteFieldElement<P, N, M>) -> FiniteFieldElement<P, N, M> {
        let modulus = modulus::<P, N, M>();
        let mut remainder = value.coefficients.to_vec();
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
    const DEGREE: usize = N;
}

impl<const P: u64, const N: usize, M> Add for FiniteFieldElement<P, N, M> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        FiniteFieldAdd::apply(self, rhs)
    }
}

impl<const P: u64, const N: usize, M> Neg for FiniteFieldElement<P, N, M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        FiniteFieldAdd::inverse(self)
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
        FiniteFieldMul::apply(self, rhs)
    }
}

impl<const P: u64, const N: usize, M> Div for FiniteFieldElement<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        FiniteFieldMul::apply(self, FiniteFieldMul::inverse(rhs))
    }
}

/// `F_(P^N)` using the deterministic default defining polynomial.
pub type Fq<const P: u64, const N: usize> = FiniteField<P, N, FirstIrreducible>;
pub type FqElement<const P: u64, const N: usize> = FiniteFieldElement<P, N, FirstIrreducible>;

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

fn generated_modulus<const P: u64>(degree: usize) -> Vec<PrimeFieldElement<P>> {
    static CACHE: OnceLock<Mutex<HashMap<(u64, usize), Vec<u64>>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));

    if let Some(coefficients) = cache.lock().unwrap().get(&(P, degree)).cloned() {
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
        if is_irreducible(&candidate) {
            break candidate;
        }
        assert!(increment(&mut lower, P), "no irreducible polynomial found");
    };

    cache.lock().unwrap().insert(
        (P, degree),
        polynomial
            .iter()
            .map(|coefficient| coefficient.value())
            .collect(),
    );
    polynomial
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
    use eqn_algebra::field::{AlgebraicExtension, Field};
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
    fn explicit_modulus_defines_multiplication() {
        type F9 = FiniteField<3, 2, X2PlusOne>;
        type E = FiniteFieldElement<3, 2, X2PlusOne>;

        let alpha = E::from_values([0, 1]);
        assert_eq!(F9::multiply(alpha, alpha), E::from_values([2, 0]));
        assert!(F9::modulus_is_irreducible());
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
        fn assert_extension<E: FieldExtension + FiniteExtension + AlgebraicExtension>() {}

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
