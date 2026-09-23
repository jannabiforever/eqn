use std::marker::PhantomData;

use eqn_algebra::field::Field;
use eqn_algebra::ring::RingElem;

use super::{FactorizationError, FiniteFactorField};

#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct DensePolynomial<F: Field> {
    coefficients: Vec<RingElem<F>>,
    #[derive_where(skip)]
    field: PhantomData<F>,
}

#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct DenseFactor<F: Field> {
    pub(super) polynomial: DensePolynomial<F>,
    pub(super) multiplicity: usize,
}

pub(super) type PolynomialFactor<F> = DenseFactor<F>;

#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct DenseFactorization<F: Field> {
    pub(super) unit: RingElem<F>,
    pub(super) factors: Vec<DenseFactor<F>>,
}

impl<F: Field> DenseFactorization<F> {
    #[cfg(test)]
    pub(super) fn recompose(&self) -> DensePolynomial<F> {
        let mut product = DensePolynomial::constant(self.unit.clone());
        for factor in &self.factors {
            for _ in 0..factor.multiplicity {
                product = product.mul(&factor.polynomial);
            }
        }
        product
    }
}

impl<F: Field> DensePolynomial<F> {
    pub(super) fn new(mut coefficients: Vec<RingElem<F>>) -> Self {
        Self::trim_coefficients(&mut coefficients);
        Self {
            coefficients,
            field: PhantomData,
        }
    }

    pub(super) fn zero() -> Self {
        Self::new(Vec::new())
    }

    pub(super) fn one() -> Self {
        Self::constant(F::ONE)
    }

    pub(super) fn variable() -> Self {
        Self::new(vec![F::ZERO, F::ONE])
    }

    pub(super) fn constant(value: RingElem<F>) -> Self {
        Self::new(vec![value])
    }

    pub(super) fn from_coefficients(coefficients: impl Into<Vec<RingElem<F>>>) -> Self {
        Self::new(coefficients.into())
    }

    pub(super) fn coefficients(&self) -> &[RingElem<F>] {
        &self.coefficients
    }

    pub(super) fn degree(&self) -> Option<usize> {
        self.coefficients.len().checked_sub(1)
    }

    pub(super) fn leading_coefficient(&self) -> Option<RingElem<F>> {
        self.coefficients.last().cloned()
    }

    pub(super) fn is_zero(&self) -> bool {
        self.coefficients.is_empty()
    }

    pub(super) fn is_one(&self) -> bool {
        self.coefficients == [F::ONE]
    }

    pub(super) fn is_constant(&self) -> bool {
        self.coefficients.len() <= 1
    }

    pub(super) fn add(&self, rhs: &Self) -> Self {
        let len = self.coefficients.len().max(rhs.coefficients.len());
        let coefficients = (0..len)
            .map(|i| {
                F::add(
                    self.coefficients.get(i).cloned().unwrap_or(F::ZERO),
                    rhs.coefficients.get(i).cloned().unwrap_or(F::ZERO),
                )
            })
            .collect();
        Self::new(coefficients)
    }

    pub(super) fn neg(&self) -> Self {
        Self::new(self.coefficients.iter().cloned().map(F::negate).collect())
    }

    pub(super) fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.neg())
    }

    pub(super) fn mul(&self, rhs: &Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        let mut product = vec![F::ZERO; self.coefficients.len() + rhs.coefficients.len() - 1];
        for (i, a) in self.coefficients.iter().cloned().enumerate() {
            for (j, b) in rhs.coefficients.iter().cloned().enumerate() {
                product[i + j] = F::add(product[i + j].clone(), F::multiply(a.clone(), b));
            }
        }
        Self::new(product)
    }

    pub(super) fn scale(&self, scalar: RingElem<F>) -> Self {
        if scalar == F::ZERO {
            return Self::zero();
        }
        Self::new(
            self.coefficients
                .iter()
                .cloned()
                .map(|coefficient| F::multiply(scalar.clone(), coefficient))
                .collect(),
        )
    }

    pub(super) fn div_rem(&self, divisor: &Self) -> Result<(Self, Self), FactorizationError> {
        if divisor.is_zero() {
            return Err(FactorizationError::DivisionByZero);
        }

        if self.degree() < divisor.degree() {
            return Ok((Self::zero(), self.clone()));
        }

        let mut remainder = self.coefficients.clone();
        let mut quotient = vec![F::ZERO; remainder.len() - divisor.coefficients.len() + 1];
        let leading_inverse = F::invert(divisor.leading_coefficient().unwrap());
        while remainder.len() >= divisor.coefficients.len() && !remainder.is_empty() {
            let shift = remainder.len() - divisor.coefficients.len();
            let coefficient =
                F::multiply(remainder.last().cloned().unwrap(), leading_inverse.clone());
            quotient[shift] = coefficient.clone();
            for (i, divisor_coefficient) in divisor.coefficients.iter().cloned().enumerate() {
                let product = F::multiply(coefficient.clone(), divisor_coefficient);
                remainder[i + shift] = F::add(remainder[i + shift].clone(), F::negate(product));
            }
            Self::trim_coefficients(&mut remainder);
        }
        Ok((Self::new(quotient), Self::new(remainder)))
    }

    pub(super) fn div_exact(&self, divisor: &Self) -> Result<Self, FactorizationError> {
        let (quotient, remainder) = self.div_rem(divisor)?;
        if remainder.is_zero() {
            Ok(quotient)
        } else {
            Err(FactorizationError::InexactDivision)
        }
    }

    pub(super) fn rem(&self, divisor: &Self) -> Result<Self, FactorizationError> {
        Ok(self.div_rem(divisor)?.1)
    }

    pub(super) fn gcd(&self, rhs: &Self) -> Result<Self, FactorizationError> {
        let mut a = self.clone();
        let mut b = rhs.clone();
        while !b.is_zero() {
            let r = a.rem(&b)?;
            a = b;
            b = r;
        }
        Ok(a.monic())
    }

    pub(super) fn derivative(&self) -> Self {
        if self.coefficients.len() <= 1 {
            return Self::zero();
        }
        let coefficients = self
            .coefficients
            .iter()
            .cloned()
            .enumerate()
            .skip(1)
            .map(|(degree, coefficient)| F::multiply(F::from_usize(degree), coefficient))
            .collect();
        Self::new(coefficients)
    }

    pub(super) fn monic(&self) -> Self {
        match self.leading_coefficient() {
            Some(leading) => self.scale(F::invert(leading)),
            None => Self::zero(),
        }
    }

    pub(super) fn pow_mod(
        &self,
        mut exponent: u128,
        modulus: &Self,
    ) -> Result<Self, FactorizationError> {
        let mut result = Self::one().rem(modulus)?;
        let mut base = self.rem(modulus)?;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = result.mul(&base).rem(modulus)?;
            }
            exponent >>= 1;
            if exponent > 0 {
                base = base.mul(&base).rem(modulus)?;
            }
        }
        Ok(result)
    }

    fn trim_coefficients(coefficients: &mut Vec<RingElem<F>>) {
        while coefficients.last() == Some(&F::ZERO) {
            coefficients.pop();
        }
    }
}

impl<F: FiniteFactorField> DensePolynomial<F> {
    pub(super) fn factor(&self) -> Result<DenseFactorization<F>, FactorizationError> {
        let square_free = self.square_free_factorization()?;
        let mut factors = Vec::new();
        for factor in square_free.factors {
            for irreducible in factor.polynomial.factor_square_free()? {
                factors.push(DenseFactor {
                    polynomial: irreducible,
                    multiplicity: factor.multiplicity,
                });
            }
        }
        Self::sort_factors(&mut factors);
        Ok(DenseFactorization {
            unit: square_free.unit,
            factors,
        })
    }

    pub(super) fn square_free_factorization(
        &self,
    ) -> Result<DenseFactorization<F>, FactorizationError> {
        if self.is_zero() {
            return Err(FactorizationError::ZeroPolynomial);
        }

        let unit = self.leading_coefficient().unwrap_or(F::ONE);
        let factors = self.monic().square_free_part(1)?;
        Ok(DenseFactorization { unit, factors })
    }

    fn square_free_part(
        &self,
        multiplicity_scale: usize,
    ) -> Result<Vec<DenseFactor<F>>, FactorizationError> {
        if self.is_constant() {
            return Ok(Vec::new());
        }

        let derivative = self.derivative();
        if derivative.is_zero() {
            let characteristic = Self::positive_characteristic()?;
            let scale = multiplicity_scale
                .checked_mul(characteristic)
                .ok_or(FactorizationError::MultiplicityOverflow)?;
            return self.pth_root_polynomial()?.square_free_part(scale);
        }

        let mut factors = Vec::new();
        let mut c = self.gcd(&derivative)?;
        let mut w = self.div_exact(&c)?;
        let mut i = 1usize;
        while !w.is_one() {
            let y = w.gcd(&c)?;
            let z = w.div_exact(&y)?;
            Self::push_factor(
                &mut factors,
                z,
                multiplicity_scale
                    .checked_mul(i)
                    .ok_or(FactorizationError::MultiplicityOverflow)?,
            );
            w = y;
            c = c.div_exact(&w)?;
            i = i
                .checked_add(1)
                .ok_or(FactorizationError::MultiplicityOverflow)?;
        }

        if !c.is_one() {
            let characteristic = Self::positive_characteristic()?;
            let scale = multiplicity_scale
                .checked_mul(characteristic)
                .ok_or(FactorizationError::MultiplicityOverflow)?;
            factors.extend(c.pth_root_polynomial()?.square_free_part(scale)?);
        }
        Ok(factors)
    }

    fn factor_square_free(&self) -> Result<Vec<Self>, FactorizationError> {
        let mut factors = Vec::new();
        for (degree, factor) in self.distinct_degree_factorization()? {
            factors.extend(factor.equal_degree_factorization(degree)?);
        }
        Ok(factors)
    }

    fn distinct_degree_factorization(&self) -> Result<Vec<(usize, Self)>, FactorizationError> {
        let mut factors = Vec::new();
        let mut remaining = self.monic();
        let x = Self::variable();
        let mut h = x.clone();
        let mut degree = 1usize;
        let order = F::order()?;

        while remaining.degree().unwrap_or(0) >= 2 * degree {
            h = h.pow_mod(order, &remaining)?;
            let g = h.sub(&x).gcd(&remaining)?;
            if !g.is_one() {
                factors.push((degree, g.clone()));
                remaining = remaining.div_exact(&g)?;
                if remaining.is_one() {
                    return Ok(factors);
                }
                h = h.rem(&remaining)?;
            }
            degree += 1;
        }

        if !remaining.is_one() {
            let degree = remaining.degree().unwrap_or(1);
            factors.push((degree, remaining));
        }
        Ok(factors)
    }

    fn equal_degree_factorization(&self, degree: usize) -> Result<Vec<Self>, FactorizationError> {
        if self.degree().unwrap_or(0) == degree {
            return Ok(vec![self.monic()]);
        }

        let mut factors = vec![self.monic()];
        let seed_count = self.seed_count()?;
        for index in 0..seed_count {
            let seed = self.seed(index)?;
            let mut next = Vec::new();
            for factor in factors {
                if factor.degree().unwrap_or(0) == degree {
                    next.push(factor);
                    continue;
                }

                let split = if F::CHARACTERISTIC == 2 {
                    factor.cantor_zassenhaus_even_split(&seed, degree)?
                } else {
                    factor.cantor_zassenhaus_odd_split(&seed, degree)?
                };
                match split {
                    Some((a, b)) => {
                        next.push(a);
                        next.push(b);
                    }
                    None => next.push(factor),
                }
            }
            factors = next;
            Self::sort_polynomials(&mut factors);
            if factors
                .iter()
                .all(|factor| factor.degree().unwrap_or(0) == degree)
            {
                return Ok(factors.into_iter().map(|factor| factor.monic()).collect());
            }
        }

        Err(FactorizationError::DeterministicSplittingExhausted)
    }

    fn cantor_zassenhaus_odd_split(
        &self,
        seed: &Self,
        degree: usize,
    ) -> Result<Option<(Self, Self)>, FactorizationError> {
        let exponent = Self::odd_cantor_zassenhaus_exponent(degree)?;
        let candidate = seed.pow_mod(exponent, self)?.sub(&Self::one());
        self.nontrivial_split(&candidate)
    }

    fn cantor_zassenhaus_even_split(
        &self,
        seed: &Self,
        degree: usize,
    ) -> Result<Option<(Self, Self)>, FactorizationError> {
        let mut trace = Self::zero();
        let mut h = seed.rem(self)?;
        let order = F::order()?;
        for _ in 0..degree {
            trace = trace.add(&h);
            h = h.pow_mod(order, self)?;
        }
        self.nontrivial_split(&trace)
    }

    fn nontrivial_split(
        &self,
        candidate: &Self,
    ) -> Result<Option<(Self, Self)>, FactorizationError> {
        let g = candidate.gcd(self)?;
        if g.is_one() || g == *self {
            Ok(None)
        } else {
            let quotient = self.div_exact(&g)?;
            Ok(Some((g.monic(), quotient.monic())))
        }
    }

    fn seed_count(&self) -> Result<u128, FactorizationError> {
        let degree = self.degree().unwrap_or(0);
        F::order()?
            .checked_pow(u32::try_from(degree).map_err(|_| FactorizationError::FieldOrderOverflow)?)
            .ok_or(FactorizationError::FieldOrderOverflow)
    }

    fn seed(&self, mut index: u128) -> Result<Self, FactorizationError> {
        let degree = self.degree().unwrap_or(0);
        let order = F::order()?;
        let mut coefficients = Vec::with_capacity(degree);
        for _ in 0..degree {
            coefficients.push(F::element(index % order)?);
            index /= order;
        }
        Ok(Self::new(coefficients))
    }

    fn odd_cantor_zassenhaus_exponent(degree: usize) -> Result<u128, FactorizationError> {
        let order = F::order()?;
        let half = (order - 1) / 2;
        let mut exponent = 0u128;
        for _ in 0..degree {
            exponent = exponent
                .checked_mul(order)
                .and_then(|value| value.checked_add(half))
                .ok_or(FactorizationError::FieldOrderOverflow)?;
        }
        Ok(exponent)
    }

    fn pth_root_polynomial(&self) -> Result<Self, FactorizationError> {
        let characteristic = Self::positive_characteristic()?;
        let mut coefficients = Vec::new();
        for (degree, coefficient) in self.coefficients.iter().cloned().enumerate() {
            if degree % characteristic == 0 {
                coefficients.push(F::pth_root(coefficient));
            } else if coefficient != F::ZERO {
                return Err(FactorizationError::NonPositiveCharacteristic);
            }
        }
        Ok(Self::new(coefficients))
    }

    fn positive_characteristic() -> Result<usize, FactorizationError> {
        if F::CHARACTERISTIC == 0 {
            return Err(FactorizationError::NonPositiveCharacteristic);
        }
        usize::try_from(F::CHARACTERISTIC).map_err(|_| FactorizationError::FieldOrderOverflow)
    }

    fn push_factor(factors: &mut Vec<DenseFactor<F>>, polynomial: Self, multiplicity: usize) {
        if !polynomial.is_constant() {
            factors.push(DenseFactor {
                polynomial: polynomial.monic(),
                multiplicity,
            });
        }
    }

    fn sort_factors(factors: &mut [DenseFactor<F>]) {
        factors.sort_by(|a, b| {
            a.polynomial
                .sort_key()
                .cmp(&b.polynomial.sort_key())
                .then(a.multiplicity.cmp(&b.multiplicity))
        });
    }

    fn sort_polynomials(factors: &mut [Self]) {
        factors.sort_by_key(Self::sort_key);
    }

    fn sort_key(&self) -> (usize, String) {
        (
            self.degree().unwrap_or(0),
            format!("{:?}", self.coefficients()),
        )
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{PrimeField, PrimeFieldElement};

    use super::*;
    use crate::finite_field::{Fq, FqElement, UnivariatePolynomial};

    type F2 = PrimeField<2>;
    type F5 = PrimeField<5>;
    type E3 = PrimeFieldElement<3>;
    type E5 = PrimeFieldElement<5>;

    struct TestPolynomial;

    impl TestPolynomial {
        fn fp<const P: u64>(values: &[u64]) -> DensePolynomial<PrimeField<P>> {
            DensePolynomial::new(values.iter().copied().map(PrimeFieldElement::new).collect())
        }

        fn factor_coefficients<const P: u64>(
            factorization: &DenseFactorization<PrimeField<P>>,
        ) -> Vec<Vec<u64>> {
            factorization
                .factors
                .iter()
                .map(|factor| {
                    factor
                        .polynomial
                        .coefficients()
                        .iter()
                        .map(|coefficient| coefficient.value())
                        .collect()
                })
                .collect()
        }

        fn assert_all_monic_factorizations<const P: u64>(maximum_degree: usize) {
            for degree in 1..=maximum_degree {
                let count = P.pow(u32::try_from(degree).unwrap());
                for mut encoded in 0..count {
                    let mut coefficients: Vec<PrimeFieldElement<P>> =
                        Vec::with_capacity(degree + 1);
                    for _ in 0..degree {
                        coefficients.push(PrimeFieldElement::new(encoded % P));
                        encoded /= P;
                    }
                    coefficients.push(PrimeFieldElement::ONE);
                    let polynomial = DensePolynomial::<PrimeField<P>>::new(coefficients);
                    let factorization = polynomial.factor().unwrap();

                    assert_eq!(factorization.recompose(), polynomial);
                    assert!(factorization.factors.iter().all(|factor| {
                        UnivariatePolynomial::new(factor.polynomial.coefficients().to_vec())
                            .is_irreducible()
                    }));
                }
            }
        }
    }

    #[test]
    fn finite_factorization_rejects_the_zero_polynomial() {
        assert_eq!(
            DensePolynomial::<F2>::zero().factor(),
            Err(FactorizationError::ZeroPolynomial)
        );
    }

    #[test]
    fn finite_factorization_keeps_nonzero_constants_as_units() {
        let polynomial = DensePolynomial::<F5>::constant(E5::new(3));
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.unit, E5::new(3));
        assert!(factorization.factors.is_empty());
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn euclidean_division_reconstructs_the_dividend() {
        let dividend = TestPolynomial::fp::<5>(&[1, 0, 4, 1]);
        let divisor = TestPolynomial::fp::<5>(&[1, 1]);
        let (quotient, remainder) = dividend.div_rem(&divisor).unwrap();

        assert_eq!(quotient.mul(&divisor).add(&remainder), dividend);
        assert!(remainder.degree() < divisor.degree());
    }

    #[test]
    fn modular_power_reduces_the_zero_exponent() {
        let polynomial = TestPolynomial::fp::<5>(&[2, 1]);

        assert_eq!(
            polynomial.pow_mod(0, &DensePolynomial::one()).unwrap(),
            DensePolynomial::zero()
        );
    }

    #[test]
    fn prime_field_factorization_splits_linear_factors_over_five_elements() {
        let polynomial = TestPolynomial::fp::<5>(&[0, 4, 1, 4, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.unit, E5::ONE);
        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 4);
    }

    #[test]
    fn prime_field_factorization_splits_quadratics_over_three_elements() {
        let polynomial = TestPolynomial::fp::<3>(&[2, 0, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(
            TestPolynomial::factor_coefficients(&factorization),
            vec![vec![1, 1], vec![2, 1]]
        );
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn irreducible_polynomial_remains_one_factor() {
        let polynomial = TestPolynomial::fp::<2>(&[1, 1, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].polynomial, polynomial);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn square_free_factorization_records_repeated_factors() {
        let linear = TestPolynomial::fp::<3>(&[1, 1]);
        let polynomial = linear.mul(&linear).mul(&TestPolynomial::fp::<3>(&[2, 1]));
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.unit, E3::ONE);
        assert_eq!(factorization.recompose(), polynomial);
        assert!(
            factorization
                .factors
                .iter()
                .any(|factor| factor.multiplicity == 2)
        );
    }

    #[test]
    fn inseparable_prime_field_polynomial_uses_pth_root_recursion() {
        let polynomial = TestPolynomial::fp::<2>(&[1, 0, 0, 0, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(
            factorization.factors[0].polynomial,
            TestPolynomial::fp::<2>(&[1, 1])
        );
        assert_eq!(factorization.factors[0].multiplicity, 4);
    }

    #[test]
    fn cantor_zassenhaus_handles_even_characteristic() {
        let polynomial = TestPolynomial::fp::<2>(&[0, 1, 1, 0, 0, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 2);
    }

    #[test]
    fn cantor_zassenhaus_splits_equal_degree_quadratics_in_odd_characteristic() {
        let polynomial = TestPolynomial::fp::<3>(&[2, 1, 0, 1, 1]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 2);
        assert!(
            factorization
                .factors
                .iter()
                .all(|factor| factor.polynomial.degree() == Some(2))
        );
    }

    #[test]
    fn finite_extension_pth_root_uses_inverse_frobenius_coefficients() {
        type F4 = Fq<2, 2>;
        type E4 = FqElement<2, 2>;

        let a = E4::from_values([0, 1]);
        let polynomial = DensePolynomial::<F4>::new(vec![a, E4::ZERO, E4::ONE]);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 2);
    }

    #[test]
    fn finite_extension_fields_use_the_same_finite_algorithm() {
        type F4 = Fq<2, 2>;
        type E4 = FqElement<2, 2>;

        let a = E4::from_values([0, 1]);
        let x_minus_a = DensePolynomial::<F4>::new(vec![-a, E4::ONE]);
        let x_minus_one = DensePolynomial::<F4>::new(vec![E4::ONE, E4::ONE]);
        let polynomial = x_minus_a.mul(&x_minus_one);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 2);
    }

    #[test]
    fn finite_factorization_is_deterministic() {
        let polynomial = TestPolynomial::fp::<5>(&[4, 0, 0, 0, 1]);
        let first = polynomial.factor().unwrap();
        let second = polynomial.factor().unwrap();

        assert_eq!(first, second);
    }

    #[test]
    fn small_prime_field_factorizations_recompose_into_irreducibles() {
        TestPolynomial::assert_all_monic_factorizations::<2>(5);
        TestPolynomial::assert_all_monic_factorizations::<3>(4);
    }
}
