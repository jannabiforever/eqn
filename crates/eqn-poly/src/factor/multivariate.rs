use std::collections::BTreeMap;
use std::marker::PhantomData;

use eqn_algebra::field::Field;
use eqn_algebra::ring::RingElem;

use super::dense::{DensePolynomial, PolynomialFactor};
use super::rational::RationalFactorizationExt;
use super::{FactorizationError, FiniteFactorField, RationalFactorizationError, RationalField};

/// A coordinate-indexed multivariate polynomial over a field.
///
/// NOTE: This representation intentionally overlaps with [`crate::Polynomial`].
/// A fixed variable order supports Kronecker substitution and reconstruction,
/// while [`crate::Polynomial`] preserves symbol identity.
///
/// See <https://en.wikipedia.org/wiki/Kronecker_substitution>.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct IndexedPolynomial<F: Field> {
    variables: usize,
    terms: BTreeMap<Vec<usize>, RingElem<F>>,
    #[derive_where(skip)]
    field: PhantomData<F>,
}

/// A coordinate-indexed factor with multiplicity.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct IndexedFactor<F: Field> {
    pub(super) polynomial: IndexedPolynomial<F>,
    pub(super) multiplicity: usize,
}

/// A unit times monic coordinate-indexed factors.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub(super) struct IndexedFactorization<F: Field> {
    pub(super) variables: usize,
    pub(super) unit: RingElem<F>,
    pub(super) factors: Vec<IndexedFactor<F>>,
}

impl<F: Field> IndexedFactorization<F> {
    #[cfg(test)]
    pub(super) fn recompose(&self) -> IndexedPolynomial<F> {
        let mut product = IndexedPolynomial::constant(self.variables, self.unit.clone());
        for factor in &self.factors {
            for _ in 0..factor.multiplicity {
                product = product.mul(&factor.polynomial);
            }
        }
        product
    }
}

impl<F: Field> IndexedPolynomial<F> {
    pub(super) fn new(
        variables: usize,
        terms: impl IntoIterator<Item = (Vec<usize>, RingElem<F>)>,
    ) -> Self {
        let mut collected = BTreeMap::new();
        for (exponents, coefficient) in terms {
            assert_eq!(
                exponents.len(),
                variables,
                "term has the wrong number of variables"
            );
            if coefficient == F::ZERO {
                continue;
            }
            collected
                .entry(exponents)
                .and_modify(|old: &mut RingElem<F>| *old = F::add(old.clone(), coefficient.clone()))
                .or_insert(coefficient);
        }
        collected.retain(|_, coefficient| *coefficient != F::ZERO);
        Self {
            variables,
            terms: collected,
            field: PhantomData,
        }
    }

    pub(super) fn zero(variables: usize) -> Self {
        Self::new(variables, [])
    }

    #[cfg(test)]
    pub(super) fn one(variables: usize) -> Self {
        Self::constant(variables, F::ONE)
    }

    #[cfg(test)]
    pub(super) fn constant(variables: usize, coefficient: RingElem<F>) -> Self {
        if coefficient == F::ZERO {
            Self::zero(variables)
        } else {
            Self::new(variables, [(vec![0; variables], coefficient)])
        }
    }

    #[cfg(test)]
    pub(super) fn variable(variables: usize, variable: usize) -> Self {
        assert!(variable < variables, "variable index out of range");
        let mut exponents = vec![0; variables];
        exponents[variable] = 1;
        Self::new(variables, [(exponents, F::ONE)])
    }

    pub(super) fn monomial(
        variables: usize,
        exponents: Vec<usize>,
        coefficient: RingElem<F>,
    ) -> Self {
        Self::new(variables, [(exponents, coefficient)])
    }

    pub(super) fn terms(&self) -> &BTreeMap<Vec<usize>, RingElem<F>> {
        &self.terms
    }

    pub(super) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub(super) fn is_constant(&self) -> bool {
        self.terms
            .keys()
            .all(|exponents| exponents.iter().all(|exponent| *exponent == 0))
    }

    pub(super) fn constant_coefficient(&self) -> RingElem<F> {
        self.terms
            .get(&vec![0; self.variables])
            .cloned()
            .unwrap_or(F::ZERO)
    }

    pub(super) fn add(&self, rhs: &Self) -> Self {
        assert_eq!(self.variables, rhs.variables, "variable count mismatch");
        let mut terms = self.terms.clone();
        for (exponents, coefficient) in &rhs.terms {
            terms
                .entry(exponents.clone())
                .and_modify(|old| *old = F::add(old.clone(), coefficient.clone()))
                .or_insert_with(|| coefficient.clone());
        }
        Self::new(self.variables, terms)
    }

    pub(super) fn neg(&self) -> Self {
        Self::new(
            self.variables,
            self.terms.iter().map(|(exponents, coefficient)| {
                (exponents.clone(), F::negate(coefficient.clone()))
            }),
        )
    }

    pub(super) fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.neg())
    }

    pub(super) fn mul(&self, rhs: &Self) -> Self {
        assert_eq!(self.variables, rhs.variables, "variable count mismatch");
        if self.is_zero() || rhs.is_zero() {
            return Self::zero(self.variables);
        }

        let mut terms = BTreeMap::new();
        for (left_exponents, left_coefficient) in &self.terms {
            for (right_exponents, right_coefficient) in &rhs.terms {
                let exponents = left_exponents
                    .iter()
                    .zip(right_exponents)
                    .map(|(left, right)| {
                        left.checked_add(*right)
                            .expect("monomial exponent overflow")
                    })
                    .collect::<Vec<_>>();
                let coefficient = F::multiply(left_coefficient.clone(), right_coefficient.clone());
                terms
                    .entry(exponents)
                    .and_modify(|old: &mut RingElem<F>| {
                        *old = F::add(old.clone(), coefficient.clone())
                    })
                    .or_insert(coefficient);
            }
        }
        Self::new(self.variables, terms)
    }

    pub(super) fn scale(&self, scalar: RingElem<F>) -> Self {
        if scalar == F::ZERO {
            return Self::zero(self.variables);
        }
        Self::new(
            self.variables,
            self.terms.iter().map(|(exponents, coefficient)| {
                (
                    exponents.clone(),
                    F::multiply(scalar.clone(), coefficient.clone()),
                )
            }),
        )
    }

    pub(super) fn monic(&self) -> Self {
        match self.leading_coefficient() {
            Some(coefficient) => self.scale(F::invert(coefficient)),
            None => self.clone(),
        }
    }

    pub(super) fn div_exact(&self, divisor: &Self) -> Result<Self, FactorizationError> {
        self.div_rem(divisor).and_then(|(quotient, remainder)| {
            if remainder.is_zero() {
                Ok(quotient)
            } else {
                Err(FactorizationError::InexactDivision)
            }
        })
    }

    pub(super) fn div_rem(&self, divisor: &Self) -> Result<(Self, Self), FactorizationError> {
        assert_eq!(self.variables, divisor.variables, "variable count mismatch");
        if divisor.is_zero() {
            return Err(FactorizationError::DivisionByZero);
        }

        let mut quotient = Self::zero(self.variables);
        let mut remainder = Self::zero(self.variables);
        let mut work = self.clone();
        let (divisor_exponents, divisor_coefficient) = divisor
            .leading_term()
            .ok_or(FactorizationError::DivisionByZero)?;
        let divisor_inverse = F::invert(divisor_coefficient);

        while let Some((work_exponents, work_coefficient)) = work.leading_term() {
            if let Some(exponents) =
                Self::checked_exponent_difference(&work_exponents, &divisor_exponents)
            {
                let coefficient = F::multiply(work_coefficient, divisor_inverse.clone());
                let term = Self::monomial(self.variables, exponents, coefficient);
                quotient = quotient.add(&term);
                work = work.sub(&term.mul(divisor));
            } else {
                let term = Self::monomial(self.variables, work_exponents, work_coefficient);
                remainder = remainder.add(&term);
                work = work.sub(&term);
            }
        }

        Ok((quotient, remainder))
    }

    fn leading_term(&self) -> Option<(Vec<usize>, RingElem<F>)> {
        self.terms
            .last_key_value()
            .map(|(exponents, coefficient)| (exponents.clone(), coefficient.clone()))
    }

    fn leading_coefficient(&self) -> Option<RingElem<F>> {
        self.leading_term().map(|(_, coefficient)| coefficient)
    }

    fn checked_exponent_difference(left: &[usize], right: &[usize]) -> Option<Vec<usize>> {
        left.iter()
            .zip(right)
            .map(|(left, right)| left.checked_sub(*right))
            .collect()
    }

    fn degree_bounds(&self) -> Vec<usize> {
        let mut bounds = vec![0; self.variables];
        for exponents in self.terms.keys() {
            for (variable, exponent) in exponents.iter().copied().enumerate() {
                bounds[variable] = bounds[variable].max(exponent);
            }
        }
        bounds
    }

    fn kronecker_base(&self) -> Result<usize, FactorizationError> {
        self.degree_bounds()
            .into_iter()
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .map(|base| base.max(2))
            .ok_or(FactorizationError::FieldOrderOverflow)
    }

    fn kronecker_powers(&self, base: usize) -> Result<Vec<usize>, FactorizationError> {
        let mut powers = Vec::with_capacity(self.variables);
        let mut power = 1usize;
        for _ in 0..self.variables {
            powers.push(power);
            if powers.len() < self.variables {
                power = power
                    .checked_mul(base)
                    .ok_or(FactorizationError::FieldOrderOverflow)?;
            }
        }
        Ok(powers)
    }

    fn encode_kronecker(&self, base: usize) -> Result<DensePolynomial<F>, FactorizationError> {
        let powers = self.kronecker_powers(base)?;
        let mut coefficients = Vec::new();
        for (exponents, coefficient) in &self.terms {
            let degree = exponents
                .iter()
                .zip(&powers)
                .try_fold(0usize, |degree, (exponent, power)| {
                    exponent
                        .checked_mul(*power)
                        .and_then(|term_degree| degree.checked_add(term_degree))
                })
                .ok_or(FactorizationError::FieldOrderOverflow)?;
            if coefficients.len() <= degree {
                coefficients.resize(degree + 1, F::ZERO);
            }
            coefficients[degree] = F::add(coefficients[degree].clone(), coefficient.clone());
        }
        Ok(DensePolynomial::new(coefficients))
    }

    fn decode_kronecker(
        variables: usize,
        bounds: &[usize],
        base: usize,
        polynomial: &DensePolynomial<F>,
    ) -> Option<Self> {
        let mut terms = Vec::new();
        for (mut degree, coefficient) in polynomial.coefficients().iter().cloned().enumerate() {
            if coefficient == F::ZERO {
                continue;
            }
            let mut exponents = vec![0; variables];
            for variable in 0..variables {
                let exponent = degree % base;
                if exponent > bounds[variable] {
                    return None;
                }
                exponents[variable] = exponent;
                degree /= base;
            }
            if degree != 0 {
                return None;
            }
            terms.push((exponents, coefficient));
        }
        Some(Self::new(variables, terms))
    }

    fn push_factor(factors: &mut Vec<IndexedFactor<F>>, polynomial: Self) {
        if polynomial.is_constant() {
            return;
        }
        let polynomial = polynomial.monic();
        if let Some(factor) = factors
            .iter_mut()
            .find(|factor| factor.polynomial == polynomial)
        {
            factor.multiplicity += 1;
        } else {
            factors.push(IndexedFactor {
                polynomial,
                multiplicity: 1,
            });
        }
    }

    fn sort_factors(factors: &mut [IndexedFactor<F>]) {
        factors.sort_by_key(|factor| factor.polynomial.sort_key());
    }

    fn sort_key(&self) -> (u128, String) {
        (
            self.terms
                .keys()
                .map(|exponents| exponents.iter().map(|&exponent| exponent as u128).sum())
                .max()
                .unwrap_or(0),
            format!("{:?}", self.terms),
        )
    }
}

struct KroneckerSearch<'a, F: Field> {
    variables: usize,
    bounds: &'a [usize],
    base: usize,
    atoms: &'a [DensePolynomial<F>],
    remaining: &'a IndexedPolynomial<F>,
}

impl<F: Field> KroneckerSearch<'_, F> {
    fn find_factor_candidate(
        &self,
    ) -> Result<Option<(IndexedPolynomial<F>, Vec<usize>)>, FactorizationError> {
        for size in 1..self.atoms.len() {
            let mut subset = Vec::with_capacity(size);
            if let Some(candidate) = self.find_factor_candidate_of_size(size, 0, &mut subset)? {
                return Ok(Some(candidate));
            }
        }
        Ok(None)
    }

    fn find_factor_candidate_of_size(
        &self,
        size: usize,
        start: usize,
        subset: &mut Vec<usize>,
    ) -> Result<Option<(IndexedPolynomial<F>, Vec<usize>)>, FactorizationError> {
        if subset.len() == size {
            let encoded = subset
                .iter()
                .fold(DensePolynomial::one(), |product, index| {
                    product.mul(&self.atoms[*index])
                });
            let Some(candidate) = IndexedPolynomial::decode_kronecker(
                self.variables,
                self.bounds,
                self.base,
                &encoded,
            ) else {
                return Ok(None);
            };
            let candidate = candidate.monic();
            if !candidate.is_constant() && self.remaining.div_exact(&candidate).is_ok() {
                return Ok(Some((candidate, subset.clone())));
            }
            return Ok(None);
        }

        let needed = size - subset.len();
        for index in start..=self.atoms.len() - needed {
            subset.push(index);
            if let Some(candidate) = self.find_factor_candidate_of_size(size, index + 1, subset)? {
                return Ok(Some(candidate));
            }
            subset.pop();
        }
        Ok(None)
    }

    fn certifies_remaining_irreducible(&self) -> bool {
        let encoded = self
            .atoms
            .iter()
            .fold(DensePolynomial::one(), |product, atom| product.mul(atom));
        IndexedPolynomial::decode_kronecker(self.variables, self.bounds, self.base, &encoded)
            .is_some_and(|candidate| candidate.monic() == self.remaining.monic())
    }
}

impl<F: Field> IndexedPolynomial<F> {
    fn factor_from_kronecker_atoms(
        &self,
        atoms: Vec<DensePolynomial<F>>,
    ) -> Result<IndexedFactorization<F>, FactorizationError> {
        if self.is_zero() {
            return Err(FactorizationError::ZeroPolynomial);
        }
        if self.is_constant() {
            return Ok(IndexedFactorization {
                variables: self.variables,
                unit: self.constant_coefficient(),
                factors: Vec::new(),
            });
        }

        let base = self.kronecker_base()?;
        let bounds = self.degree_bounds();
        let mut atoms = atoms;
        let mut remaining = self.clone();
        let mut factors = Vec::new();

        while !atoms.is_empty() && !remaining.is_constant() {
            let search = KroneckerSearch {
                variables: remaining.variables,
                bounds: &bounds,
                base,
                atoms: &atoms,
                remaining: &remaining,
            };
            let Some((candidate, used)) = search.find_factor_candidate()? else {
                if search.certifies_remaining_irreducible() {
                    let unit = remaining.leading_coefficient().unwrap_or(F::ONE);
                    Self::push_factor(&mut factors, remaining.monic());
                    Self::sort_factors(&mut factors);
                    return Ok(IndexedFactorization {
                        variables: self.variables,
                        unit,
                        factors,
                    });
                }
                return Err(FactorizationError::DeterministicSplittingExhausted);
            };
            remaining = remaining.div_exact(&candidate)?;
            Self::remove_atoms(&mut atoms, &used);
            Self::push_factor(&mut factors, candidate);
        }

        if !atoms.is_empty() {
            return Err(FactorizationError::DeterministicSplittingExhausted);
        }

        let unit = if remaining.is_constant() {
            remaining.constant_coefficient()
        } else {
            let unit = remaining.leading_coefficient().unwrap_or(F::ONE);
            Self::push_factor(&mut factors, remaining.monic());
            unit
        };
        Self::sort_factors(&mut factors);
        Ok(IndexedFactorization {
            variables: self.variables,
            unit,
            factors,
        })
    }

    fn expanded_univariate_atoms(factors: Vec<PolynomialFactor<F>>) -> Vec<DensePolynomial<F>> {
        let mut atoms = Vec::new();
        for factor in factors {
            for _ in 0..factor.multiplicity {
                atoms.push(factor.polynomial.clone());
            }
        }
        atoms
    }

    fn remove_atoms(atoms: &mut Vec<DensePolynomial<F>>, used: &[usize]) {
        for index in used.iter().rev() {
            atoms.remove(*index);
        }
    }
}

impl<F: FiniteFactorField> IndexedPolynomial<F> {
    /// The irreducible factorization over a finite field.
    pub(super) fn factor_finite_field(
        &self,
    ) -> Result<IndexedFactorization<F>, FactorizationError> {
        if self.is_zero() {
            return Err(FactorizationError::ZeroPolynomial);
        }
        let base = self.kronecker_base()?;
        let encoded = self.encode_kronecker(base)?;
        let encoded_factorization = encoded.factor()?;
        self.factor_from_kronecker_atoms(Self::expanded_univariate_atoms(
            encoded_factorization.factors,
        ))
    }
}

impl IndexedPolynomial<RationalField> {
    /// The irreducible factorization over `Q`.
    pub(super) fn factor_rational(
        &self,
    ) -> Result<IndexedFactorization<RationalField>, RationalFactorizationError> {
        if self.is_zero() {
            return Err(RationalFactorizationError::ZeroPolynomial);
        }
        let base = self
            .kronecker_base()
            .map_err(|_| RationalFactorizationError::SearchConversion)?;
        let encoded = self
            .encode_kronecker(base)
            .map_err(|_| RationalFactorizationError::SearchConversion)?;
        let encoded_factorization = encoded.factor_rational()?;
        self.factor_from_kronecker_atoms(Self::expanded_univariate_atoms(
            encoded_factorization.factors,
        ))
        .map_err(|_| RationalFactorizationError::SearchConversion)
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{PrimeField, PrimeFieldElement};
    use eqn_core::set::Rational;

    use super::*;

    type F2 = PrimeField<2>;
    type F3 = PrimeField<3>;
    type E2 = PrimeFieldElement<2>;
    type E3 = PrimeFieldElement<3>;

    struct TestIndexedPolynomial;

    impl TestIndexedPolynomial {
        fn f2(value: u64) -> E2 {
            E2::new(value)
        }

        fn f3(value: u64) -> E3 {
            E3::new(value)
        }

        fn q(value: i64) -> Rational {
            Rational::from(value)
        }

        fn r(numerator: i64, denominator: i64) -> Rational {
            Rational {
                numerator,
                denominator,
            }
        }
    }

    #[test]
    fn finite_field_factorization_splits_difference_of_squares() {
        let polynomial = IndexedPolynomial::<F3>::new(
            2,
            [
                (vec![2, 0], TestIndexedPolynomial::f3(1)),
                (vec![0, 2], TestIndexedPolynomial::f3(2)),
            ],
        );
        let factorization = polynomial.factor_finite_field().unwrap();

        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn finite_field_factorization_recomposes_three_linear_factors() {
        let x = IndexedPolynomial::<F3>::variable(2, 0);
        let y = IndexedPolynomial::<F3>::variable(2, 1);
        let polynomial = x.mul(&y).mul(&x.add(&y));
        let factorization = polynomial.factor_finite_field().unwrap();

        assert_eq!(factorization.factors.len(), 3);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn finite_field_factorization_records_inseparable_square() {
        let polynomial = IndexedPolynomial::<F2>::new(
            2,
            [
                (vec![2, 0], TestIndexedPolynomial::f2(1)),
                (vec![0, 2], TestIndexedPolynomial::f2(1)),
            ],
        );
        let factorization = polynomial.factor_finite_field().unwrap();

        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn finite_field_factorization_keeps_irreducible_multivariate_factor() {
        let polynomial = IndexedPolynomial::<F2>::new(
            2,
            [
                (vec![1, 1], TestIndexedPolynomial::f2(1)),
                (vec![1, 0], TestIndexedPolynomial::f2(1)),
                (vec![0, 1], TestIndexedPolynomial::f2(1)),
            ],
        );
        let factorization = polynomial.factor_finite_field().unwrap();

        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].polynomial, polynomial);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn multivariate_division_reduces_terms_after_an_undivisible_leader() {
        let x = IndexedPolynomial::<F3>::variable(2, 0);
        let y = IndexedPolynomial::<F3>::variable(2, 1);
        let dividend = x.add(&y);
        let (quotient, remainder) = dividend.div_rem(&y).unwrap();

        assert_eq!(quotient, IndexedPolynomial::one(2));
        assert_eq!(remainder, x);
        assert_eq!(quotient.mul(&y).add(&remainder), dividend);
    }

    #[test]
    fn constant_factorization_preserves_its_variable_count() {
        let polynomial = IndexedPolynomial::<F3>::constant(3, TestIndexedPolynomial::f3(2));
        let factorization = polynomial.factor_finite_field().unwrap();

        assert_eq!(factorization.variables, 3);
        assert_eq!(factorization.unit, TestIndexedPolynomial::f3(2));
        assert!(factorization.factors.is_empty());
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn kronecker_factorization_rejects_an_unrepresentable_base() {
        let polynomial =
            IndexedPolynomial::<F3>::monomial(1, vec![usize::MAX], TestIndexedPolynomial::f3(1));

        assert_eq!(
            polynomial.factor_finite_field(),
            Err(FactorizationError::FieldOrderOverflow)
        );
    }

    #[test]
    #[should_panic(expected = "monomial exponent overflow")]
    fn indexed_multiplication_rejects_exponent_overflow() {
        let maximal =
            IndexedPolynomial::<F3>::monomial(1, vec![usize::MAX], TestIndexedPolynomial::f3(1));
        let variable = IndexedPolynomial::<F3>::variable(1, 0);

        maximal.mul(&variable);
    }

    #[test]
    fn rational_factorization_splits_difference_of_squares() {
        let polynomial = IndexedPolynomial::<RationalField>::new(
            2,
            [
                (vec![2, 0], TestIndexedPolynomial::q(1)),
                (vec![0, 2], TestIndexedPolynomial::q(-1)),
            ],
        );
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn rational_factorization_recomposes_three_linear_factors() {
        let x = IndexedPolynomial::<RationalField>::variable(2, 0);
        let y = IndexedPolynomial::<RationalField>::variable(2, 1);
        let polynomial = x.mul(&y).mul(&x.add(&y));
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.factors.len(), 3);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn rational_factorization_preserves_nonmonic_unit() {
        let x = IndexedPolynomial::<RationalField>::variable(2, 0);
        let y = IndexedPolynomial::<RationalField>::variable(2, 1);
        let scalar = TestIndexedPolynomial::r(3, 2);
        let polynomial = x.mul(&x.add(&y)).scale(scalar.clone());
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.unit, scalar);
        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn rational_factorization_certifies_irreducible_multivariate_residue() {
        let polynomial = IndexedPolynomial::<RationalField>::new(
            2,
            [
                (vec![1, 1], TestIndexedPolynomial::q(1)),
                (vec![1, 0], TestIndexedPolynomial::q(1)),
                (vec![0, 1], TestIndexedPolynomial::q(1)),
            ],
        );
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].polynomial, polynomial);
        assert_eq!(factorization.recompose(), polynomial);
    }
}
