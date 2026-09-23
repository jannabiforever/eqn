use eqn_core::set::Rational;

use super::dense::{DenseFactorization, DensePolynomial, PolynomialFactor};
use super::{RationalFactorizationError, RationalField};

/// Exact factorization over `Q`.
///
/// See <https://en.wikipedia.org/wiki/Kronecker%27s_method>.
pub(super) trait RationalFactorizationExt {
    fn factor_rational(
        &self,
    ) -> Result<DenseFactorization<RationalField>, RationalFactorizationError>;
}

impl RationalFactorizationExt for DensePolynomial<RationalField> {
    fn factor_rational(
        &self,
    ) -> Result<DenseFactorization<RationalField>, RationalFactorizationError> {
        let lifted = IntPolynomial::from_dense(self)?;
        let unit = I128Rational::from_rational(
            &self
                .leading_coefficient()
                .ok_or(RationalFactorizationError::ZeroPolynomial)?,
        )?
        .into_rational()?;
        let mut factors = Vec::new();

        for factor in lifted.primitive_part()?.factor_irreducibles()? {
            Self::push_rational_factor(&mut factors, factor.to_monic_dense()?);
        }

        factors.sort_by_key(Self::factor_sort_key);
        Ok(DenseFactorization { unit, factors })
    }
}

impl DensePolynomial<RationalField> {
    fn push_rational_factor(factors: &mut Vec<PolynomialFactor<RationalField>>, polynomial: Self) {
        if let Some(existing) = factors
            .iter_mut()
            .find(|factor| factor.polynomial == polynomial)
        {
            existing.multiplicity += 1;
        } else {
            factors.push(PolynomialFactor {
                polynomial,
                multiplicity: 1,
            });
        }
    }

    fn factor_sort_key(factor: &PolynomialFactor<RationalField>) -> (Option<usize>, String) {
        (
            factor.polynomial.degree(),
            format!("{:?}", factor.polynomial.coefficients()),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct IntPolynomial {
    coefficients: Vec<i128>,
}

impl IntPolynomial {
    fn new(mut coefficients: Vec<i128>) -> Self {
        while coefficients.last() == Some(&0) {
            coefficients.pop();
        }
        Self { coefficients }
    }

    fn from_dense(
        polynomial: &DensePolynomial<RationalField>,
    ) -> Result<Self, RationalFactorizationError> {
        if polynomial.is_zero() {
            return Err(RationalFactorizationError::ZeroPolynomial);
        }

        let coefficients = polynomial
            .coefficients()
            .iter()
            .map(I128Rational::from_rational)
            .collect::<Result<Vec<_>, _>>()?;
        let denominator_lcm = coefficients
            .iter()
            .try_fold(1i128, |lcm, coefficient| Checked::lcm(lcm, coefficient.den))?;
        let integers = coefficients
            .into_iter()
            .map(|coefficient| {
                Checked::mul(
                    coefficient.num,
                    denominator_lcm
                        .checked_div(coefficient.den)
                        .ok_or(RationalFactorizationError::FixedWidthOverflow)?,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(integers))
    }

    fn degree(&self) -> Option<usize> {
        self.coefficients.len().checked_sub(1)
    }

    fn is_constant(&self) -> bool {
        self.coefficients.len() <= 1
    }

    fn leading_coefficient(&self) -> Option<i128> {
        self.coefficients.last().copied()
    }

    fn primitive_part(&self) -> Result<Self, RationalFactorizationError> {
        if self.coefficients.is_empty() {
            return Err(RationalFactorizationError::ZeroPolynomial);
        }

        let content = self
            .coefficients
            .iter()
            .try_fold(0i128, |content, &coefficient| {
                Ok::<_, RationalFactorizationError>(Checked::gcd(
                    content,
                    Checked::abs(coefficient)?,
                ))
            })?;
        if content == 0 {
            return Err(RationalFactorizationError::ZeroPolynomial);
        }
        Ok(Self::new(
            self.coefficients
                .iter()
                .map(|coefficient| coefficient / content)
                .collect(),
        ))
    }

    fn factor_irreducibles(&self) -> Result<Vec<Self>, RationalFactorizationError> {
        if self.is_constant() {
            return Ok(Vec::new());
        }
        if self.degree() == Some(1) {
            return Ok(vec![self.primitive_part()?]);
        }

        match self.find_nontrivial_factor()? {
            Some(factor) => {
                let quotient = self.div_exact_integer(&factor)?;
                let mut factors = factor.primitive_part()?.factor_irreducibles()?;
                factors.extend(quotient.primitive_part()?.factor_irreducibles()?);
                Ok(factors)
            }
            None => Ok(vec![self.primitive_part()?]),
        }
    }

    fn find_nontrivial_factor(&self) -> Result<Option<Self>, RationalFactorizationError> {
        if self.coefficients.first() == Some(&0) {
            return Ok(Some(Self::new(vec![0, 1])));
        }
        let point_count = self
            .degree()
            .and_then(|degree| degree.checked_add(1))
            .ok_or(RationalFactorizationError::SearchConversion)?;
        let points = self.nonroot_points(point_count)?;
        let divisor_sets = points
            .iter()
            .map(|&point| self.evaluate(point).and_then(Checked::signed_divisors))
            .collect::<Result<Vec<_>, _>>()?;
        self.search_divisors(&points, &divisor_sets, &mut Vec::new(), 0)
    }

    fn search_divisors(
        &self,
        points: &[i128],
        divisor_sets: &[Vec<i128>],
        values: &mut Vec<i128>,
        index: usize,
    ) -> Result<Option<Self>, RationalFactorizationError> {
        if index == points.len() {
            let candidate = match Self::interpolate_integer(points, values) {
                Ok(candidate) => candidate.primitive_part()?,
                Err(RationalFactorizationError::SearchConversion) => return Ok(None),
                Err(error) => return Err(error),
            };
            if let Some(factor) = self.nontrivial_exact_factor(&candidate)? {
                return Ok(Some(factor));
            }
            return Ok(None);
        }

        for &value in &divisor_sets[index] {
            values.push(value);
            if let Some(factor) = self.search_divisors(points, divisor_sets, values, index + 1)? {
                return Ok(Some(factor));
            }
            values.pop();
        }
        Ok(None)
    }

    fn nontrivial_exact_factor(
        &self,
        candidate: &Self,
    ) -> Result<Option<Self>, RationalFactorizationError> {
        let self_degree = self.degree().unwrap_or(0);
        let candidate_degree = candidate.degree().unwrap_or(0);
        if candidate.is_constant() || candidate_degree >= self_degree {
            return Ok(None);
        }

        match self.div_exact_integer(candidate) {
            Ok(quotient) if !quotient.is_constant() => {
                if candidate_degree <= quotient.degree().unwrap_or(0) {
                    Ok(Some(candidate.primitive_part()?))
                } else {
                    Ok(Some(quotient.primitive_part()?))
                }
            }
            Ok(_) | Err(RationalFactorizationError::SearchConversion) => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn nonroot_points(&self, count: usize) -> Result<Vec<i128>, RationalFactorizationError> {
        let mut points = Vec::with_capacity(count);
        let mut radius = 0i128;
        while points.len() < count {
            for point in Self::point_candidates(radius) {
                if self.evaluate(point)? != 0 {
                    points.push(point);
                    if points.len() == count {
                        break;
                    }
                }
            }
            radius = radius
                .checked_add(1)
                .ok_or(RationalFactorizationError::SearchConversion)?;
        }
        Ok(points)
    }

    fn point_candidates(radius: i128) -> Vec<i128> {
        if radius == 0 {
            vec![0]
        } else {
            vec![radius, -radius]
        }
    }

    fn evaluate(&self, value: i128) -> Result<i128, RationalFactorizationError> {
        self.coefficients.iter().rev().try_fold(0i128, |sum, &c| {
            Checked::mul(sum, value).and_then(|product| Checked::add(product, c))
        })
    }

    fn interpolate_integer(
        points: &[i128],
        values: &[i128],
    ) -> Result<Self, RationalFactorizationError> {
        let mut coefficients = vec![I128Rational::integer(0); points.len()];
        for (i, (&x_i, &y_i)) in points.iter().zip(values).enumerate() {
            let mut basis = vec![1i128];
            let mut denominator = 1i128;
            for (j, &x_j) in points.iter().enumerate() {
                if i == j {
                    continue;
                }
                basis = Self::multiply_by_linear(&basis, Checked::neg(x_j)?)?;
                denominator = Checked::mul(denominator, Checked::sub(x_i, x_j)?)?;
            }
            let scale = I128Rational::new(y_i, denominator)?;
            for (degree, coefficient) in basis.into_iter().enumerate() {
                coefficients[degree] = coefficients[degree].add(scale.mul_i128(coefficient)?)?;
            }
        }

        let integers = coefficients
            .into_iter()
            .map(I128Rational::into_integer)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(integers))
    }

    fn multiply_by_linear(
        coefficients: &[i128],
        constant: i128,
    ) -> Result<Vec<i128>, RationalFactorizationError> {
        let mut product = vec![0i128; coefficients.len() + 1];
        for (degree, &coefficient) in coefficients.iter().enumerate() {
            product[degree] = Checked::add(product[degree], Checked::mul(coefficient, constant)?)?;
            product[degree + 1] = Checked::add(product[degree + 1], coefficient)?;
        }
        Ok(product)
    }

    fn div_exact_integer(&self, divisor: &Self) -> Result<Self, RationalFactorizationError> {
        if divisor.coefficients.is_empty() {
            return Err(RationalFactorizationError::SearchConversion);
        }
        if self.degree() < divisor.degree() {
            return Err(RationalFactorizationError::SearchConversion);
        }

        let mut remainder = self
            .coefficients
            .iter()
            .copied()
            .map(I128Rational::integer)
            .collect::<Vec<_>>();
        let mut quotient = vec![
            I128Rational::integer(0);
            self.coefficients.len() - divisor.coefficients.len() + 1
        ];
        let leading = I128Rational::integer(divisor.leading_coefficient().unwrap());

        while remainder.len() >= divisor.coefficients.len()
            && remainder.iter().any(|coefficient| !coefficient.is_zero())
        {
            Self::trim_rational_coefficients(&mut remainder);
            if remainder.len() < divisor.coefficients.len() {
                break;
            }
            let shift = remainder.len() - divisor.coefficients.len();
            let coefficient = remainder.last().copied().unwrap().div(leading)?;
            quotient[shift] = coefficient;
            for (degree, &divisor_coefficient) in divisor.coefficients.iter().enumerate() {
                let product = coefficient.mul_i128(divisor_coefficient)?;
                remainder[degree + shift] = remainder[degree + shift].sub(product)?;
            }
        }
        Self::trim_rational_coefficients(&mut remainder);
        if remainder.iter().any(|coefficient| !coefficient.is_zero()) {
            return Err(RationalFactorizationError::SearchConversion);
        }

        let integers = quotient
            .into_iter()
            .map(I128Rational::into_integer)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(integers))
    }

    fn trim_rational_coefficients(coefficients: &mut Vec<I128Rational>) {
        while coefficients.last().is_some_and(I128Rational::is_zero) {
            coefficients.pop();
        }
    }

    fn to_monic_dense(&self) -> Result<DensePolynomial<RationalField>, RationalFactorizationError> {
        let leading = self
            .leading_coefficient()
            .ok_or(RationalFactorizationError::ZeroPolynomial)?;
        Ok(DensePolynomial::from_coefficients(
            self.coefficients
                .iter()
                .map(|&coefficient| I128Rational::new(coefficient, leading)?.into_rational())
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct I128Rational {
    num: i128,
    den: i128,
}

impl I128Rational {
    fn new(num: i128, den: i128) -> Result<Self, RationalFactorizationError> {
        if den == 0 {
            return Err(RationalFactorizationError::InvalidDenominator);
        }
        let mut num = num;
        let mut den = den;
        if den < 0 {
            num = Checked::neg(num)?;
            den = Checked::neg(den)?;
        }
        let gcd = Checked::gcd(Checked::abs(num)?, den);
        Ok(Self {
            num: num / gcd,
            den: den / gcd,
        })
    }

    fn from_rational(value: &Rational) -> Result<Self, RationalFactorizationError> {
        Self::new(i128::from(value.numerator), i128::from(value.denominator))
    }

    fn integer(value: i128) -> Self {
        Self { num: value, den: 1 }
    }

    fn is_zero(&self) -> bool {
        self.num == 0
    }

    fn add(self, rhs: Self) -> Result<Self, RationalFactorizationError> {
        Self::new(
            Checked::add(
                Checked::mul(self.num, rhs.den)?,
                Checked::mul(rhs.num, self.den)?,
            )?,
            Checked::mul(self.den, rhs.den)?,
        )
    }

    fn sub(self, rhs: Self) -> Result<Self, RationalFactorizationError> {
        self.add(Self {
            num: Checked::neg(rhs.num)?,
            den: rhs.den,
        })
    }

    fn mul_i128(self, rhs: i128) -> Result<Self, RationalFactorizationError> {
        Self::new(Checked::mul(self.num, rhs)?, self.den)
    }

    fn div(self, rhs: Self) -> Result<Self, RationalFactorizationError> {
        Self::new(
            Checked::mul(self.num, rhs.den)?,
            Checked::mul(self.den, rhs.num)?,
        )
    }

    fn into_integer(self) -> Result<i128, RationalFactorizationError> {
        if self.den == 1 {
            Ok(self.num)
        } else {
            Err(RationalFactorizationError::SearchConversion)
        }
    }

    fn into_rational(self) -> Result<Rational, RationalFactorizationError> {
        Ok(Rational {
            numerator: i64::try_from(self.num)
                .map_err(|_| RationalFactorizationError::FixedWidthOverflow)?,
            denominator: i64::try_from(self.den)
                .map_err(|_| RationalFactorizationError::FixedWidthOverflow)?,
        })
    }
}

struct Checked;

impl Checked {
    fn add(lhs: i128, rhs: i128) -> Result<i128, RationalFactorizationError> {
        lhs.checked_add(rhs)
            .ok_or(RationalFactorizationError::FixedWidthOverflow)
    }

    fn sub(lhs: i128, rhs: i128) -> Result<i128, RationalFactorizationError> {
        lhs.checked_sub(rhs)
            .ok_or(RationalFactorizationError::FixedWidthOverflow)
    }

    fn mul(lhs: i128, rhs: i128) -> Result<i128, RationalFactorizationError> {
        lhs.checked_mul(rhs)
            .ok_or(RationalFactorizationError::FixedWidthOverflow)
    }

    fn neg(value: i128) -> Result<i128, RationalFactorizationError> {
        value
            .checked_neg()
            .ok_or(RationalFactorizationError::FixedWidthOverflow)
    }

    fn abs(value: i128) -> Result<i128, RationalFactorizationError> {
        value
            .checked_abs()
            .ok_or(RationalFactorizationError::FixedWidthOverflow)
    }

    fn gcd(mut lhs: i128, mut rhs: i128) -> i128 {
        while rhs != 0 {
            let next = lhs % rhs;
            lhs = rhs;
            rhs = next;
        }
        lhs.abs()
    }

    fn lcm(lhs: i128, rhs: i128) -> Result<i128, RationalFactorizationError> {
        if lhs == 0 || rhs == 0 {
            return Err(RationalFactorizationError::InvalidDenominator);
        }
        Self::mul(lhs / Self::gcd(lhs, rhs), rhs).and_then(Self::abs)
    }

    fn signed_divisors(value: i128) -> Result<Vec<i128>, RationalFactorizationError> {
        let value = Self::abs(value)?;
        if value == 0 {
            return Err(RationalFactorizationError::SearchConversion);
        }

        let mut divisors = Vec::new();
        let mut candidate = 1i128;
        while Self::mul(candidate, candidate)? <= value {
            if value % candidate == 0 {
                divisors.push(candidate);
                divisors.push(Self::neg(candidate)?);
                let paired = value / candidate;
                if paired != candidate {
                    divisors.push(paired);
                    divisors.push(Self::neg(paired)?);
                }
            }
            candidate = Self::add(candidate, 1)?;
        }
        divisors.sort_unstable();
        divisors.dedup();
        Ok(divisors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestRationalPolynomial;

    impl TestRationalPolynomial {
        fn q(value: i64) -> Rational {
            Rational::from(value)
        }

        fn r(numerator: i64, denominator: i64) -> Rational {
            Rational {
                numerator,
                denominator,
            }
        }

        fn polynomial(coefficients: &[i64]) -> DensePolynomial<RationalField> {
            DensePolynomial::from_coefficients(
                coefficients
                    .iter()
                    .copied()
                    .map(Self::q)
                    .collect::<Vec<_>>(),
            )
        }

        fn assert_recomposes(
            polynomial: DensePolynomial<RationalField>,
            expected: Vec<Vec<Rational>>,
        ) {
            let factorization = polynomial.factor_rational().unwrap();
            assert_eq!(factorization.recompose(), polynomial);
            assert_eq!(
                factorization
                    .factors
                    .iter()
                    .map(|factor| { factor.polynomial.coefficients().to_vec() })
                    .collect::<Vec<_>>(),
                expected
            );
        }
    }

    #[test]
    fn nonmonic_polynomial_recomposes_with_its_content() {
        TestRationalPolynomial::assert_recomposes(
            TestRationalPolynomial::polynomial(&[12, 14, 4]),
            vec![
                vec![TestRationalPolynomial::q(2), TestRationalPolynomial::q(1)],
                vec![
                    TestRationalPolynomial::r(3, 2),
                    TestRationalPolynomial::q(1),
                ],
            ],
        );
    }

    #[test]
    fn repeated_factors_are_recorded_as_multiplicity() {
        let polynomial = TestRationalPolynomial::polynomial(&[-1, 3, -3, 1]);
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 3);
        assert_eq!(
            factorization.factors[0].polynomial,
            TestRationalPolynomial::polynomial(&[-1, 1])
        );
    }

    #[test]
    fn repeated_zero_roots_are_recorded_as_multiplicity() {
        let polynomial = TestRationalPolynomial::polynomial(&[0, 0, 0, 1]);
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 3);
        assert_eq!(
            factorization.factors[0].polynomial,
            TestRationalPolynomial::polynomial(&[0, 1])
        );
    }

    #[test]
    fn x_squared_plus_one_is_irreducible_over_the_rationals() {
        TestRationalPolynomial::assert_recomposes(
            TestRationalPolynomial::polynomial(&[1, 0, 1]),
            vec![vec![
                TestRationalPolynomial::q(1),
                TestRationalPolynomial::q(0),
                TestRationalPolynomial::q(1),
            ]],
        );
    }

    #[test]
    fn reducible_polynomial_without_rational_roots_is_split() {
        TestRationalPolynomial::assert_recomposes(
            TestRationalPolynomial::polynomial(&[4, 0, 0, 0, 1]),
            vec![
                vec![
                    TestRationalPolynomial::q(2),
                    TestRationalPolynomial::q(-2),
                    TestRationalPolynomial::q(1),
                ],
                vec![
                    TestRationalPolynomial::q(2),
                    TestRationalPolynomial::q(2),
                    TestRationalPolynomial::q(1),
                ],
            ],
        );
    }

    #[test]
    fn rational_coefficients_are_cleared_before_factorization() {
        let polynomial = DensePolynomial::from_coefficients(vec![
            TestRationalPolynomial::r(1, 2),
            TestRationalPolynomial::r(3, 2),
            Rational::ONE,
        ]);

        assert_eq!(
            polynomial.factor_rational().unwrap().recompose(),
            polynomial
        );
    }
}
