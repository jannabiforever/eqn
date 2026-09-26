//! Polynomial factorization through private algorithm-specific kernels.
//!
//! [`Polynomial`] remains the only public polynomial representation. Dense
//! coefficient arrays and coordinate-indexed terms are temporary internal
//! forms because Cantor-Zassenhaus and Kronecker substitution need constant-
//! time degree and exponent access.

use std::collections::BTreeMap;
use std::fmt;
use std::num::NonZeroUsize;

use eqn_algebra::field::{Field, PrimeField, PrimeFieldElement};
use eqn_algebra::operator_impl::{QAdd, QMul};
use eqn_algebra::ring::RingElem;
use eqn_core::set::{Q, Set};
use eqn_core::symbol::Symbol;

use crate::finite_field::{FiniteField, FiniteFieldElement, IrreduciblePolynomial};
use crate::{Monomial, Polynomial};

mod dense;
mod multivariate;
mod rational;

/// The rational coefficient field.
pub type RationalField = (Q, QAdd, QMul);

/// A coefficient field with known characteristic.
pub trait FactorCoefficientField: Field {
    const CHARACTERISTIC: u64;
}

/// A finite coefficient field.
pub trait FiniteFactorField: FactorCoefficientField {
    fn order() -> Result<u128, FactorizationError>;

    fn element(index: u128) -> Result<RingElem<Self>, FactorizationError>;

    fn pth_root(value: RingElem<Self>) -> RingElem<Self>;
}

impl<const P: u64> FactorCoefficientField for PrimeField<P> {
    const CHARACTERISTIC: u64 = P;
}

impl<const P: u64> FiniteFactorField for PrimeField<P> {
    fn order() -> Result<u128, FactorizationError> {
        Ok(u128::from(P))
    }

    fn element(index: u128) -> Result<RingElem<Self>, FactorizationError> {
        if index >= Self::order()? {
            return Err(FactorizationError::ElementIndexOutOfRange);
        }
        let value = u64::try_from(index).map_err(|_| FactorizationError::FieldOrderOverflow)?;
        Ok(PrimeFieldElement::new(value))
    }

    fn pth_root(value: RingElem<Self>) -> RingElem<Self> {
        value
    }
}

impl<const P: u64, const N: usize, M> FactorCoefficientField for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    const CHARACTERISTIC: u64 = P;
}

impl<const P: u64, const N: usize, M> FiniteFactorField for FiniteField<P, N, M>
where
    M: IrreduciblePolynomial<P, N>,
{
    fn order() -> Result<u128, FactorizationError> {
        let mut order = 1u128;
        for _ in 0..N {
            order = order
                .checked_mul(u128::from(P))
                .ok_or(FactorizationError::FieldOrderOverflow)?;
        }
        Ok(order)
    }

    fn element(mut index: u128) -> Result<RingElem<Self>, FactorizationError> {
        if index >= Self::order()? {
            return Err(FactorizationError::ElementIndexOutOfRange);
        }
        let mut coefficients = [PrimeFieldElement::ZERO; N];
        for coefficient in &mut coefficients {
            let value = u64::try_from(index % u128::from(P))
                .map_err(|_| FactorizationError::FieldOrderOverflow)?;
            *coefficient = PrimeFieldElement::new(value);
            index /= u128::from(P);
        }
        Ok(FiniteFieldElement::from_coefficients(coefficients))
    }

    fn pth_root(mut value: RingElem<Self>) -> RingElem<Self> {
        for _ in 1..N {
            value = value.pow(u128::from(P));
        }
        value
    }
}

/// A finite-field factorization failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FactorizationError {
    ZeroPolynomial,
    DivisionByZero,
    InexactDivision,
    NonPositiveCharacteristic,
    FieldOrderOverflow,
    ElementIndexOutOfRange,
    MultiplicityOverflow,
    DeterministicSplittingExhausted,
}

impl fmt::Display for FactorizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroPolynomial => write!(f, "the zero polynomial has no finite factorization"),
            Self::DivisionByZero => write!(f, "division by the zero polynomial"),
            Self::InexactDivision => write!(f, "polynomial division left a nonzero remainder"),
            Self::NonPositiveCharacteristic => write!(f, "the characteristic must be positive"),
            Self::FieldOrderOverflow => write!(f, "finite-field order or exponent overflowed"),
            Self::ElementIndexOutOfRange => write!(f, "finite-field element index is out of range"),
            Self::MultiplicityOverflow => write!(f, "factor multiplicity overflowed"),
            Self::DeterministicSplittingExhausted => {
                write!(f, "exhaustive deterministic splitting did not split")
            }
        }
    }
}

impl std::error::Error for FactorizationError {}

/// A rational factorization failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RationalFactorizationError {
    ZeroPolynomial,
    InvalidDenominator,
    FixedWidthOverflow,
    SearchConversion,
}

impl fmt::Display for RationalFactorizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroPolynomial => write!(f, "the zero polynomial has no finite factorization"),
            Self::InvalidDenominator => write!(f, "a rational coefficient has denominator zero"),
            Self::FixedWidthOverflow => write!(f, "fixed-width arithmetic overflowed"),
            Self::SearchConversion => write!(f, "Kronecker search exceeded fixed-width bounds"),
        }
    }
}

impl std::error::Error for RationalFactorizationError {}

/// An irreducible factor with multiplicity.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; RingElem<R>)]
pub struct PolynomialFactor<R: Field> {
    pub polynomial: Polynomial<R>,
    pub multiplicity: usize,
}

/// A unit times monic irreducible polynomial factors.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq; RingElem<R>)]
pub struct PolynomialFactorization<R: Field> {
    pub unit: RingElem<R>,
    pub factors: Vec<PolynomialFactor<R>>,
}

impl<R: Field> PolynomialFactorization<R> {
    pub fn recompose(&self) -> Polynomial<R> {
        let mut product = Polynomial::constant(self.unit.clone());
        for factor in &self.factors {
            if let Some(multiplicity) = NonZeroUsize::new(factor.multiplicity) {
                product = product * factor.polynomial.clone().pow(multiplicity);
            }
        }
        product
    }
}

/// Why polynomial factorization did not produce a finite factorization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PolynomialFactorizationError {
    FiniteField(FactorizationError),
    Rational(RationalFactorizationError),
    MissingVariable,
}

impl fmt::Display for PolynomialFactorizationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FiniteField(error) => error.fmt(f),
            Self::Rational(error) => error.fmt(f),
            Self::MissingVariable => f.write_str("a nonconstant factor needs a variable"),
        }
    }
}

impl std::error::Error for PolynomialFactorizationError {}

impl From<FactorizationError> for PolynomialFactorizationError {
    fn from(error: FactorizationError) -> Self {
        Self::FiniteField(error)
    }
}

impl From<RationalFactorizationError> for PolynomialFactorizationError {
    fn from(error: RationalFactorizationError) -> Self {
        Self::Rational(error)
    }
}

struct PolynomialFactorCodec;

impl PolynomialFactorCodec {
    fn variables<R: Field>(polynomial: &Polynomial<R>) -> Vec<Symbol<R::Domain>> {
        let mut variables = BTreeMap::new();
        for monomial in polynomial.terms.keys() {
            for variable in monomial.0.keys() {
                variables.insert(variable.clone(), ());
            }
        }
        variables.into_keys().collect()
    }

    fn into_dense<R: Field>(
        polynomial: &Polynomial<R>,
    ) -> (Option<Symbol<R::Domain>>, dense::DensePolynomial<R>) {
        let variable = Self::variables(polynomial).into_iter().next();
        let mut coefficients = vec![polynomial.constant.clone()];
        for (monomial, coefficient) in &polynomial.terms {
            let degree = monomial
                .0
                .values()
                .next()
                .map(|exponent| exponent.get())
                .unwrap_or(0);
            if coefficients.len() <= degree {
                coefficients.resize(degree + 1, R::ZERO);
            }
            coefficients[degree] = R::add(coefficients[degree].clone(), coefficient.clone());
        }
        (variable, dense::DensePolynomial::new(coefficients))
    }

    fn from_dense<R: Field>(
        polynomial: &dense::DensePolynomial<R>,
        variable: Option<&Symbol<R::Domain>>,
    ) -> Result<Polynomial<R>, PolynomialFactorizationError> {
        polynomial
            .coefficients()
            .iter()
            .cloned()
            .enumerate()
            .filter(|(_, coefficient)| *coefficient != R::ZERO)
            .map(|(degree, coefficient)| {
                Ok((Self::monomial_from_degree(variable, degree)?, coefficient))
            })
            .collect()
    }

    fn monomial_from_degree<D: Set>(
        variable: Option<&Symbol<D>>,
        degree: usize,
    ) -> Result<Monomial<D>, PolynomialFactorizationError> {
        let Some(exponent) = NonZeroUsize::new(degree) else {
            return Ok(Monomial::ONE);
        };
        let variable = variable
            .cloned()
            .ok_or(PolynomialFactorizationError::MissingVariable)?;
        Ok(Monomial(BTreeMap::from([(variable, exponent)])))
    }

    fn into_indexed<R: Field>(
        polynomial: &Polynomial<R>,
        variables: &[Symbol<R::Domain>],
    ) -> multivariate::IndexedPolynomial<R> {
        let constant = (!polynomial.constant.eq(&R::ZERO))
            .then(|| (vec![0; variables.len()], polynomial.constant.clone()));
        let terms = polynomial.terms.iter().map(|(monomial, coefficient)| {
            let exponents = variables
                .iter()
                .map(|variable| {
                    monomial
                        .0
                        .get(variable)
                        .map(|exponent| exponent.get())
                        .unwrap_or(0)
                })
                .collect();
            (exponents, coefficient.clone())
        });
        multivariate::IndexedPolynomial::new(variables.len(), constant.into_iter().chain(terms))
    }

    fn from_indexed<R: Field>(
        polynomial: &multivariate::IndexedPolynomial<R>,
        variables: &[Symbol<R::Domain>],
    ) -> Polynomial<R> {
        polynomial
            .terms()
            .iter()
            .map(|(exponents, coefficient)| {
                let powers = exponents
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(index, exponent)| {
                        Some((variables[index].clone(), NonZeroUsize::new(exponent)?))
                    })
                    .collect();
                (Monomial(powers), coefficient.clone())
            })
            .collect()
    }

    fn from_dense_factorization<R: Field>(
        factorization: dense::DenseFactorization<R>,
        variable: Option<&Symbol<R::Domain>>,
    ) -> Result<PolynomialFactorization<R>, PolynomialFactorizationError> {
        let factors = factorization
            .factors
            .into_iter()
            .map(|factor| {
                Ok::<_, PolynomialFactorizationError>(PolynomialFactor {
                    polynomial: Self::from_dense(&factor.polynomial, variable)?,
                    multiplicity: factor.multiplicity,
                })
            })
            .collect::<Result<_, _>>()?;
        Ok(PolynomialFactorization {
            unit: factorization.unit,
            factors,
        })
    }

    fn from_indexed_factorization<R: Field>(
        factorization: multivariate::IndexedFactorization<R>,
        variables: &[Symbol<R::Domain>],
    ) -> PolynomialFactorization<R> {
        PolynomialFactorization {
            unit: factorization.unit,
            factors: factorization
                .factors
                .into_iter()
                .map(|factor| PolynomialFactor {
                    polynomial: Self::from_indexed(&factor.polynomial, variables),
                    multiplicity: factor.multiplicity,
                })
                .collect(),
        }
    }
}

impl<F: FiniteFactorField> Polynomial<F> {
    /// Irreducible factorization over a finite field.
    ///
    /// See <https://en.wikipedia.org/wiki/Cantor%E2%80%93Zassenhaus_algorithm>.
    pub fn factor(&self) -> Result<PolynomialFactorization<F>, PolynomialFactorizationError> {
        let variables = PolynomialFactorCodec::variables(self);
        if variables.len() <= 1 {
            let (variable, polynomial) = PolynomialFactorCodec::into_dense(self);
            return PolynomialFactorCodec::from_dense_factorization(
                polynomial.factor()?,
                variable.as_ref(),
            );
        }
        let polynomial = PolynomialFactorCodec::into_indexed(self, &variables);
        let factorization = polynomial.factor_finite_field()?;
        Ok(PolynomialFactorCodec::from_indexed_factorization(
            factorization,
            &variables,
        ))
    }
}

impl Polynomial<RationalField> {
    /// Irreducible factorization over `Q`.
    ///
    /// See <https://en.wikipedia.org/wiki/Kronecker%27s_method>.
    pub fn factor_rational(
        &self,
    ) -> Result<PolynomialFactorization<RationalField>, PolynomialFactorizationError> {
        use rational::RationalFactorizationExt;

        let variables = PolynomialFactorCodec::variables(self);
        if variables.len() <= 1 {
            let (variable, polynomial) = PolynomialFactorCodec::into_dense(self);
            return PolynomialFactorCodec::from_dense_factorization(
                polynomial.factor_rational()?,
                variable.as_ref(),
            );
        }
        let polynomial = PolynomialFactorCodec::into_indexed(self, &variables);
        let factorization = polynomial.factor_rational()?;
        Ok(PolynomialFactorCodec::from_indexed_factorization(
            factorization,
            &variables,
        ))
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::field::{PrimeField, PrimeFieldElement};
    use eqn_algebra::operator_impl::{QAdd, QMul};
    use eqn_core::set::{Q, Rational};

    use super::*;

    type F2 = PrimeField<2>;
    type Qq = (Q, QAdd, QMul);

    struct TestPolynomial;

    impl TestPolynomial {
        fn fp<const P: u64>(src: &str) -> Polynomial<PrimeField<P>> {
            src.parse().unwrap()
        }

        fn q(src: &str) -> Polynomial<Qq> {
            src.parse().unwrap()
        }
    }

    #[test]
    fn finite_field_univariate_factorization_recomposes() {
        let polynomial = TestPolynomial::fp::<3>("x^2 - 1");
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn finite_field_multivariate_factorization_recomposes() {
        let polynomial = TestPolynomial::fp::<3>("x^2 - y^2");
        let factorization = polynomial.factor().unwrap();
        let factors = factorization
            .factors
            .iter()
            .map(|factor| factor.polynomial.clone())
            .collect::<Vec<_>>();

        assert_eq!(factorization.factors.len(), 2);
        assert!(factors.contains(&TestPolynomial::fp::<3>("x - y")));
        assert!(factors.contains(&TestPolynomial::fp::<3>("x + y")));
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn finite_field_multiplicities_survive_the_public_conversion() {
        let polynomial = TestPolynomial::fp::<3>("(x + 1)^2 * (x - 1)");
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert!(
            factorization
                .factors
                .iter()
                .any(|factor| factor.multiplicity == 2)
        );
    }

    #[test]
    fn finite_extension_univariate_factorization_recomposes() {
        type F4 = crate::finite_field::FiniteField<2, 2>;
        type E4 = crate::finite_field::FiniteFieldElement<2, 2>;

        let alpha = E4::from_coefficients([PrimeFieldElement::ZERO, PrimeFieldElement::ONE]);
        let polynomial = Polynomial::<F4>::from(Symbol::new("x"))
            * Polynomial::from(Symbol::new("x"))
            + Polynomial::constant(alpha);
        let factorization = polynomial.factor().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 2);
    }

    #[test]
    fn rational_univariate_factorization_recomposes() {
        let polynomial = TestPolynomial::q("x^2 - 1");
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn rational_multiplicities_survive_the_public_conversion() {
        let polynomial = TestPolynomial::q("(x - 1)^3");
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
        assert_eq!(factorization.factors.len(), 1);
        assert_eq!(factorization.factors[0].multiplicity, 3);
    }

    #[test]
    fn rational_multivariate_factorization_recomposes() {
        let polynomial = TestPolynomial::q("x^2 - y^2");
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.factors.len(), 2);
        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn rational_coefficients_keep_their_unit() {
        let polynomial = Polynomial::<Qq>::constant(Rational {
            numerator: 3,
            denominator: 2,
        }) * TestPolynomial::q("x^2 - 1");
        let factorization = polynomial.factor_rational().unwrap();

        assert_eq!(factorization.recompose(), polynomial);
    }

    #[test]
    fn zero_polynomial_has_no_finite_factorization() {
        assert!(matches!(
            Polynomial::<F2>::ZERO.factor(),
            Err(PolynomialFactorizationError::FiniteField(
                FactorizationError::ZeroPolynomial
            ))
        ));
    }

    #[test]
    fn zero_polynomial_has_no_rational_factorization() {
        assert!(matches!(
            Polynomial::<Qq>::ZERO.factor_rational(),
            Err(PolynomialFactorizationError::Rational(
                RationalFactorizationError::ZeroPolynomial
            ))
        ));
    }
}
