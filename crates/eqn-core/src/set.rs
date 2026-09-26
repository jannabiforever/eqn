pub use eqn_macros::Set;
use num_bigint::Sign;
use num_integer::Integer;

use crate::map::Map;

// ================================================================================
// Set
// ================================================================================

/// A set: a type whose values are its elements and whose `Eq` is equality of
/// canonical representations.
pub trait Set: Clone + Eq + std::fmt::Debug {}

/// A subset of `Superset`, given by its membership predicate.
pub trait Subset {
    type Superset: Set;

    fn contains(element: &Self::Superset) -> bool;
}

// ================================================================================
// Sets of numbers
// ================================================================================

macro_rules! impl_set {
    ($($t:ty),*) => { $(impl Set for $t {})* };
}

impl_set!(
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    num_bigint::BigUint,
    num_bigint::BigInt
);

/// The natural numbers, including `0`.
pub type N = num_bigint::BigUint;

/// The integers.
pub type Z = num_bigint::BigInt;

/// A rational number in lowest terms, with a positive denominator.
#[derive(Clone, Debug, Eq, PartialEq, Set)]
pub struct Rational {
    numerator: Z,
    denominator: Z,
}

impl Rational {
    /// `numerator / denominator` in lowest terms. `denominator` must be
    /// nonzero.
    pub fn new(numerator: Z, denominator: Z) -> Self {
        assert!(denominator != Z::ZERO, "denominator is zero");
        let divisor = numerator.gcd(&denominator);
        let numerator = numerator / &divisor;
        let denominator = denominator / divisor;
        match denominator.sign() {
            Sign::Minus => Self {
                numerator: -numerator,
                denominator: -denominator,
            },
            _ => Self {
                numerator,
                denominator,
            },
        }
    }

    /// The additive identity.
    pub fn zero() -> Self {
        Self::from(Z::ZERO)
    }

    /// The multiplicative identity.
    pub fn one() -> Self {
        Self::from(Z::from(1))
    }

    /// The multiplicative inverse. `self` must be nonzero.
    pub fn recip(self) -> Self {
        Self::new(self.denominator, self.numerator)
    }
}

impl std::ops::Neg for Q {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl std::ops::Add for Q {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::new(
            &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            self.denominator * other.denominator,
        )
    }
}

impl std::ops::Mul for Q {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.numerator,
            self.denominator * other.denominator,
        )
    }
}

impl From<Z> for Rational {
    fn from(value: Z) -> Self {
        Self {
            numerator: value,
            denominator: Z::from(1),
        }
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self::from(Z::from(value))
    }
}

impl<Z1, Z2> From<(Z1, Z2)> for Rational
where
    Z1: Into<Z>,
    Z2: Into<Z>,
{
    fn from(value: (Z1, Z2)) -> Self {
        let (numerator, denominator) = {
            let (n, d) = value;
            (n.into(), d.into())
        };

        Self::new(numerator, denominator)
    }
}

/// Why a string is not a [`Q`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseRationalError {
    Int(num_bigint::ParseBigIntError),
    ZeroDenominator,
}

impl std::fmt::Display for ParseRationalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(e) => e.fmt(f),
            Self::ZeroDenominator => f.write_str("denominator is zero"),
        }
    }
}

impl std::error::Error for ParseRationalError {}

impl From<num_bigint::ParseBigIntError> for ParseRationalError {
    fn from(e: num_bigint::ParseBigIntError) -> Self {
        Self::Int(e)
    }
}

/// Reads an integer (`-3`) or a fraction (`3/4`).
impl std::str::FromStr for Q {
    type Err = ParseRationalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (numerator, denominator) = match s.split_once('/') {
            Some((n, d)) => (n.parse()?, d.parse()?),
            None => (s.parse()?, Z::from(1)),
        };
        if denominator == Z::ZERO {
            return Err(ParseRationalError::ZeroDenominator);
        }
        Ok(Self::new(numerator, denominator))
    }
}

/// The rational numbers.
pub type Q = Rational;

/// A real number.
///
/// NOTE: equality is that of the approximation carried, which is coarser than
/// equality of the reals.
/// TODO: an exact representation.
#[derive(Clone, Debug, Set)]
pub struct R(f64);

impl PartialEq for R {
    fn eq(&self, other: &Self) -> bool {
        other.0 >= self.0 && self.0 >= other.0
    }
}

impl Eq for R {}

impl std::str::FromStr for R {
    type Err = std::num::ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self)
    }
}

// ================================================================================
// Inclusions
// ================================================================================

/// The inclusion `\mathbb{N} \hookrightarrow \mathbb{Z}`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalsInIntegers;

impl Map<N, Z> for NaturalsInIntegers {
    fn map(&self, element: N) -> Z {
        Z::from(element)
    }
}

/// The inclusion `\mathbb{Z} \hookrightarrow \mathbb{Q}`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntegersInRationals;

impl Map<Z, Q> for IntegersInRationals {
    fn map(&self, element: Z) -> Q {
        Q::from(element)
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_parse_integers_and_fractions() {
        assert_eq!("3".parse::<Rational>().unwrap(), Rational::from(3));
        assert_eq!("-3".parse::<Rational>().unwrap(), Rational::from(-3));
        assert_eq!(
            "6/4".parse::<Rational>().unwrap(),
            Rational::new(Z::from(3), Z::from(2))
        );
        assert_eq!(
            "1/0".parse::<Q>().unwrap_err(),
            ParseRationalError::ZeroDenominator
        );
        assert!("1.5".parse::<Q>().is_err());
    }

    #[test]
    fn rationals_are_held_in_lowest_terms_with_a_positive_denominator() {
        assert_eq!(
            Rational::new(Z::from(6), Z::from(4)),
            Rational::new(Z::from(3), Z::from(2))
        );
        assert_eq!(
            Rational::new(Z::from(1), Z::from(-2)),
            Rational::new(Z::from(-1), Z::from(2))
        );
        assert_eq!(Rational::new(Z::from(0), Z::from(-7)), Rational::zero());
    }

    #[test]
    fn reals_parse_decimals() {
        assert_eq!("2.5".parse::<R>().unwrap(), R(2.5));
        assert_eq!("-1".parse::<R>().unwrap(), R(-1.0));
    }

    #[test]
    fn naturals_and_integers_are_not_bounded_by_the_machine_word() {
        let power = N::from(2u32).pow(200);
        assert_eq!(&power * &power, N::from(2u32).pow(400));
        assert!(power > N::from(u128::MAX));

        let factorial = (1..=40u32).map(Z::from).product::<Z>();
        assert_eq!(&factorial / Z::from(40), (1..=39u32).map(Z::from).product());
        assert!(factorial > Z::from(i128::MAX));
    }

    #[test]
    fn rationals_add_where_machine_integers_would_overflow() {
        let half_of = |power: u32| Rational::new(Z::from(1), Z::from(2).pow(power));

        assert_eq!(half_of(100) + half_of(100), half_of(99));
        assert_eq!(
            half_of(100) + Rational::new(Z::from(1), Z::from(3).pow(100)),
            Rational::new(
                Z::from(3).pow(100) + Z::from(2).pow(100),
                Z::from(2).pow(100) * Z::from(3).pow(100)
            )
        );
    }

    #[test]
    fn the_inclusions_preserve_addition_and_multiplication() {
        for (a, b) in [(0u32, 7u32), (3, 5), (12, 12)] {
            let (a, b) = (N::from(a), N::from(b));
            assert_eq!(
                NaturalsInIntegers.map(a.clone() + b.clone()),
                NaturalsInIntegers.map(a.clone()) + NaturalsInIntegers.map(b.clone())
            );
            assert_eq!(
                NaturalsInIntegers.map(a.clone() * b.clone()),
                NaturalsInIntegers.map(a) * NaturalsInIntegers.map(b)
            );
        }

        for (a, b) in [(0, -7), (3, 5), (-12, 12)] {
            let (a, b) = (Z::from(a), Z::from(b));
            assert_eq!(
                IntegersInRationals.map(a.clone() + b.clone()),
                IntegersInRationals.map(a.clone()) + IntegersInRationals.map(b.clone())
            );
            assert_eq!(
                IntegersInRationals.map(a.clone() * b.clone()),
                IntegersInRationals.map(a) * IntegersInRationals.map(b)
            );
        }
    }
}
