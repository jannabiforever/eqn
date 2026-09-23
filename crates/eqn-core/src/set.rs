// ================================================================================
// Set
// ================================================================================

pub use eqn_macros::Set;

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
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize
);

/// The natural numbers, including `0`.
/// TODO: big num
pub type N = u32;

/// The integers.
/// TODO: big num
pub type Z = i64;

/// A rational number in lowest terms, with a positive denominator.
/// TODO: big num
#[derive(Clone, Debug, Eq, PartialEq, Set)]
pub struct Rational {
    numerator: i64,
    denominator: i64,
}

impl Rational {
    pub const ZERO: Self = Self {
        numerator: 0,
        denominator: 1,
    };

    pub const ONE: Self = Self {
        numerator: 1,
        denominator: 1,
    };

    /// `numerator / denominator` in lowest terms. `denominator` must be
    /// nonzero.
    pub const fn new(numerator: i64, denominator: i64) -> Self {
        let divisor = Self::gcd(numerator.abs(), denominator.abs());
        let sign = if denominator < 0 { -1 } else { 1 };
        Self {
            numerator: sign * numerator / divisor,
            denominator: sign * denominator / divisor,
        }
    }

    const fn gcd(mut a: i64, mut b: i64) -> i64 {
        while b != 0 {
            let remainder = a % b;
            a = b;
            b = remainder;
        }
        a
    }

    pub const fn recip(self) -> Self {
        Self::new(self.denominator, self.numerator)
    }
}

impl std::ops::Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.numerator, self.denominator)
    }
}

impl std::ops::Add for Rational {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.denominator + other.numerator * self.denominator,
            self.denominator * other.denominator,
        )
    }
}

impl std::ops::Mul for Rational {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.numerator,
            self.denominator * other.denominator,
        )
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self::new(value, 1)
    }
}

/// Why a string is not a [`Rational`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseRationalError {
    Int(std::num::ParseIntError),
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

impl From<std::num::ParseIntError> for ParseRationalError {
    fn from(e: std::num::ParseIntError) -> Self {
        Self::Int(e)
    }
}

/// Reads an integer (`-3`) or a fraction (`3/4`).
impl std::str::FromStr for Rational {
    type Err = ParseRationalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (numerator, denominator) = match s.split_once('/') {
            Some((n, d)) => (n.parse()?, d.parse()?),
            None => (s.parse()?, 1),
        };
        if denominator == 0 {
            return Err(ParseRationalError::ZeroDenominator);
        }
        Ok(Self::new(numerator, denominator))
    }
}

/// The rational numbers.
/// TODO: big num
pub type Q = Rational;

/// represent a real number
/// NOTE: a bit hacky implementation on PartialEq / Eq
#[derive(Clone, Debug, Set)]
pub struct RealNumber(f64);

impl PartialEq for RealNumber {
    fn eq(&self, other: &Self) -> bool {
        other.0 >= self.0 && self.0 >= other.0
    }
}

impl Eq for RealNumber {}

impl std::str::FromStr for RealNumber {
    type Err = std::num::ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse().map(Self)
    }
}

/// The real numbers.
/// TODO: big num
pub type R = RealNumber;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_parse_integers_and_fractions() {
        assert_eq!("3".parse::<Rational>().unwrap(), Rational::from(3));
        assert_eq!("-3".parse::<Rational>().unwrap(), Rational::from(-3));
        assert_eq!("6/4".parse::<Rational>().unwrap(), Rational::new(3, 2));
        assert_eq!(
            "1/0".parse::<Rational>().unwrap_err(),
            ParseRationalError::ZeroDenominator
        );
        assert!("1.5".parse::<Rational>().is_err());
    }

    #[test]
    fn reals_parse_decimals() {
        assert_eq!("2.5".parse::<RealNumber>().unwrap(), RealNumber(2.5));
        assert_eq!("-1".parse::<RealNumber>().unwrap(), RealNumber(-1.0));
    }
}
