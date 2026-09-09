// ================================================================================
// Set traits
// ================================================================================

pub use eqn_macros::Set;

pub trait Set {
    // Ord gives expressions a total order for canonical (sorted) forms.
    type Element: Clone + Eq + std::fmt::Debug;
}

/// Alias for a set's element.
pub type Elem<S> = <S as Set>::Element;

// ================================================================================
// Set implementations
// ================================================================================

/// A set of all natural numbers (including 0)
/// TODO: big num
#[derive(Set)]
#[set(element = u32)]
pub struct N;

/// A set of all integers.
/// TODO: big num
#[derive(Set)]
#[set(element = i64)]
pub struct Z;

/// represent a rational number
/// TODO: big num
#[derive(Clone, Debug, Eq)]
pub struct Rational {
    pub numerator: i64,
    pub denominator: i64,
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

    pub const fn recip(self) -> Self {
        Self {
            numerator: self.denominator,
            denominator: self.numerator,
        }
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        self.numerator * other.denominator == self.denominator * other.numerator
    }
}

impl std::ops::Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self {
        Rational {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl std::ops::Add for Rational {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Rational {
            numerator: self.numerator * other.denominator + other.numerator * self.denominator,
            denominator: self.denominator * other.denominator,
        }
    }
}

impl std::ops::Mul for Rational {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        Rational {
            numerator: self.numerator * other.numerator,
            denominator: self.denominator * other.denominator,
        }
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self {
            numerator: value,
            denominator: 1,
        }
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
        Ok(Self {
            numerator,
            denominator,
        })
    }
}

/// A set of all rationals.
/// TODO: big num
#[derive(Clone, Set)]
#[set(element = Rational)]
pub struct Q;

/// represent a real number
/// NOTE: a bit hacky implementation on PartialEq / Eq
#[derive(Clone, Debug)]
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

/// A set of all real numbers
/// TODO: big num
#[derive(Set)]
#[set(element = RealNumber)]
pub struct R;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_parse_integers_and_fractions() {
        assert_eq!("3".parse::<Rational>().unwrap(), Rational::from(3));
        assert_eq!("-3".parse::<Rational>().unwrap(), Rational::from(-3));
        assert_eq!(
            "6/4".parse::<Rational>().unwrap(),
            Rational {
                numerator: 3,
                denominator: 2
            }
        );
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
