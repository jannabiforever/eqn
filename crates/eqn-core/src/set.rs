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

/// A set of numbers as a type of its own, standing apart from the machine
/// type that represents it: `Z` is the integers, `i64` is the 64-bit
/// integers.
macro_rules! number_set {
    ($(#[$doc:meta])* $name:ident($repr:ty)) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Set)]
        pub struct $name($repr);

        impl $name {
            pub const ZERO: Self = Self(0);
            pub const ONE: Self = Self(1);
        }

        impl From<$repr> for $name {
            fn from(value: $repr) -> Self {
                Self(value)
            }
        }

        impl From<$name> for $repr {
            fn from(value: $name) -> Self {
                value.0
            }
        }

        impl std::str::FromStr for $name {
            type Err = std::num::ParseIntError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                s.parse().map(Self)
            }
        }

        impl std::ops::Add for $name {
            type Output = Self;

            fn add(self, other: Self) -> Self {
                Self(self.0 + other.0)
            }
        }

        impl std::ops::Mul for $name {
            type Output = Self;

            fn mul(self, other: Self) -> Self {
                Self(self.0 * other.0)
            }
        }
    };
}

number_set!(
    /// The natural numbers, including `0`.
    /// TODO: big num
    N(u32)
);

number_set!(
    /// The integers.
    /// TODO: big num
    Z(i64)
);

impl std::ops::Neg for Z {
    type Output = Self;

    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl std::ops::Sub for Z {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}

/// The rational numbers: fractions in lowest terms with a positive
/// denominator.
/// TODO: big num
#[derive(Clone, Debug, Eq, PartialEq, Set)]
pub struct Q {
    numerator: i64,
    denominator: i64,
}

impl Q {
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

impl std::ops::Neg for Q {
    type Output = Self;

    fn neg(self) -> Self {
        Self::new(-self.numerator, self.denominator)
    }
}

impl std::ops::Add for Q {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self::new(
            self.numerator * other.denominator + other.numerator * self.denominator,
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

impl From<i64> for Q {
    fn from(value: i64) -> Self {
        Self::new(value, 1)
    }
}

/// Why a string is not a [`Q`].
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
impl std::str::FromStr for Q {
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

/// The real numbers, as `f64`.
/// NOTE: a bit hacky implementation on PartialEq / Eq
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rationals_parse_integers_and_fractions() {
        assert_eq!("3".parse::<Q>().unwrap(), Q::from(3));
        assert_eq!("-3".parse::<Q>().unwrap(), Q::from(-3));
        assert_eq!("6/4".parse::<Q>().unwrap(), Q::new(3, 2));
        assert_eq!(
            "1/0".parse::<Q>().unwrap_err(),
            ParseRationalError::ZeroDenominator
        );
        assert!("1.5".parse::<Q>().is_err());
    }

    #[test]
    fn reals_parse_decimals() {
        assert_eq!("2.5".parse::<R>().unwrap(), R(2.5));
        assert_eq!("-1".parse::<R>().unwrap(), R(-1.0));
    }
}
