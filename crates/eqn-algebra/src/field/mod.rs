use crate::op::{Associative, BinaryOperator, Commutative, Inverse};
use crate::ring::{Element, Ring, SemiRing};
use crate::set::Set;

// ================================================================================
// Field
// ================================================================================

/// A field: a commutative ring whose multiplication has inverses for every
/// element except `ZERO`. `invert(ZERO)` is a contract violation, not an
/// error; the operator's `Inverse` impl is only consulted for non-zero input.
pub trait Field: Ring<Multiplication: Commutative + Inverse> {
    fn invert(a: Element<Self>) -> Element<Self> {
        <Self::Multiplication as Inverse>::inverse(a)
    }
}

/// Any ring whose multiplication is commutative and invertible is a field
/// for free.
impl<R> Field for R
where
    R: Ring,
    R::Multiplication: Commutative + Inverse,
{
}

// ================================================================================
// Rational: the canonical test field
// ================================================================================

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// `num / den` in lowest terms, `den > 0`. The canonical test field.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    pub const ZERO: Self = Self { num: 0, den: 1 };
    pub const ONE: Self = Self { num: 1, den: 1 };

    /// Normalizes sign into `num` and reduces by the gcd. Panics on `den == 0`.
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "zero denominator");
        let sign = if den < 0 { -1 } else { 1 };
        let num = num * sign;
        let den = den * sign;
        let g = gcd(num.unsigned_abs(), den.unsigned_abs()) as i64;
        Self {
            num: num / g,
            den: den / g,
        }
    }

    /// The multiplicative inverse. Panics on zero.
    pub fn recip(self) -> Self {
        assert!(self.num != 0, "reciprocal of zero");
        Self::new(self.den, self.num)
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self { num: value, den: 1 }
    }
}

impl std::ops::Add for Rational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::new(self.num * rhs.den + rhs.num * self.den, self.den * rhs.den)
    }
}

impl std::ops::Mul for Rational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self::new(self.num * rhs.num, self.den * rhs.den)
    }
}

impl std::ops::Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            num: -self.num,
            den: self.den,
        }
    }
}

// `den` is always positive, so cross-multiplication compares correctly;
// deriving `Ord` from the raw fields would rank `1/2` below `1/3`.
impl Ord for Rational {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let lhs = i128::from(self.num) * i128::from(other.den);
        let rhs = i128::from(other.num) * i128::from(self.den);
        lhs.cmp(&rhs)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

#[derive(Set)]
#[set(element = Rational)]
pub struct Rationals;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Rationals, apply = |a, b| a + b, identity = Rational::ZERO, inverse = |a| -a)]
pub struct RationalAdd;

#[derive(Associative, BinaryOperator, Commutative)]
#[operator(domain = Rationals, apply = |a, b| a * b, identity = Rational::ONE, inverse = Rational::recip)]
pub struct RationalMul;

pub struct RationalField;

impl SemiRing for RationalField {
    type Domain = Rationals;
    type Addition = RationalAdd;
    type Multiplication = RationalMul;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_normalizes() {
        assert_eq!(Rational::new(2, 4), Rational::new(1, 2));
        assert_eq!(Rational::new(1, -2), Rational::new(-1, 2));
    }

    #[test]
    fn ordering_compares_values_not_raw_fields() {
        assert!(Rational::new(1, 3) < Rational::new(1, 2));
    }

    #[test]
    fn recip_inverts() {
        assert_eq!(Rational::new(2, 3).recip(), Rational::new(3, 2));
    }

    #[test]
    #[should_panic(expected = "reciprocal of zero")]
    fn recip_of_zero_panics() {
        let _ = Rational::ZERO.recip();
    }

    #[test]
    fn field_invert_agrees_with_recip_and_multiplication() {
        let x = Rational::new(2, 3);

        assert_eq!(RationalField::invert(x), Rational::new(3, 2));
        assert_eq!(
            RationalField::multiply(x, RationalField::invert(x)),
            Rational::ONE
        );
    }
}
