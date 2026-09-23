use std::marker::PhantomData;

use crate::set::Set;

// ================================================================================
// Equivalences and normal forms
// ================================================================================

/// An equivalence relation on `X`.
///
/// Implementations must be reflexive, symmetric and transitive. Rust cannot
/// verify these laws, so implementations should cover them with tests.
pub trait Equivalence<X: Set> {
    fn equivalent(a: &X, b: &X) -> bool;
}

/// A choice of one representative in each class of an equivalence on `X`.
///
/// `reduce` must be idempotent, and `reduce(a) == reduce(b)` exactly when
/// `a` and `b` are equivalent. Rust cannot verify this, so a normal form
/// should be tested against the [`Equivalence`] it represents.
pub trait NormalForm<X: Set> {
    fn reduce(element: X) -> X;
}

// ================================================================================
// Classes
// ================================================================================

/// A class of `X` modulo `N`, held by the representative `N` chooses, so
/// equality of classes is equality of representatives.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
#[derive_where(Hash, Ord, PartialOrd; X)]
pub struct EqClass<X: Set, N: NormalForm<X>> {
    representative: X,
    #[derive_where(skip)]
    normal_form: PhantomData<N>,
}

impl<X: Set, N: NormalForm<X>> EqClass<X, N> {
    pub fn new(element: X) -> Self {
        Self {
            representative: N::reduce(element),
            normal_form: PhantomData,
        }
    }

    pub const fn representative(&self) -> &X {
        &self.representative
    }

    pub fn into_representative(self) -> X {
        self.representative
    }
}

impl<X: Set, N: NormalForm<X>> Set for EqClass<X, N> {}

#[cfg(test)]
mod tests {
    use std::hash::{DefaultHasher, Hash, Hasher};

    use super::*;
    use crate::set::Z;

    /// `x \mapsto x \bmod 2`
    struct Mod2;

    impl NormalForm<Z> for Mod2 {
        fn reduce(element: Z) -> Z {
            Z::from(i64::from(element).rem_euclid(2))
        }
    }

    /// Same parity, stated independently of the normal form.
    struct SameParity;

    impl Equivalence<Z> for SameParity {
        fn equivalent(a: &Z, b: &Z) -> bool {
            i64::from(*a - *b) % 2 == 0
        }
    }

    type Parity = EqClass<Z, Mod2>;

    #[test]
    fn classes_are_equal_exactly_when_the_relation_holds() {
        for a in (-3..=3).map(Z::from) {
            for b in (-3..=3).map(Z::from) {
                assert_eq!(
                    Parity::new(a) == Parity::new(b),
                    SameParity::equivalent(&a, &b)
                );
            }
        }
    }

    #[test]
    fn hash_and_order_agree_with_equality() {
        fn hash(class: &Parity) -> u64 {
            let mut hasher = DefaultHasher::new();
            class.hash(&mut hasher);
            hasher.finish()
        }

        for a in (-3..=3).map(Z::from) {
            for b in (-3..=3).map(Z::from) {
                let (lhs, rhs) = (Parity::new(a), Parity::new(b));

                if lhs == rhs {
                    assert_eq!(hash(&lhs), hash(&rhs));
                }
                assert_eq!(lhs == rhs, lhs.cmp(&rhs).is_eq());
            }
        }

        assert!(Parity::new(Z::from(2)) < Parity::new(Z::from(-3)));
    }

    #[test]
    fn classes_form_a_set_and_hold_a_reduced_representative() {
        fn assert_set<S: Set>() {}

        assert_set::<Parity>();
        assert_eq!(Parity::new(Z::from(7)).representative(), &Z::ONE);
        assert_eq!(Parity::new(Z::from(-4)).representative(), &Z::ZERO);
        assert_eq!(Parity::new(Z::from(5)).into_representative(), Z::from(1));
    }
}
