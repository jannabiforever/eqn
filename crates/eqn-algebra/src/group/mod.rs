use eqn_core::op::{BinaryOperator, Commutative, Inverse};
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

use crate::monoid::{Monoid, MonoidElem, Submonoid};

mod normal;
mod parse;
mod quotient;
mod rewriter;

// Re-exports
pub use normal::NormalSubgroup;
pub use quotient::{Coset, Cosets, QuotientGroup, QuotientOp};
pub use rewriter::{AbelianGroupRewriter, GroupRewriter};

/// A group: a set equipped with an associative binary operation, an identity
/// element, and a two-sided inverse for every element.
///
/// The inherited [`Monoid`] supplies the set, operation, and identity.
/// [`Inverse`] declares that, for every element `x`, both
/// `inverse(x) * x` and `x * inverse(x)` equal [`Monoid::IDENTITY`], where `*`
/// denotes [`Monoid::apply`]. Rust cannot verify these laws, so implementations
/// should cover them with property tests where practical.
pub trait Group: Monoid<Operator: BinaryOperator + Inverse> {
    /// Returns the two-sided inverse of `value` under the group's operation.
    fn inverse(value: MonoidElem<Self>) -> MonoidElem<Self> {
        <Self::Operator as Inverse>::inverse(value)
    }
}

/// Classifies every monoid whose operation supplies inverses as a group.
impl<M> Group for M
where
    M: Monoid,
    M::Operator: Inverse,
{
}

/// A submonoid of a group that is closed under inverses.
pub trait Subgroup: Submonoid<Parent: Group> {}

/// An abelian group: a group whose operation is commutative.
///
/// In addition to the group laws, `x * y` must equal `y * x` for every pair of
/// elements in the set. [`Commutative`] declares this law.
pub trait AbelianGroup: Group + Monoid<Operator: Commutative> {}

/// Classifies every group with a commutative operation as an abelian group.
impl<G> AbelianGroup for G
where
    G: Group,
    G::Operator: Commutative,
{
}

/// An expression tree over a group. `Inv` is the operation that distinguishes
/// it from a [`crate::monoid::MonoidExpr`].
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum GroupExpr<G: Group> {
    Const(MonoidElem<G>),
    Symbol(Symbol<G::Domain>),
    Inv(Box<GroupExpr<G>>),
    Op(Vec<GroupExpr<G>>),
    Pow {
        base: Box<GroupExpr<G>>,
        exponent: isize,
    },
}

impl<D: Set, G: Group<Domain = D>> From<Symbol<D>> for GroupExpr<G> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

impl<G: Group> Expression for GroupExpr<G> {
    type Domain = G::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Inv(inner) | Self::Pow { base: inner, .. } => std::slice::from_ref(inner),
            Self::Op(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Inv(inner) | Self::Pow { base: inner, .. } => std::slice::from_mut(inner),
            Self::Op(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::op::{Associative, BinaryOperator};

    use super::*;

    #[derive(Set)]
    #[set(element = i64)]
    pub(super) struct IntegerSet;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = IntegerSet, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
    pub(super) struct Addition;

    pub(super) type IntegerAdditionGroup = (IntegerSet, Addition);

    struct EvenIntegers;

    impl Submonoid for EvenIntegers {
        type Parent = IntegerAdditionGroup;

        fn contains(value: &MonoidElem<Self::Parent>) -> bool {
            value % 2 == 0
        }
    }

    impl Subgroup for EvenIntegers {}

    #[test]
    fn invertible_monoid_is_a_group() {
        assert_eq!(IntegerAdditionGroup::inverse(7), -7);
    }

    #[test]
    fn inverse_satisfies_both_group_laws() {
        for value in [-10, -1, 0, 1, 10] {
            let inverse = IntegerAdditionGroup::inverse(value);

            assert_eq!(
                IntegerAdditionGroup::apply(inverse, value),
                IntegerAdditionGroup::IDENTITY
            );
            assert_eq!(
                IntegerAdditionGroup::apply(value, inverse),
                IntegerAdditionGroup::IDENTITY
            );
        }
    }

    #[test]
    fn even_integers_form_a_subgroup() {
        fn assert_subgroup<S: Subgroup>() {}

        assert_subgroup::<EvenIntegers>();
        assert!(EvenIntegers::contains(&IntegerAdditionGroup::IDENTITY));

        for value in [-10, -2, 0, 4, 12] {
            assert!(EvenIntegers::contains(&IntegerAdditionGroup::inverse(
                value
            )));
        }
    }

    #[test]
    fn abelian_group_operator_is_commutative() {
        for lhs in [-10, -1, 0, 1, 10] {
            for rhs in [-10, -1, 0, 1, 10] {
                assert_eq!(
                    IntegerAdditionGroup::apply(lhs, rhs),
                    IntegerAdditionGroup::apply(rhs, lhs)
                );
            }
        }
    }

    pub(super) type Expr = GroupExpr<IntegerAdditionGroup>;

    pub(super) fn expr(src: &str) -> Expr {
        src.parse().unwrap()
    }

    #[test]
    fn descendants_are_preorder_left_to_right() {
        let (x, y) = (expr("x"), expr("y"));
        let (inv, pow) = (expr("inv(x)"), expr("y^2"));
        let product = expr("inv(x) * y^2");

        assert_eq!(product.children(), [inv.clone(), pow.clone()]);
        assert_eq!(
            product.descendants().collect::<Vec<_>>(),
            [&inv, &x, &pow, &y]
        );
        assert_eq!(product.degrees_of_freedom(), 2);

        let mut product = product;
        let mut seen = vec![];
        let mut walk = product.descendants_mut();
        while let Some(e) = walk.next() {
            seen.push(e.clone());
            if matches!(e, Expr::Pow { .. }) {
                walk.skip_children();
            }
        }
        assert_eq!(seen, [inv, x, pow]);
    }

    #[test]
    fn group_expression_supports_substitution() {
        let product = expr("x * inv(x) * (x * y)^2");

        assert_eq!(product.degrees_of_freedom(), 2);
        assert_eq!(
            product.substituted(Symbol::new("x"), &expr("4")),
            expr("4 * inv(4) * (4 * y)^2")
        );
    }
}
