use eqn_core::op::{BinaryOperator, Commutative, Inverse};
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

use crate::monoid::{Monoid, MonoidElem};

pub mod normal;
mod parse;
pub mod quotient;
pub mod rewriter;
pub mod solver;

/// A group: a set equipped with an associative binary operation, an identity
/// element, and a two-sided inverse for every element.
///
/// The inherited [`Monoid`] supplies the set, operation, and identity.
/// [`Inverse`] declares that, for every element `x`, both
/// `inverse(x) * x` and `x * inverse(x)` equal [`Monoid::identity`], where `*`
/// denotes [`Monoid::apply`]. Rust cannot verify these laws, so implementations
/// should cover them with property tests where practical.
pub trait Group: Monoid<Operator: BinaryOperator + Inverse> {
    /// Source spelling of "apply to the inverse": `a INVERSE_SYMBOL b` and
    /// `INVERSE_SYMBOL a`.
    const INVERSE_SYMBOL: &'static str = <Self::Operator as Inverse>::INVERSE_SYMBOL;

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
    use std::ops::Add;

    use eqn_core::op::{Associative, BinaryOperator};
    use eqn_core::quotient::{Congruence, NormalForm};

    use super::*;
    use crate::group::normal::NormalSubgroup;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = i64, symbol = "+", apply = Add::add, identity = 0, inverse = |a| -a, inverse_symbol = "-")]
    pub(super) struct Addition;

    pub(super) type IntegerAdditionGroup = (Addition,);

    #[derive(Clone, Copy, Debug, Eq, PartialEq, Set)]
    pub(super) struct Symmetry {
        rotation: u8,
        pub(super) reflected: bool,
    }

    impl Symmetry {
        pub(super) const fn new(rotation: u8, reflected: bool) -> Self {
            Self {
                rotation,
                reflected,
            }
        }

        const fn applied(self, rhs: Self) -> Self {
            let rhs_rotation = if self.reflected {
                (3 - rhs.rotation) % 3
            } else {
                rhs.rotation
            };
            Symmetry::new(
                (self.rotation + rhs_rotation) % 3,
                self.reflected ^ rhs.reflected,
            )
        }

        const fn identity() -> Self {
            Self::new(0, false)
        }

        const fn inversed(self) -> Self {
            let rotation = if self.reflected {
                self.rotation
            } else {
                (3 - self.rotation) % 3
            };
            Self::new(rotation, self.reflected)
        }
    }

    #[derive(Associative, BinaryOperator)]
    #[operator(domain = Symmetry, symbol = "*", apply = Symmetry::applied, identity = Symmetry::identity(), inverse = Symmetry::inversed, inverse_symbol = "/")]
    pub(super) struct Compose;

    pub(super) type D3 = (Compose,);

    pub(super) fn symmetries() -> [Symmetry; 6] {
        [
            Symmetry::new(0, false),
            Symmetry::new(1, false),
            Symmetry::new(2, false),
            Symmetry::new(0, true),
            Symmetry::new(1, true),
            Symmetry::new(2, true),
        ]
    }

    struct EvenIntegers;

    impl NormalForm<i64> for EvenIntegers {
        fn reduce(value: i64) -> i64 {
            value.rem_euclid(2)
        }
    }

    impl Congruence<Addition> for EvenIntegers {}

    impl NormalSubgroup for EvenIntegers {
        type Group = IntegerAdditionGroup;
    }

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
                IntegerAdditionGroup::identity()
            );
            assert_eq!(
                IntegerAdditionGroup::apply(value, inverse),
                IntegerAdditionGroup::identity()
            );
        }
    }

    #[test]
    fn even_integers_form_a_subgroup() {
        for value in [-10, -2, 0, 4, 12] {
            assert!(EvenIntegers::contains(&IntegerAdditionGroup::inverse(
                value
            )));
        }
    }

    #[test]
    fn reduction_mod_two_is_a_congruence_for_addition() {
        for a in -5..=5 {
            for b in -5..=5 {
                assert_eq!(
                    EvenIntegers::reduce(Addition::apply(a, b)),
                    EvenIntegers::reduce(Addition::apply(
                        EvenIntegers::reduce(a),
                        EvenIntegers::reduce(b)
                    ))
                );
            }
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
        let product = expr("inv(x) + y^2");

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
        let product = expr("x + inv(x) + (x + y)^2");

        assert_eq!(product.degrees_of_freedom(), 2);
        assert_eq!(
            product.substituted(Symbol::new("x"), &expr("4")),
            expr("4 + inv(4) + (4 + y)^2")
        );
    }
}
