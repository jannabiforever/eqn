use std::collections::HashSet;

use crate::monoid::Monoid;
use crate::op::{BinaryOperator, Commutative, Inverse};
use crate::rewriter::Expression;
use crate::set::Set;
use crate::symbol::Symbol;

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
    fn inverse(value: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element {
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
    Const(<G::Domain as Set>::Element),
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

    fn degrees_of_freedom(&self) -> usize {
        let mut symbols = HashSet::new();
        let mut expressions = vec![self];

        while let Some(expr) = expressions.pop() {
            match expr {
                Self::Const(_) => {}
                Self::Symbol(symbol) => {
                    symbols.insert(symbol);
                }
                Self::Inv(expr) | Self::Pow { base: expr, .. } => expressions.push(expr),
                Self::Op(exprs) => expressions.extend(exprs),
            }
        }
        symbols.len()
    }

    fn substitute(&mut self, symbol: Symbol<Self::Domain>, replacement: &Self) {
        let mut expressions = vec![self];

        while let Some(expr) = expressions.pop() {
            match expr {
                Self::Const(_) => {}
                Self::Symbol(candidate) if *candidate == symbol => *expr = replacement.clone(),
                Self::Symbol(_) => {}
                Self::Inv(expr) | Self::Pow { base: expr, .. } => expressions.push(expr),
                Self::Op(exprs) => expressions.extend(exprs),
            }
        }
    }
}

mod rewriter;
pub use rewriter::{AbelianGroupRewriter, GroupRewriter};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{Associative, BinaryOperator};

    #[derive(Set)]
    #[set(element = i64)]
    pub(super) struct IntegerSet;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = IntegerSet, apply = |a, b| a + b, identity = 0, inverse = |a| -a)]
    pub(super) struct Addition;

    pub(super) type IntegerAdditionGroup = (IntegerSet, Addition);

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

    #[test]
    fn group_expression_supports_substitution() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let expr = Expr::Op(vec![
            Expr::Symbol(x.clone()),
            Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
            Expr::Pow {
                base: Box::new(Expr::Op(vec![
                    Expr::Symbol(x.clone()),
                    Expr::Symbol(y.clone()),
                ])),
                exponent: 2,
            },
        ]);

        assert_eq!(expr.degrees_of_freedom(), 2);
        assert!(
            expr.substituted(x, &Expr::Const(4))
                == Expr::Op(vec![
                    Expr::Const(4),
                    Expr::Inv(Box::new(Expr::Const(4))),
                    Expr::Pow {
                        base: Box::new(Expr::Op(vec![Expr::Const(4), Expr::Symbol(y),])),
                        exponent: 2,
                    },
                ])
        );
    }
}
