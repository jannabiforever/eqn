use std::collections::HashSet;

use crate::formatter::{Expression, Formatter};
use crate::monoid::Monoid;
use crate::op::{BinaryOperator, CommutativeOperator, InverseOperator};
use crate::set::Set;
use crate::symbol::Symbol;

/// A group: a set equipped with an associative binary operation, an identity
/// element, and a two-sided inverse for every element.
///
/// The inherited [`Monoid`] supplies the set, operation, and identity.
/// [`InverseOperator`] declares that, for every element `x`, both
/// `inverse(x) * x` and `x * inverse(x)` equal [`Monoid::IDENTITY`], where `*`
/// denotes [`Monoid::apply`]. Rust cannot verify these laws, so implementations
/// should cover them with property tests where practical.
pub trait Group: Monoid<Operator: BinaryOperator + InverseOperator> {
    /// Returns the two-sided inverse of `value` under the group's operation.
    fn inverse(value: <Self::Domain as Set>::Element) -> <Self::Domain as Set>::Element {
        <Self::Operator as InverseOperator>::inverse(value)
    }
}

/// Classifies every monoid whose operation supplies inverses as a group.
impl<M> Group for M
where
    M: Monoid,
    M::Operator: InverseOperator,
{
}

/// An abelian group: a group whose operation is commutative.
///
/// In addition to the group laws, `x * y` must equal `y * x` for every pair of
/// elements in the set. [`CommutativeOperator`] declares this law.
pub trait AbelianGroup: Group + Monoid<Operator: CommutativeOperator> {}

/// Classifies every group with a commutative operation as an abelian group.
impl<G> AbelianGroup for G
where
    G: Group,
    G::Operator: CommutativeOperator,
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

fn cmp_structural<G: Group>(lhs: &GroupExpr<G>, rhs: &GroupExpr<G>) -> std::cmp::Ordering {
    const fn rank<G: Group>(expr: &GroupExpr<G>) -> u8 {
        match expr {
            GroupExpr::Const(_) => 0,
            GroupExpr::Symbol(_) => 1,
            GroupExpr::Inv(_) => 2,
            GroupExpr::Pow { .. } => 3,
            GroupExpr::Op(_) => 4,
        }
    }

    match (lhs, rhs) {
        (GroupExpr::Const(_), GroupExpr::Const(_)) => std::cmp::Ordering::Equal,
        (GroupExpr::Symbol(lhs), GroupExpr::Symbol(rhs)) => lhs.cmp(rhs),
        (GroupExpr::Inv(lhs), GroupExpr::Inv(rhs)) => cmp_structural(lhs, rhs),
        (
            GroupExpr::Pow {
                base: lhs,
                exponent: lhs_exponent,
            },
            GroupExpr::Pow {
                base: rhs,
                exponent: rhs_exponent,
            },
        ) => cmp_structural(lhs, rhs).then(lhs_exponent.cmp(rhs_exponent)),
        (GroupExpr::Op(lhs), GroupExpr::Op(rhs)) => lhs
            .iter()
            .zip(rhs)
            .map(|(lhs, rhs)| cmp_structural(lhs, rhs))
            .find(|ordering| ordering.is_ne())
            .unwrap_or(lhs.len().cmp(&rhs.len())),
        (lhs, rhs) => rank(lhs).cmp(&rank(rhs)),
    }
}

fn split_power<G: Group>(expr: GroupExpr<G>) -> (GroupExpr<G>, isize) {
    match expr {
        GroupExpr::Inv(base) => (*base, -1),
        GroupExpr::Pow { base, exponent } => (*base, exponent),
        base => (base, 1),
    }
}

fn power<G: Group>(base: GroupExpr<G>, exponent: isize) -> GroupExpr<G> {
    match exponent {
        0 => GroupExpr::Const(G::IDENTITY),
        1 => base,
        -1 => GroupExpr::Inv(Box::new(base)),
        exponent => GroupExpr::Pow {
            base: Box::new(base),
            exponent,
        },
    }
}

fn pow_constant<G: Group>(mut base: <G::Domain as Set>::Element, exponent: isize) -> GroupExpr<G> {
    if exponent.is_negative() {
        base = G::inverse(base);
    }

    let mut exponent = exponent.unsigned_abs();
    let mut value = G::IDENTITY;
    while exponent != 0 {
        if exponent % 2 == 1 {
            value = G::apply(value, base.clone());
        }
        exponent /= 2;
        if exponent != 0 {
            base = G::apply(base.clone(), base);
        }
    }
    GroupExpr::Const(value)
}

fn finish<G: Group>(mut exprs: Vec<GroupExpr<G>>) -> GroupExpr<G> {
    match exprs.len() {
        0 => GroupExpr::Const(G::IDENTITY),
        1 => exprs.pop().unwrap(),
        _ => GroupExpr::Op(exprs),
    }
}

fn normalize<G: Group>(expr: GroupExpr<G>, commutative: bool) -> GroupExpr<G> {
    match expr {
        GroupExpr::Const(_) | GroupExpr::Symbol(_) => expr,
        GroupExpr::Inv(expr) => match normalize(*expr, commutative) {
            GroupExpr::Const(value) => GroupExpr::Const(G::inverse(value)),
            GroupExpr::Inv(expr) => *expr,
            GroupExpr::Pow { base, exponent } => match exponent.checked_neg() {
                Some(exponent) => normalize(GroupExpr::Pow { base, exponent }, commutative),
                None => GroupExpr::Inv(Box::new(GroupExpr::Pow { base, exponent })),
            },
            GroupExpr::Op(exprs) => normalize(
                GroupExpr::Op(
                    exprs
                        .into_iter()
                        .rev()
                        .map(|expr| GroupExpr::Inv(Box::new(expr)))
                        .collect(),
                ),
                commutative,
            ),
            expr => GroupExpr::Inv(Box::new(expr)),
        },
        GroupExpr::Op(exprs) => {
            let mut flat = Vec::new();
            for expr in exprs {
                match normalize(expr, commutative) {
                    GroupExpr::Op(inner) => flat.extend(inner),
                    expr => flat.push(expr),
                }
            }

            if commutative {
                let mut constant = G::IDENTITY;
                let mut powers: Vec<(GroupExpr<G>, isize)> = Vec::new();

                for expr in flat {
                    match expr {
                        GroupExpr::Const(value) => constant = G::apply(constant, value),
                        expr => {
                            let (base, exponent) = split_power(expr);
                            if let Some((_, current)) =
                                powers.iter_mut().find(|(candidate, _)| *candidate == base)
                                && let Some(exponent) = current.checked_add(exponent)
                            {
                                *current = exponent;
                            } else {
                                powers.push((base, exponent));
                            }
                        }
                    }
                }

                powers.retain(|(_, exponent)| *exponent != 0);
                powers.sort_by(|(lhs, _), (rhs, _)| cmp_structural(lhs, rhs));

                let mut out = Vec::new();
                if powers.is_empty() || constant != G::IDENTITY {
                    out.push(GroupExpr::Const(constant));
                }
                out.extend(
                    powers
                        .into_iter()
                        .map(|(base, exponent)| power(base, exponent)),
                );
                finish(out)
            } else {
                let mut out = Vec::new();

                for expr in flat {
                    if expr == GroupExpr::Const(G::IDENTITY) {
                        continue;
                    }
                    match (out.pop(), expr) {
                        (Some(GroupExpr::Const(lhs)), GroupExpr::Const(rhs)) => {
                            let value = G::apply(lhs, rhs);
                            if value != G::IDENTITY {
                                out.push(GroupExpr::Const(value));
                            }
                        }
                        (Some(lhs), rhs) => {
                            let inverse_pair = matches!(
                                (&lhs, &rhs),
                                (GroupExpr::Inv(lhs), rhs) | (rhs, GroupExpr::Inv(lhs))
                                    if lhs.as_ref() == rhs
                            );
                            if inverse_pair {
                                continue;
                            }

                            let (lhs, lhs_exponent) = split_power(lhs);
                            let (rhs, rhs_exponent) = split_power(rhs);
                            if lhs == rhs {
                                match lhs_exponent.checked_add(rhs_exponent) {
                                    Some(exponent) if exponent != 0 => {
                                        out.push(power(lhs, exponent));
                                    }
                                    Some(_) => {}
                                    None => {
                                        out.push(power(lhs, lhs_exponent));
                                        out.push(power(rhs, rhs_exponent));
                                    }
                                }
                            } else {
                                out.push(power(lhs, lhs_exponent));
                                out.push(power(rhs, rhs_exponent));
                            }
                        }
                        (None, expr) => out.push(expr),
                    }
                }

                finish(out)
            }
        }
        GroupExpr::Pow { base, exponent } => {
            if exponent == 0 {
                return GroupExpr::Const(G::IDENTITY);
            }

            let base = normalize(*base, commutative);
            match (base, exponent) {
                (GroupExpr::Const(base), exponent) => pow_constant::<G>(base, exponent),
                (base, 1) => base,
                (base, -1) => normalize(GroupExpr::Inv(Box::new(base)), commutative),
                (
                    GroupExpr::Pow {
                        base,
                        exponent: inner,
                    },
                    outer,
                ) => match inner.checked_mul(outer) {
                    Some(exponent) => normalize(GroupExpr::Pow { base, exponent }, commutative),
                    None => GroupExpr::Pow {
                        base: Box::new(GroupExpr::Pow {
                            base,
                            exponent: inner,
                        }),
                        exponent: outer,
                    },
                },
                (GroupExpr::Inv(base), exponent) => match exponent.checked_neg() {
                    Some(exponent) => normalize(GroupExpr::Pow { base, exponent }, commutative),
                    None => GroupExpr::Pow {
                        base: Box::new(GroupExpr::Inv(base)),
                        exponent,
                    },
                },
                (GroupExpr::Op(exprs), exponent) if commutative => normalize(
                    GroupExpr::Op(
                        exprs
                            .into_iter()
                            .map(|base| GroupExpr::Pow {
                                base: Box::new(base),
                                exponent,
                            })
                            .collect(),
                    ),
                    true,
                ),
                (base, exponent) => GroupExpr::Pow {
                    base: Box::new(base),
                    exponent,
                },
            }
        }
    }
}

/// Canonicalizes group expressions while preserving factor order.
#[derive_where::derive_where(Default)]
pub struct GroupFormatter<G: Group> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: Group> GroupFormatter<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: Group> Formatter for GroupFormatter<G> {
    type Expr = GroupExpr<G>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        normalize(expr, false)
    }
}

/// Canonicalizes group expressions using the abelian group laws, collecting
/// equal bases and distributing powers over the group operation.
#[derive_where::derive_where(Default)]
pub struct AbelianGroupFormatter<G: AbelianGroup> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: AbelianGroup> AbelianGroupFormatter<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: AbelianGroup> Formatter for AbelianGroupFormatter<G> {
    type Expr = GroupExpr<G>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        normalize(expr, true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{AssociativeOperator, BinaryOperator, IdentityOperator};

    struct IntegerSet;

    impl Set for IntegerSet {
        type Element = i64;
    }

    #[derive(AssociativeOperator, CommutativeOperator)]
    struct Addition;

    impl BinaryOperator for Addition {
        type Domain = IntegerSet;

        fn apply(a: i64, b: i64) -> i64 {
            a + b
        }
    }

    impl IdentityOperator for Addition {
        const IDENTITY: i64 = 0;
    }

    impl InverseOperator for Addition {
        fn inverse(a: i64) -> i64 {
            -a
        }
    }

    type IntegerAdditionGroup = (IntegerSet, Addition);

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

    type Expr = GroupExpr<IntegerAdditionGroup>;

    #[test]
    fn group_formatter_preserves_order_and_reduces_inverses() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let expr = Expr::Op(vec![
            Expr::Const(1),
            Expr::Const(2),
            Expr::Symbol(x.clone()),
            Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
            Expr::Inv(Box::new(Expr::Op(vec![
                Expr::Symbol(x.clone()),
                Expr::Symbol(y.clone()),
            ]))),
        ]);

        assert!(
            GroupFormatter::new().format_expr(expr)
                == Expr::Op(vec![
                    Expr::Const(3),
                    Expr::Inv(Box::new(Expr::Symbol(y))),
                    Expr::Inv(Box::new(Expr::Symbol(x))),
                ])
        );
    }

    #[test]
    fn abelian_group_formatter_sorts_and_cancels_globally() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let expr = Expr::Op(vec![
            Expr::Symbol(y.clone()),
            Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
            Expr::Const(2),
            Expr::Symbol(x.clone()),
            Expr::Inv(Box::new(Expr::Symbol(y))),
            Expr::Symbol(x.clone()),
            Expr::Const(-2),
        ]);

        assert!(AbelianGroupFormatter::new().format_expr(expr) == Expr::Symbol(x));
    }

    #[test]
    fn only_abelian_formatter_reduces_commutators() {
        let a = Symbol::new("a");
        let b = Symbol::new("b");
        let commutator = Expr::Op(vec![
            Expr::Symbol(a.clone()),
            Expr::Symbol(b.clone()),
            Expr::Pow {
                base: Box::new(Expr::Symbol(a.clone())),
                exponent: -1,
            },
            Expr::Pow {
                base: Box::new(Expr::Symbol(b.clone())),
                exponent: -1,
            },
        ]);

        assert!(
            GroupFormatter::new().format_expr(commutator.clone())
                == Expr::Op(vec![
                    Expr::Symbol(a.clone()),
                    Expr::Symbol(b.clone()),
                    Expr::Inv(Box::new(Expr::Symbol(a))),
                    Expr::Inv(Box::new(Expr::Symbol(b))),
                ])
        );
        assert!(
            AbelianGroupFormatter::new().format_expr(commutator)
                == Expr::Const(IntegerAdditionGroup::IDENTITY)
        );
    }

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

    #[test]
    fn group_formatter_folds_constant_and_double_inverses() {
        let x = Symbol::new("x");
        let formatter = GroupFormatter::new();

        assert!(formatter.format_expr(Expr::Inv(Box::new(Expr::Const(3)))) == Expr::Const(-3));
        assert!(
            formatter.format_expr(Expr::Inv(Box::new(Expr::Inv(Box::new(Expr::Symbol(
                x.clone(),
            ))))))
                == Expr::Symbol(x)
        );
    }

    #[test]
    fn group_formatter_normalizes_powers() {
        let x = Symbol::new("x");
        let formatter = GroupFormatter::new();

        assert!(
            formatter.format_expr(Expr::Pow {
                base: Box::new(Expr::Const(3)),
                exponent: -3,
            }) == Expr::Const(-9)
        );
        assert!(
            formatter.format_expr(Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: 0,
            }) == Expr::Const(0)
        );
        assert!(
            formatter.format_expr(Expr::Pow {
                base: Box::new(Expr::Pow {
                    base: Box::new(Expr::Symbol(x.clone())),
                    exponent: 3,
                }),
                exponent: -2,
            }) == Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: -6,
            }
        );
        assert!(
            formatter.format_expr(Expr::Inv(Box::new(Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: 2,
            }))) == Expr::Pow {
                base: Box::new(Expr::Symbol(x)),
                exponent: -2,
            }
        );
    }

    #[test]
    fn group_formatters_combine_powers_where_allowed() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");

        let non_commutative = Expr::Op(vec![
            Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: 2,
            },
            Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: -3,
            },
            Expr::Symbol(y.clone()),
            Expr::Symbol(x.clone()),
        ]);
        assert!(
            GroupFormatter::new().format_expr(non_commutative)
                == Expr::Op(vec![
                    Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
                    Expr::Symbol(y.clone()),
                    Expr::Symbol(x.clone()),
                ])
        );

        let abelian = Expr::Op(vec![
            Expr::Pow {
                base: Box::new(Expr::Symbol(y.clone())),
                exponent: 2,
            },
            Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: -3,
            },
            Expr::Symbol(x.clone()),
            Expr::Symbol(y.clone()),
        ]);
        assert!(
            AbelianGroupFormatter::new().format_expr(abelian)
                == Expr::Op(vec![
                    Expr::Pow {
                        base: Box::new(Expr::Symbol(x)),
                        exponent: -2,
                    },
                    Expr::Pow {
                        base: Box::new(Expr::Symbol(y)),
                        exponent: 3,
                    },
                ])
        );
    }

    #[test]
    fn only_abelian_formatter_distributes_powers_over_products() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let expr = Expr::Pow {
            base: Box::new(Expr::Op(vec![
                Expr::Const(2),
                Expr::Symbol(y.clone()),
                Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
            ])),
            exponent: 3,
        };

        assert!(
            GroupFormatter::new().format_expr(expr.clone())
                == Expr::Pow {
                    base: Box::new(Expr::Op(vec![
                        Expr::Const(2),
                        Expr::Symbol(y.clone()),
                        Expr::Inv(Box::new(Expr::Symbol(x.clone()))),
                    ])),
                    exponent: 3,
                }
        );
        assert!(
            AbelianGroupFormatter::new().format_expr(expr)
                == Expr::Op(vec![
                    Expr::Const(6),
                    Expr::Pow {
                        base: Box::new(Expr::Symbol(x)),
                        exponent: -3,
                    },
                    Expr::Pow {
                        base: Box::new(Expr::Symbol(y)),
                        exponent: 3,
                    },
                ])
        );
    }
}
