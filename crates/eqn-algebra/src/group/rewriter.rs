use super::{AbelianGroup, Group, GroupExpr};
use crate::flatten;
use crate::rewriter::Rewriter;
use crate::set::Set;

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

/// Moves the expression out, leaving an allocation-free placeholder behind.
fn take<G: Group>(expr: &mut GroupExpr<G>) -> GroupExpr<G> {
    std::mem::replace(expr, GroupExpr::Op(Vec::new()))
}

/// Normalizes in place: leaves are untouched, children are normalized where
/// they sit, and only nodes whose shape changes are replaced.
fn normalize<G: Group>(expr: &mut GroupExpr<G>, commutative: bool) {
    match expr {
        GroupExpr::Const(_) | GroupExpr::Symbol(_) => {}
        GroupExpr::Inv(inner) => {
            normalize(inner, commutative);
            match take(inner) {
                GroupExpr::Const(value) => *expr = GroupExpr::Const(G::inverse(value)),
                GroupExpr::Inv(e) => *expr = *e,
                GroupExpr::Pow { base, exponent } => match exponent.checked_neg() {
                    Some(exponent) => {
                        *expr = GroupExpr::Pow { base, exponent };
                        normalize(expr, commutative);
                    }
                    None => **inner = GroupExpr::Pow { base, exponent },
                },
                GroupExpr::Op(exprs) => {
                    *expr = GroupExpr::Op(
                        exprs
                            .into_iter()
                            .rev()
                            .map(|e| GroupExpr::Inv(Box::new(e)))
                            .collect(),
                    );
                    normalize(expr, commutative);
                }
                e => **inner = e,
            }
        }
        GroupExpr::Op(exprs) => {
            exprs.iter_mut().for_each(|e| normalize(e, commutative));
            let split = |e| match e {
                GroupExpr::Op(inner) => Ok(inner),
                e => Err(e),
            };
            let flat = flatten(std::mem::take(exprs), split);

            if commutative {
                let mut constant = G::IDENTITY;
                let mut powers: Vec<(GroupExpr<G>, isize)> = Vec::new();

                for e in flat {
                    match e {
                        GroupExpr::Const(value) => constant = G::apply(constant, value),
                        e => {
                            let (base, exponent) = split_power(e);
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
                *expr = finish(out);
            } else {
                let mut out = Vec::new();

                for e in flat {
                    if e == GroupExpr::Const(G::IDENTITY) {
                        continue;
                    }
                    match (out.pop(), e) {
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
                        (None, e) => out.push(e),
                    }
                }

                *expr = finish(out);
            }
        }
        GroupExpr::Pow { base, exponent } => {
            let exponent = *exponent;
            if exponent == 0 {
                *expr = GroupExpr::Const(G::IDENTITY);
                return;
            }

            normalize(base, commutative);
            match (take(base), exponent) {
                (GroupExpr::Const(base), exponent) => *expr = pow_constant::<G>(base, exponent),
                (base, 1) => *expr = base,
                (base, -1) => {
                    *expr = GroupExpr::Inv(Box::new(base));
                    normalize(expr, commutative);
                }
                (
                    GroupExpr::Pow {
                        base: inner_base,
                        exponent: inner,
                    },
                    outer,
                ) => match inner.checked_mul(outer) {
                    Some(exponent) => {
                        *expr = GroupExpr::Pow {
                            base: inner_base,
                            exponent,
                        };
                        normalize(expr, commutative);
                    }
                    None => {
                        **base = GroupExpr::Pow {
                            base: inner_base,
                            exponent: inner,
                        }
                    }
                },
                (GroupExpr::Inv(inner_base), exponent) => match exponent.checked_neg() {
                    Some(exponent) => {
                        *expr = GroupExpr::Pow {
                            base: inner_base,
                            exponent,
                        };
                        normalize(expr, commutative);
                    }
                    None => **base = GroupExpr::Inv(inner_base),
                },
                (GroupExpr::Op(exprs), exponent) if commutative => {
                    *expr = GroupExpr::Op(
                        exprs
                            .into_iter()
                            .map(|b| GroupExpr::Pow {
                                base: Box::new(b),
                                exponent,
                            })
                            .collect(),
                    );
                    normalize(expr, true);
                }
                (b, _) => **base = b,
            }
        }
    }
}

/// Canonicalizes group expressions while preserving factor order.
#[derive_where::derive_where(Default)]
pub struct GroupRewriter<G: Group> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: Group> GroupRewriter<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: Group> Rewriter for GroupRewriter<G> {
    type Expr = GroupExpr<G>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr, false);
    }
}

/// Canonicalizes group expressions using the abelian group laws, collecting
/// equal bases and distributing powers over the group operation.
#[derive_where::derive_where(Default)]
pub struct AbelianGroupRewriter<G: AbelianGroup> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: AbelianGroup> AbelianGroupRewriter<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: AbelianGroup> Rewriter for AbelianGroupRewriter<G> {
    type Expr = GroupExpr<G>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        normalize(expr, true);
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::*;
    use super::*;
    use crate::monoid::Monoid;
    use crate::symbol::Symbol;

    #[test]
    fn group_rewriter_preserves_order_and_reduces_inverses() {
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
            GroupRewriter::new().rewrited_expr(expr)
                == Expr::Op(vec![
                    Expr::Const(3),
                    Expr::Inv(Box::new(Expr::Symbol(y))),
                    Expr::Inv(Box::new(Expr::Symbol(x))),
                ])
        );
    }

    #[test]
    fn abelian_group_rewriter_sorts_and_cancels_globally() {
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

        assert!(AbelianGroupRewriter::new().rewrited_expr(expr) == Expr::Symbol(x));
    }

    #[test]
    fn only_abelian_rewriter_reduces_commutators() {
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
            GroupRewriter::new().rewrited_expr(commutator.clone())
                == Expr::Op(vec![
                    Expr::Symbol(a.clone()),
                    Expr::Symbol(b.clone()),
                    Expr::Inv(Box::new(Expr::Symbol(a))),
                    Expr::Inv(Box::new(Expr::Symbol(b))),
                ])
        );
        assert!(
            AbelianGroupRewriter::new().rewrited_expr(commutator)
                == Expr::Const(IntegerAdditionGroup::IDENTITY)
        );
    }

    #[test]
    fn group_rewriter_folds_constant_and_double_inverses() {
        let x = Symbol::new("x");
        let formatter = GroupRewriter::new();

        assert!(formatter.rewrited_expr(Expr::Inv(Box::new(Expr::Const(3)))) == Expr::Const(-3));
        assert!(
            formatter.rewrited_expr(Expr::Inv(Box::new(Expr::Inv(Box::new(Expr::Symbol(
                x.clone(),
            ))))))
                == Expr::Symbol(x)
        );
    }

    #[test]
    fn group_rewriter_normalizes_powers() {
        let x = Symbol::new("x");
        let formatter = GroupRewriter::new();

        assert!(
            formatter.rewrited_expr(Expr::Pow {
                base: Box::new(Expr::Const(3)),
                exponent: -3,
            }) == Expr::Const(-9)
        );
        assert!(
            formatter.rewrited_expr(Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: 0,
            }) == Expr::Const(0)
        );
        assert!(
            formatter.rewrited_expr(Expr::Pow {
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
            formatter.rewrited_expr(Expr::Inv(Box::new(Expr::Pow {
                base: Box::new(Expr::Symbol(x.clone())),
                exponent: 2,
            }))) == Expr::Pow {
                base: Box::new(Expr::Symbol(x)),
                exponent: -2,
            }
        );
    }

    #[test]
    fn group_rewriters_combine_powers_where_allowed() {
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
            GroupRewriter::new().rewrited_expr(non_commutative)
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
            AbelianGroupRewriter::new().rewrited_expr(abelian)
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
    fn only_abelian_rewriter_distributes_powers_over_products() {
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
            GroupRewriter::new().rewrited_expr(expr.clone())
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
            AbelianGroupRewriter::new().rewrited_expr(expr)
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
