use super::{AbelianGroup, Group, GroupExpr};
use crate::Flatten;
use crate::rewriter::Rewriter;
use crate::set::Set;

impl<G: Group> GroupExpr<G> {
    fn cmp_structural(&self, rhs: &Self) -> std::cmp::Ordering {
        const fn rank<G: Group>(expr: &GroupExpr<G>) -> u8 {
            match expr {
                GroupExpr::Const(_) => 0,
                GroupExpr::Symbol(_) => 1,
                GroupExpr::Inv(_) => 2,
                GroupExpr::Pow { .. } => 3,
                GroupExpr::Op(_) => 4,
            }
        }

        match (self, rhs) {
            (GroupExpr::Const(_), GroupExpr::Const(_)) => std::cmp::Ordering::Equal,
            (GroupExpr::Symbol(lhs), GroupExpr::Symbol(rhs)) => lhs.cmp(rhs),
            (GroupExpr::Inv(lhs), GroupExpr::Inv(rhs)) => lhs.cmp_structural(rhs),
            (
                GroupExpr::Pow {
                    base: lhs,
                    exponent: lhs_exponent,
                },
                GroupExpr::Pow {
                    base: rhs,
                    exponent: rhs_exponent,
                },
            ) => lhs.cmp_structural(rhs).then(lhs_exponent.cmp(rhs_exponent)),
            (GroupExpr::Op(lhs), GroupExpr::Op(rhs)) => lhs
                .iter()
                .zip(rhs)
                .map(|(lhs, rhs)| lhs.cmp_structural(rhs))
                .find(|ordering| ordering.is_ne())
                .unwrap_or(lhs.len().cmp(&rhs.len())),
            (lhs, rhs) => rank(lhs).cmp(&rank(rhs)),
        }
    }

    fn split_power(self) -> (Self, isize) {
        match self {
            GroupExpr::Inv(base) => (*base, -1),
            GroupExpr::Pow { base, exponent } => (*base, exponent),
            base => (base, 1),
        }
    }

    fn power(self, exponent: isize) -> Self {
        match exponent {
            0 => GroupExpr::Const(G::IDENTITY),
            1 => self,
            -1 => GroupExpr::Inv(Box::new(self)),
            exponent => GroupExpr::Pow {
                base: Box::new(self),
                exponent,
            },
        }
    }

    fn pow_constant(mut base: <G::Domain as Set>::Element, exponent: isize) -> Self {
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

    fn finish(mut exprs: Vec<Self>) -> Self {
        match exprs.len() {
            0 => GroupExpr::Const(G::IDENTITY),
            1 => exprs.pop().unwrap(),
            _ => GroupExpr::Op(exprs),
        }
    }

    /// Moves the expression out, leaving an allocation-free placeholder behind.
    fn take(&mut self) -> Self {
        std::mem::replace(self, GroupExpr::Op(Vec::new()))
    }

    fn split_op(self) -> Result<Vec<Self>, Self> {
        match self {
            GroupExpr::Op(inner) => Ok(inner),
            e => Err(e),
        }
    }

    /// `self` is `Inv(inner)` with `inner` normalized. Applies the inverse
    /// rules and returns whether the result needs another normalization
    /// pass.
    fn reduce_inv(&mut self) -> bool {
        let GroupExpr::Inv(inner) = self else {
            unreachable!()
        };
        match inner.take() {
            GroupExpr::Const(value) => {
                *self = GroupExpr::Const(G::inverse(value));
                false
            }
            GroupExpr::Inv(e) => {
                *self = *e;
                false
            }
            GroupExpr::Pow { base, exponent } => match exponent.checked_neg() {
                Some(exponent) => {
                    *self = GroupExpr::Pow { base, exponent };
                    true
                }
                None => {
                    **inner = GroupExpr::Pow { base, exponent };
                    false
                }
            },
            // (a * b)^-1 = b^-1 * a^-1
            GroupExpr::Op(exprs) => {
                *self = GroupExpr::Op(
                    exprs
                        .into_iter()
                        .rev()
                        .map(|e| GroupExpr::Inv(Box::new(e)))
                        .collect(),
                );
                true
            }
            e => {
                **inner = e;
                false
            }
        }
    }

    /// `self` is `Pow { base, .. }` with `base` normalized. Applies the power
    /// rules shared by every group and returns whether the result needs
    /// another normalization pass.
    fn reduce_pow(&mut self) -> bool {
        let GroupExpr::Pow { base, exponent } = self else {
            unreachable!()
        };
        let exponent = *exponent;
        if exponent == 0 {
            *self = GroupExpr::Const(G::IDENTITY);
            return false;
        }

        match (base.take(), exponent) {
            (GroupExpr::Const(base), exponent) => {
                *self = Self::pow_constant(base, exponent);
                false
            }
            (base, 1) => {
                *self = base;
                false
            }
            (base, -1) => {
                *self = GroupExpr::Inv(Box::new(base));
                true
            }
            (
                GroupExpr::Pow {
                    base: inner_base,
                    exponent: inner,
                },
                outer,
            ) => match inner.checked_mul(outer) {
                Some(exponent) => {
                    *self = GroupExpr::Pow {
                        base: inner_base,
                        exponent,
                    };
                    true
                }
                None => {
                    **base = GroupExpr::Pow {
                        base: inner_base,
                        exponent: inner,
                    };
                    false
                }
            },
            (GroupExpr::Inv(inner_base), exponent) => match exponent.checked_neg() {
                Some(exponent) => {
                    *self = GroupExpr::Pow {
                        base: inner_base,
                        exponent,
                    };
                    true
                }
                None => {
                    **base = GroupExpr::Inv(inner_base);
                    false
                }
            },
            (b, _) => {
                **base = b;
                false
            }
        }
    }

    /// Order-preserving product of normalized factors: drops identities, folds
    /// *adjacent* constants, cancels *adjacent* inverse pairs, and merges
    /// *adjacent* equal bases into one power.
    fn fold_adjacent(factors: impl Iterator<Item = Self>) -> Self {
        let mut out = Vec::new();

        for e in factors {
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

                    let (lhs, lhs_exponent) = lhs.split_power();
                    let (rhs, rhs_exponent) = rhs.split_power();
                    if lhs == rhs {
                        match lhs_exponent.checked_add(rhs_exponent) {
                            Some(exponent) if exponent != 0 => {
                                out.push(lhs.power(exponent));
                            }
                            Some(_) => {}
                            None => {
                                out.push(lhs.power(lhs_exponent));
                                out.push(rhs.power(rhs_exponent));
                            }
                        }
                    } else {
                        out.push(lhs.power(lhs_exponent));
                        out.push(rhs.power(rhs_exponent));
                    }
                }
                (None, e) => out.push(e),
            }
        }

        Self::finish(out)
    }

    /// Normalizes in place using the group laws only; factor order is
    /// preserved. Leaves are untouched, children are normalized where they
    /// sit, and only nodes whose shape changes are replaced.
    fn normalize(&mut self) {
        match self {
            GroupExpr::Const(_) | GroupExpr::Symbol(_) => {}
            GroupExpr::Inv(inner) => {
                inner.normalize();
                if self.reduce_inv() {
                    self.normalize();
                }
            }
            GroupExpr::Op(exprs) => {
                exprs.iter_mut().for_each(Self::normalize);
                *self = Self::fold_adjacent(std::mem::take(exprs).flatten(Self::split_op));
            }
            GroupExpr::Pow { base, .. } => {
                base.normalize();
                if self.reduce_pow() {
                    self.normalize();
                }
            }
        }
    }
}

impl<G: AbelianGroup> GroupExpr<G> {
    /// Abelian only: `(a * b)^n = a^n * b^n`. Returns whether it rewrote.
    fn distribute_pow(&mut self) -> bool {
        let GroupExpr::Pow { base, exponent } = self else {
            return false;
        };
        if !matches!(**base, GroupExpr::Op(_)) {
            return false;
        }
        let exponent = *exponent;
        let GroupExpr::Op(factors) = base.take() else {
            unreachable!()
        };
        *self = GroupExpr::Op(
            factors
                .into_iter()
                .map(|b| GroupExpr::Pow {
                    base: Box::new(b),
                    exponent,
                })
                .collect(),
        );
        true
    }

    /// Abelian product of normalized factors: folds *all* constants into one
    /// leading constant, sums exponents of equal bases wherever they appear,
    /// and sorts the bases structurally.
    fn collect_powers(factors: impl Iterator<Item = Self>) -> Self {
        let mut constant = G::IDENTITY;
        let mut powers: Vec<(Self, isize)> = Vec::new();

        for e in factors {
            match e {
                GroupExpr::Const(value) => constant = G::apply(constant, value),
                e => {
                    let (base, exponent) = e.split_power();
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
        powers.sort_by(|(lhs, _), (rhs, _)| lhs.cmp_structural(rhs));

        let mut out = Vec::new();
        if powers.is_empty() || constant != G::IDENTITY {
            out.push(GroupExpr::Const(constant));
        }
        out.extend(
            powers
                .into_iter()
                .map(|(base, exponent)| base.power(exponent)),
        );
        Self::finish(out)
    }

    /// [`Self::normalize`] plus the abelian laws: factors commute, so equal
    /// bases are collected globally, constants fold into one, and powers
    /// distribute over products.
    fn normalize_abelian(&mut self) {
        match self {
            GroupExpr::Const(_) | GroupExpr::Symbol(_) => {}
            GroupExpr::Inv(inner) => {
                inner.normalize_abelian();
                if self.reduce_inv() {
                    self.normalize_abelian();
                }
            }
            GroupExpr::Op(exprs) => {
                exprs.iter_mut().for_each(Self::normalize_abelian);
                *self = Self::collect_powers(std::mem::take(exprs).flatten(Self::split_op));
            }
            GroupExpr::Pow { base, .. } => {
                base.normalize_abelian();
                if self.reduce_pow() || self.distribute_pow() {
                    self.normalize_abelian();
                }
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
        expr.normalize();
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
        expr.normalize_abelian();
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

    fn assert_idempotent<R: Rewriter>(rewriter: &R, expr: R::Expr)
    where
        R::Expr: PartialEq + std::fmt::Debug + Clone,
    {
        let once = rewriter.rewrited_expr(expr);
        assert_eq!(rewriter.rewrited_expr(once.clone()), once);
    }

    #[test]
    fn normalize_is_idempotent() {
        let x = Expr::Symbol(Symbol::new("x"));
        let y = Expr::Symbol(Symbol::new("y"));
        let pow = |base: Expr, exponent| Expr::Pow {
            base: Box::new(base),
            exponent,
        };
        let inv = |e: Expr| Expr::Inv(Box::new(e));
        let inputs = [
            Expr::Const(0),
            Expr::Op(vec![]),
            pow(x.clone(), 0),
            inv(inv(x.clone())),
            pow(Expr::Op(vec![x.clone(), y.clone()]), 2),
            Expr::Op(vec![
                x.clone(),
                inv(x.clone()),
                Expr::Const(3),
                Expr::Const(-3),
                pow(x.clone(), -2),
                inv(pow(x.clone(), 2)),
                y,
                x,
            ]),
        ];
        for expr in inputs {
            assert_idempotent(&GroupRewriter::new(), expr.clone());
            assert_idempotent(&AbelianGroupRewriter::new(), expr);
        }
    }
}
