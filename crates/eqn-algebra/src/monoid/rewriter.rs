use super::{Monoid, MonoidExpr};
use crate::Flatten;
use crate::op::Commutative;
use crate::rewriter::Rewriter;

// ================================================================================
// Normalization engine
// ================================================================================

impl<M: Monoid> MonoidExpr<M> {
    fn finish(mut exprs: Vec<Self>) -> Self {
        match exprs.len() {
            // NOTE: empty op simplifies to identity to keep the interface total.
            0 => MonoidExpr::Const(M::IDENTITY),
            1 => exprs.pop().unwrap(),
            _ => MonoidExpr::Op(exprs),
        }
    }

    fn split_op(self) -> Result<Vec<Self>, Self> {
        match self {
            MonoidExpr::Op(inner) => Ok(inner),
            e => Err(e),
        }
    }

    /// Order-preserving product of normalized factors: drops identities and
    /// folds *adjacent* constants.
    fn fold_adjacent(factors: impl Iterator<Item = Self>) -> Self {
        let mut out: Vec<Self> = Vec::new();

        for item in factors {
            if item == MonoidExpr::Const(M::IDENTITY) {
                continue;
            }
            match (item, out.pop()) {
                (MonoidExpr::Const(s), Some(MonoidExpr::Const(t))) => {
                    out.push(MonoidExpr::Const(M::apply(t, s)))
                }
                (item, popped) => {
                    out.extend(popped);
                    out.push(item);
                }
            }
        }

        Self::finish(out)
    }

    /// Commutative product of normalized factors: *all* constants fold into one
    /// leading constant, and symbols sort by name with multiplicity preserved.
    fn collect_symbols(factors: impl Iterator<Item = Self>) -> Self
    where
        M::Operator: Commutative,
    {
        let mut acc = M::IDENTITY;
        let mut syms = Vec::new();

        for item in factors {
            match item {
                MonoidExpr::Const(c) => acc = M::apply(acc, c),
                MonoidExpr::Symbol(s) => syms.push(s),
                // Children are normalized, so a nested op was already spliced.
                MonoidExpr::Op(_) => unreachable!(),
            }
        }

        syms.sort();

        let mut out = Vec::new();
        if syms.is_empty() || acc != M::IDENTITY {
            out.push(MonoidExpr::Const(acc));
        }
        out.extend(syms.into_iter().map(MonoidExpr::Symbol));

        Self::finish(out)
    }

    /// Normalizes in place using the monoid laws only; factor order is
    /// preserved. Leaves are untouched, children are normalized where they sit,
    /// and only nodes whose shape changes are replaced.
    fn normalize(&mut self) {
        let MonoidExpr::Op(exprs) = self else {
            return;
        };
        exprs.iter_mut().for_each(Self::normalize);
        *self = Self::fold_adjacent(std::mem::take(exprs).flatten(Self::split_op));
    }

    /// [`Self::normalize`] plus commutativity: constants fold globally and
    /// symbols sort.
    fn normalize_commutative(&mut self)
    where
        M::Operator: Commutative,
    {
        let MonoidExpr::Op(exprs) = self else {
            return;
        };
        exprs.iter_mut().for_each(Self::normalize_commutative);
        *self = Self::collect_symbols(std::mem::take(exprs).flatten(Self::split_op));
    }
}

// ================================================================================
// Formatters
// ================================================================================

/// Canonicalizes monoid expressions while preserving factor order.
#[derive_where::derive_where(Clone, Copy, Default)]
pub struct NonCommutativeMonoidRewriter<M> {
    _monoid_marker: std::marker::PhantomData<M>,
}

impl<M: Monoid> NonCommutativeMonoidRewriter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Monoid> Rewriter for NonCommutativeMonoidRewriter<M> {
    type Expr = MonoidExpr<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        expr.normalize();
    }
}

/// Simplifies to a canonical form, additionally using commutativity:
/// all constants fold into one leading constant, and symbols sort by
/// name with multiplicity preserved.
#[derive_where::derive_where(Clone, Copy, Default)]
pub struct CommutativeMonoidRewriter<M>
where
    M: Monoid,
    M::Operator: Commutative,
{
    _marker: std::marker::PhantomData<M>,
}

impl<M> CommutativeMonoidRewriter<M>
where
    M: Monoid,
    M::Operator: Commutative,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M> Rewriter for CommutativeMonoidRewriter<M>
where
    M: Monoid,
    M::Operator: Commutative,
{
    type Expr = MonoidExpr<M>;

    fn rewrite_expr(&self, expr: &mut Self::Expr) {
        expr.normalize_commutative();
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Add;

    use super::*;
    use crate::op::{Associative, BinaryOperator};
    use crate::set::Set;
    use crate::symbol::Symbol;

    #[derive(Set)]
    #[set(element = i64)]
    struct TestDomain;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, apply = Add::add, identity = 0)]
    struct TestOperator;

    #[test]
    fn test_simplify_op() {
        let x = Symbol::new("x");
        let expr = MonoidExpr::<(TestDomain, TestOperator)>::Op(vec![
            MonoidExpr::Const(1),
            MonoidExpr::Const(2),
            MonoidExpr::Symbol(x.clone()),
        ]);
        let simplified = NonCommutativeMonoidRewriter::new().rewrited_expr(expr);

        assert!(simplified == MonoidExpr::Op(vec![MonoidExpr::Const(3), MonoidExpr::Symbol(x),]));
    }

    #[test]
    fn test_simplify_with_commutativity() {
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let expr = MonoidExpr::<(TestDomain, TestOperator)>::Op(vec![
            MonoidExpr::Const(1),
            MonoidExpr::Op(vec![MonoidExpr::Const(2), MonoidExpr::Symbol(y.clone())]),
            MonoidExpr::Const(0),
            MonoidExpr::Op(vec![MonoidExpr::Symbol(x.clone()), MonoidExpr::Const(3)]),
            MonoidExpr::Const(4),
            MonoidExpr::Symbol(x.clone()),
        ]);
        let simplified = CommutativeMonoidRewriter::new().rewrited_expr(expr);

        assert!(
            simplified
                == MonoidExpr::Op(vec![
                    MonoidExpr::Const(10),
                    MonoidExpr::Symbol(x.clone()),
                    MonoidExpr::Symbol(x),
                    MonoidExpr::Symbol(y),
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
        type Expr = MonoidExpr<(TestDomain, TestOperator)>;
        let x = Symbol::new("x");
        let y = Symbol::new("y");
        let inputs = [
            Expr::Const(0),
            Expr::Symbol(x.clone()),
            Expr::Op(vec![]),
            Expr::Op(vec![
                Expr::Const(1),
                Expr::Op(vec![Expr::Const(2), Expr::Symbol(y)]),
                Expr::Const(0),
                Expr::Op(vec![Expr::Symbol(x.clone()), Expr::Const(3)]),
                Expr::Symbol(x),
            ]),
        ];
        for expr in inputs {
            assert_idempotent(&NonCommutativeMonoidRewriter::new(), expr.clone());
            assert_idempotent(&CommutativeMonoidRewriter::new(), expr);
        }
    }
}
