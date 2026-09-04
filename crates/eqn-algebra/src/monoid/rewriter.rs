use super::{Monoid, MonoidExpr};
use crate::flatten;
use crate::op::Commutative;
use crate::rewriter::Rewriter;

// ================================================================================
// Normalization engine
// ================================================================================

fn finish<M: Monoid>(mut exprs: Vec<MonoidExpr<M>>) -> MonoidExpr<M> {
    match exprs.len() {
        // NOTE: empty op simplifies to identity to keep the interface total.
        0 => MonoidExpr::Const(M::IDENTITY),
        1 => exprs.pop().unwrap(),
        _ => MonoidExpr::Op(exprs),
    }
}

fn split_op<M: Monoid>(expr: MonoidExpr<M>) -> Result<Vec<MonoidExpr<M>>, MonoidExpr<M>> {
    match expr {
        MonoidExpr::Op(inner) => Ok(inner),
        e => Err(e),
    }
}

/// Order-preserving product of normalized factors: drops identities and
/// folds *adjacent* constants.
fn fold_adjacent<M: Monoid>(factors: impl Iterator<Item = MonoidExpr<M>>) -> MonoidExpr<M> {
    let mut out: Vec<MonoidExpr<M>> = Vec::new();

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

    finish(out)
}

/// Commutative product of normalized factors: *all* constants fold into one
/// leading constant, and symbols sort by name with multiplicity preserved.
fn collect_symbols<M>(factors: impl Iterator<Item = MonoidExpr<M>>) -> MonoidExpr<M>
where
    M: Monoid,
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

    finish(out)
}

/// Normalizes in place using the monoid laws only; factor order is
/// preserved. Leaves are untouched, children are normalized where they sit,
/// and only nodes whose shape changes are replaced.
fn normalize<M: Monoid>(expr: &mut MonoidExpr<M>) {
    let MonoidExpr::Op(exprs) = expr else {
        return;
    };
    exprs.iter_mut().for_each(normalize);
    *expr = fold_adjacent(flatten(std::mem::take(exprs), split_op));
}

/// [`normalize`] plus commutativity: constants fold globally and symbols
/// sort.
fn normalize_commutative<M>(expr: &mut MonoidExpr<M>)
where
    M: Monoid,
    M::Operator: Commutative,
{
    let MonoidExpr::Op(exprs) = expr else {
        return;
    };
    exprs.iter_mut().for_each(normalize_commutative);
    *expr = collect_symbols(flatten(std::mem::take(exprs), split_op));
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
        normalize(expr);
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
        normalize_commutative(expr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::{Associative, BinaryOperator};
    use crate::set::Set;
    use crate::symbol::Symbol;

    #[derive(Set)]
    #[set(element = i64)]
    struct TestDomain;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, apply = |a, b| a + b, identity = 0)]
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
        R::Expr: PartialEq + std::fmt::Debug,
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
