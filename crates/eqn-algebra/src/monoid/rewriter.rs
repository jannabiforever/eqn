use eqn_core::op::Commutative;
use eqn_core::rewriter::Rewriter;

use super::{Monoid, MonoidExpr};
use crate::flatten;

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
    use eqn_core::op::{Associative, BinaryOperator};
    use eqn_core::set::Set;

    use super::*;

    #[derive(Set)]
    #[set(element = i64)]
    struct TestDomain;

    #[derive(Associative, BinaryOperator, Commutative)]
    #[operator(domain = TestDomain, apply = |a, b| a + b, identity = 0)]
    struct TestOperator;

    type Expr = MonoidExpr<(TestDomain, TestOperator)>;

    fn expr(src: &str) -> Expr {
        src.parse().unwrap()
    }

    #[test]
    fn test_simplify_op() {
        let simplified = NonCommutativeMonoidRewriter::new().rewrited_expr(expr("1 + 2 + x"));
        assert_eq!(simplified, expr("3 + x"));
    }

    #[test]
    fn test_simplify_with_commutativity() {
        let simplified = CommutativeMonoidRewriter::new()
            .rewrited_expr(expr("1 + (2 + y) + 0 + (x + 3) + 4 + x"));
        assert_eq!(simplified, expr("10 + x + x + y"));
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
        let inputs = [
            expr("0"),
            expr("x"),
            Expr::Op(vec![]),
            expr("1 + (2 + y) + 0 + (x + 3) + x"),
        ];
        for expr in inputs {
            assert_idempotent(&NonCommutativeMonoidRewriter::new(), expr.clone());
            assert_idempotent(&CommutativeMonoidRewriter::new(), expr);
        }
    }
}
