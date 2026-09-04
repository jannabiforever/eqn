use super::{Monoid, MonoidExpr};
use crate::op::Commutative;
use crate::rewriter::{Rewriter, flatten};

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
        normalize_noncommutative(expr);
    }
}

fn finish<M: Monoid>(mut exprs: Vec<MonoidExpr<M>>) -> MonoidExpr<M> {
    match exprs.len() {
        // NOTE: empty op simplifies to identity to keep the interface total.
        0 => MonoidExpr::Const(M::IDENTITY),
        1 => exprs.pop().unwrap(),
        _ => MonoidExpr::Op(exprs),
    }
}

fn normalize_noncommutative<M: Monoid>(expr: &mut MonoidExpr<M>) {
    let MonoidExpr::Op(exprs) = expr else {
        return;
    };
    exprs.iter_mut().for_each(normalize_noncommutative);

    let mut stack: Vec<MonoidExpr<M>> = Vec::with_capacity(exprs.len());
    let split = |e| match e {
        MonoidExpr::Op(inner) => Ok(inner),
        e => Err(e),
    };
    for item in flatten(std::mem::take(exprs), split) {
        if item == MonoidExpr::Const(M::IDENTITY) {
            continue;
        }
        match (item, stack.pop()) {
            (MonoidExpr::Const(s), Some(MonoidExpr::Const(t))) => {
                stack.push(MonoidExpr::Const(M::apply(t, s)))
            }
            (item, popped) => {
                stack.extend(popped);
                stack.push(item);
            }
        }
    }

    *expr = finish(stack);
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

fn normalize_commutative<M>(expr: &mut MonoidExpr<M>)
where
    M: Monoid,
    M::Operator: Commutative,
{
    let MonoidExpr::Op(exprs) = expr else {
        return;
    };
    let mut acc = M::IDENTITY;
    let mut syms = Vec::new();

    // Worklist instead of recursion: nested ops are spliced in, so no child
    // needs its own normalization pass. Visiting order is irrelevant under
    // commutativity.
    let mut work = std::mem::take(exprs);
    while let Some(e) = work.pop() {
        match e {
            MonoidExpr::Const(c) => acc = M::apply(acc, c),
            MonoidExpr::Symbol(s) => syms.push(s),
            MonoidExpr::Op(inner) => work.extend(inner),
        }
    }

    syms.sort();

    // `work` is drained; reuse its buffer for the output.
    let mut out = work;
    if syms.is_empty() || acc != M::IDENTITY {
        out.push(MonoidExpr::Const(acc));
    }
    out.extend(syms.into_iter().map(MonoidExpr::Symbol));

    *expr = finish(out);
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
}
