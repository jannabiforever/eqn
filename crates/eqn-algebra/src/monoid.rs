use std::collections::HashSet;

use crate::op::{Associative, BinaryOperator, Commutative, Identity};
use crate::rewriter::{Expression, Rewriter, flatten};
use crate::set::Set;
use crate::symbol::Symbol;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Set;
    type Operator: BinaryOperator<Domain = Self::Domain> + Associative + Identity;

    const IDENTITY: <Self::Domain as Set>::Element = <Self::Operator as Identity>::IDENTITY;

    fn apply(
        lhs: <Self::Domain as Set>::Element,
        rhs: <Self::Domain as Set>::Element,
    ) -> <Self::Domain as Set>::Element {
        <Self::Operator as BinaryOperator>::apply(lhs, rhs)
    }
}

/// Any (domain, operator) pair forms a monoid for free.
impl<D, Op> Monoid for (D, Op)
where
    D: Set,
    Op: BinaryOperator<Domain = D> + Associative + Identity,
{
    type Domain = D;
    type Operator = Op;
}

/// An expression tree over a monoid: constants, named symbols, and n-ary
/// applications of the monoid's operator.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum MonoidExpr<M: Monoid> {
    Const(<M::Domain as Set>::Element),
    Symbol(Symbol<M::Domain>),
    Op(Vec<MonoidExpr<M>>),
}

impl<M: Monoid> Expression for MonoidExpr<M> {
    type Domain = M::Domain;

    fn degrees_of_freedom(&self) -> usize {
        let mut visited = HashSet::new();
        let mut to_visit = vec![self];

        while let Some(e) = to_visit.pop() {
            match e {
                Self::Const(_) => continue,
                Self::Symbol(s) => {
                    visited.insert(s);
                }
                Self::Op(v) => {
                    to_visit.extend(v.iter());
                }
            }
        }
        visited.len()
    }

    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        let mut to_visit = vec![self];
        while let Some(e) = to_visit.pop() {
            match e {
                Self::Const(_) => continue,
                Self::Symbol(s) if *s == sym => {
                    *e = expr.clone();
                }
                Self::Symbol(_) => continue,
                Self::Op(v) => {
                    to_visit.extend(v.iter_mut());
                }
            }
        }
    }
}

impl<M: Monoid> MonoidExpr<M> {
    /// Wraps a domain element as a constant expression.
    #[inline]
    pub const fn constant(value: <M::Domain as Set>::Element) -> Self {
        Self::Const(value)
    }
}

impl<D: Set, M: Monoid<Domain = D>> From<Symbol<D>> for MonoidExpr<M> {
    fn from(value: Symbol<D>) -> Self {
        Self::Symbol(value)
    }
}

#[derive_where::derive_where(Clone, Copy, Default)]
pub struct NonCommutativeMonoidFormatter<M> {
    _monoid_marker: std::marker::PhantomData<M>,
}

impl<M: Monoid> NonCommutativeMonoidFormatter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Monoid> Rewriter for NonCommutativeMonoidFormatter<M> {
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
pub struct CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: Commutative,
{
    _marker: std::marker::PhantomData<M>,
}

impl<M> CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: Commutative,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M> Rewriter for CommutativeMonoidFormatter<M>
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
        let simplified = NonCommutativeMonoidFormatter::new().rewrited_expr(expr);

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
        let simplified = CommutativeMonoidFormatter::new().rewrited_expr(expr);

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
