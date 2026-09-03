use std::collections::HashSet;

use crate::formatter::{Expression, Formatter};
use crate::op::{AssociativeOperator, BinaryOperator, CommutativeOperator, IdentityOperator};
use crate::set::Set;
use crate::symbol::Symbol;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Set;
    type Operator: BinaryOperator<Domain = Self::Domain> + AssociativeOperator + IdentityOperator;

    const IDENTITY: <Self::Domain as Set>::Element = <Self::Operator as IdentityOperator>::IDENTITY;

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
    Op: BinaryOperator<Domain = D> + AssociativeOperator + IdentityOperator,
{
    type Domain = D;
    type Operator = Op;
}

/// An expression tree over a monoid: constants, named symbols, and n-ary
/// applications of the monoid's operator.
pub enum MonoidExpr<M: Monoid> {
    Const(<M::Domain as Set>::Element),
    Symbol(Symbol<M::Domain>),
    Op(Vec<MonoidExpr<M>>),
}

impl<M: Monoid> Clone for MonoidExpr<M> {
    fn clone(&self) -> Self {
        match self {
            Self::Const(e) => Self::Const(e.clone()),
            Self::Symbol(s) => Self::Symbol(s.clone()),
            Self::Op(v) => Self::Op(v.clone()),
        }
    }
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

    fn from_symbol(sym: Symbol<Self::Domain>) -> Self {
        Self::Symbol(sym)
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

/// Structural equality; no algebraic normalization (simplify first for that).
impl<M: Monoid> PartialEq for MonoidExpr<M> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(s), Self::Const(o)) => s == o,
            (Self::Symbol(s), Self::Symbol(o)) => s == o,
            (Self::Op(s), Self::Op(o)) => s == o,
            _ => false,
        }
    }
}

pub struct NonCommutativeMonoidFormatter<M> {
    _monoid_marker: std::marker::PhantomData<M>,
}

impl<M: Monoid> NonCommutativeMonoidFormatter<M> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M: Monoid> Default for NonCommutativeMonoidFormatter<M> {
    fn default() -> Self {
        Self {
            _monoid_marker: std::marker::PhantomData,
        }
    }
}

impl<M: Monoid> Formatter for NonCommutativeMonoidFormatter<M> {
    type Expr = MonoidExpr<M>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        match expr {
            MonoidExpr::Const(_) | MonoidExpr::Symbol(_) => expr,
            MonoidExpr::Op(exprs) => {
                let mut stack: Vec<MonoidExpr<M>> = Vec::new();

                for expr in exprs {
                    let items = match self.format_expr(expr) {
                        MonoidExpr::Op(inner) => inner,
                        e => vec![e],
                    };
                    for item in items {
                        if item == MonoidExpr::Const(M::IDENTITY) {
                            continue;
                        }
                        match (item, stack.pop()) {
                            (MonoidExpr::Const(s), Some(MonoidExpr::Const(t))) => {
                                stack.push(MonoidExpr::Const(M::apply(t, s)))
                            }
                            (item, popped) => {
                                if let Some(p) = popped {
                                    stack.push(p);
                                }
                                stack.push(item);
                            }
                        }
                    }
                }

                match stack.len() {
                    // NOTE: empty op simplifies to identity to keep the interface total.
                    0 => MonoidExpr::Const(M::IDENTITY),
                    1 => stack.pop().unwrap(),
                    _ => MonoidExpr::Op(stack),
                }
            }
        }
    }
}

/// Simplifies to a canonical form, additionally using commutativity:
/// all constants fold into one leading constant, and symbols sort by
/// name with multiplicity preserved.
pub struct CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: CommutativeOperator,
{
    _marker: std::marker::PhantomData<M>,
}

impl<M> CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: CommutativeOperator,
{
    pub fn new() -> Self {
        Self::default()
    }
}

impl<M> Default for CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: CommutativeOperator,
{
    fn default() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<M> Formatter for CommutativeMonoidFormatter<M>
where
    M: Monoid,
    M::Operator: CommutativeOperator,
{
    type Expr = MonoidExpr<M>;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        match expr {
            MonoidExpr::Const(_) | MonoidExpr::Symbol(_) => expr,
            MonoidExpr::Op(exprs) => {
                let mut acc = M::IDENTITY;
                let mut syms = Vec::new();

                // Worklist instead of recursion for nested ops; visiting
                // order is irrelevant under commutativity.
                let mut work = exprs;
                while let Some(expr) = work.pop() {
                    match self.format_expr(expr) {
                        MonoidExpr::Const(c) => acc = M::apply(acc, c),
                        MonoidExpr::Symbol(s) => syms.push(s),
                        MonoidExpr::Op(inner) => work.extend(inner),
                    }
                }

                syms.sort();

                let mut out = Vec::new();
                if syms.is_empty() || acc != M::IDENTITY {
                    out.push(MonoidExpr::Const(acc));
                }
                out.extend(syms.into_iter().map(MonoidExpr::Symbol));

                if out.len() == 1 {
                    out.into_iter().next().unwrap()
                } else {
                    MonoidExpr::Op(out)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::op::BinaryOperator;

    struct TestDomain;

    impl Set for TestDomain {
        type Element = i64;
    }

    struct TestOperator;

    impl BinaryOperator for TestOperator {
        type Domain = TestDomain;

        fn apply(
            a: <TestDomain as Set>::Element,
            b: <TestDomain as Set>::Element,
        ) -> <TestDomain as Set>::Element {
            a + b
        }
    }

    impl IdentityOperator for TestOperator {
        const IDENTITY: <TestDomain as Set>::Element = 0;
    }

    impl AssociativeOperator for TestOperator {}

    impl CommutativeOperator for TestOperator {}

    #[test]
    fn test_simplify_op() {
        let x = Symbol::new("x");
        let expr = MonoidExpr::<(TestDomain, TestOperator)>::Op(vec![
            MonoidExpr::Const(1),
            MonoidExpr::Const(2),
            MonoidExpr::Symbol(x.clone()),
        ]);
        let simplified = NonCommutativeMonoidFormatter::new().format_expr(expr);

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
        let simplified = CommutativeMonoidFormatter::new().format_expr(expr);

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
