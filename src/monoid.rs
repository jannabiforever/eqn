use crate::domain::Domain;
use crate::op::{AssociativeOperator, CommutativeOperator, IdentityOperator};
use crate::symbol::Symbol;

/// A monoid: a domain paired with an associative operator that has an
/// identity element. Both laws are demanded as bounds, so an operator
/// must declare them to qualify.
pub trait Monoid {
    type Domain: Domain;
    type Operator: AssociativeOperator<Self::Domain> + IdentityOperator<Self::Domain>;
}

/// Any (domain, operator) pair forms a monoid for free.
impl<D: Domain, Op: AssociativeOperator<D> + IdentityOperator<D>> Monoid for (D, Op) {
    type Domain = D;
    type Operator = Op;
}

/// An expression tree over a monoid: constants, named symbols, and n-ary
/// applications of the monoid's operator.
pub enum MonoidExpr<M: Monoid> {
    Const(<M::Domain as Domain>::Element),
    Symbol(Symbol<M::Domain>),
    Op(Vec<MonoidExpr<M>>),
}

impl<M: Monoid> MonoidExpr<M> {
    /// Wraps a domain element as a constant expression.
    #[inline]
    pub const fn constant(value: <M::Domain as Domain>::Element) -> Self {
        Self::Const(value)
    }
}

impl<D: Domain, M: Monoid<Domain = D>> From<Symbol<D>> for MonoidExpr<M> {
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

impl<D, O, M> MonoidExpr<M>
where
    D: Domain,
    O: IdentityOperator<D>,
    M: Monoid<Domain = D, Operator = O>,
{
    /// Simplifies using only the monoid laws: flattens nested ops
    /// (associativity), drops identities, and folds *adjacent* constants.
    /// Symbols keep their order -- reordering would need commutativity.
    pub fn simplify(self) -> Self {
        match self {
            Self::Const(_) | Self::Symbol(_) => self,
            Self::Op(exprs) => {
                let mut stack: Vec<Self> = Vec::new();

                for expr in exprs {
                    let items = match expr.simplify() {
                        Self::Op(inner) => inner,
                        e => vec![e],
                    };
                    for item in items {
                        if item == Self::Const(O::IDENTITY) {
                            continue;
                        }
                        match (item, stack.pop()) {
                            (Self::Const(s), Some(Self::Const(t))) => {
                                stack.push(Self::Const(O::apply(t, s)))
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
                    0 => Self::Const(O::IDENTITY),
                    1 => stack.pop().unwrap(),
                    _ => Self::Op(stack),
                }
            }
        }
    }
}

impl<D, O, M> MonoidExpr<M>
where
    D: Domain,
    O: IdentityOperator<D> + CommutativeOperator<D>,
    M: Monoid<Domain = D, Operator = O>,
{
    /// Simplifies to a canonical form, additionally using commutativity:
    /// all constants fold into one leading constant, and symbols sort by
    /// name with multiplicity preserved.
    pub fn simplify_with_commutativity(self) -> Self {
        match self {
            Self::Const(_) | Self::Symbol(_) => self,
            Self::Op(exprs) => {
                let mut acc = O::IDENTITY;
                let mut syms = Vec::new();

                // Worklist instead of recursion for nested ops; visiting
                // order is irrelevant under commutativity.
                let mut work = exprs;
                while let Some(expr) = work.pop() {
                    match expr.simplify_with_commutativity() {
                        Self::Const(c) => acc = O::apply(acc, c),
                        Self::Symbol(s) => syms.push(s),
                        Self::Op(inner) => work.extend(inner),
                    }
                }

                syms.sort();

                let mut out = Vec::new();
                if syms.is_empty() || acc != O::IDENTITY {
                    out.push(Self::Const(acc));
                }
                out.extend(syms.into_iter().map(Self::Symbol));

                if out.len() == 1 {
                    out.into_iter().next().unwrap()
                } else {
                    Self::Op(out)
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

    impl Domain for TestDomain {
        type Element = i64;
    }

    struct TestOperator;

    impl BinaryOperator<TestDomain> for TestOperator {
        fn apply(
            a: <TestDomain as Domain>::Element,
            b: <TestDomain as Domain>::Element,
        ) -> <TestDomain as Domain>::Element {
            a + b
        }
    }

    impl IdentityOperator<TestDomain> for TestOperator {
        const IDENTITY: <TestDomain as Domain>::Element = 0;
    }

    impl AssociativeOperator<TestDomain> for TestOperator {}

    impl CommutativeOperator<TestDomain> for TestOperator {}

    #[test]
    fn test_simplify_op() {
        let x = Symbol::new("x");
        let expr = MonoidExpr::<(TestDomain, TestOperator)>::Op(vec![
            MonoidExpr::Const(1),
            MonoidExpr::Const(2),
            MonoidExpr::Symbol(x.clone()),
        ]);
        let simplified = expr.simplify();

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
        let simplified = expr.simplify_with_commutativity();

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
