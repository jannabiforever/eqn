use std::str::FromStr;

use eqn_parser::{Assoc, Ast, FromAst, Grammar, ParseError};

use crate::rewriter::{ExprDom, Expression};
use crate::symbol::Symbol;

/// The proposition `lhs = rhs` between two expressions over one set. Which
/// symbol is the unknown is chosen when the equation is solved; every other
/// symbol is a parameter.
// NOTE: std derive, because derive_where refuses a bound on the bare type
// parameter and these bounds are exactly what std derive adds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Equation<E: Expression> {
    pub lhs: E,
    pub rhs: E,
}

impl<E: Expression> Equation<E> {
    pub fn new(lhs: E, rhs: E) -> Self {
        Self { lhs, rhs }
    }

    pub fn substitute(&mut self, sym: Symbol<ExprDom<E>>, expr: &E) {
        self.lhs.substitute(sym.clone(), expr);
        self.rhs.substitute(sym, expr);
    }

    pub fn substituted(mut self, sym: Symbol<ExprDom<E>>, expr: &E) -> Self {
        self.substitute(sym, expr);
        self
    }

    /// The values of `unknown` that satisfy the equation, as `solver`
    /// describes them.
    pub fn solve_for<S>(self, unknown: &Symbol<ExprDom<E>>, solver: &S) -> SolutionSet<E>
    where
        S: Solver<Expr = E>,
    {
        solver.solve(self, unknown)
    }

    fn has_equals_sign(ast: &Ast) -> bool {
        match ast {
            Ast::Number(_) | Ast::Ident(_) => false,
            Ast::Call(_, args) => args.iter().any(Self::has_equals_sign),
            Ast::Group(inner) | Ast::Prefix(_, inner) | Ast::Postfix(_, inner) => {
                Self::has_equals_sign(inner)
            }
            Ast::Infix(op, lhs, rhs) => {
                op == "=" || Self::has_equals_sign(lhs) || Self::has_equals_sign(rhs)
            }
        }
    }
}

/// A subset of the domain, as a solver describes it. For an equation with
/// unknown `x`, a solver returns the set `{x : lhs = rhs}` exactly, as a
/// function of the other symbols. It may describe that set coarsely, never
/// wrongly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SolutionSet<E: Expression> {
    /// The values of the listed expressions and nothing else, each listed
    /// once. Empty when nothing solves the equation.
    Finite(Vec<E>),
    /// Every element of the domain.
    All,
    /// The set `{x : lhs = rhs}` of an equation equivalent to the input,
    /// when the solver can say no more about it.
    Condition(Equation<E>),
}

/// A method of solving an equation for one unknown, the counterpart of
/// [`Rewriter`](crate::rewriter::Rewriter).
pub trait Solver {
    type Expr: Expression;

    /// The set of values of `unknown` that satisfy `equation`.
    fn solve(
        &self,
        equation: Equation<Self::Expr>,
        unknown: &Symbol<ExprDom<Self::Expr>>,
    ) -> SolutionSet<Self::Expr>;
}

/// `lhs = rhs`, each side in the syntax of `E`. `=` has the lowest
/// precedence, so `x + a = b` is the equation between `x + a` and `b`. An
/// equation has exactly one `=`.
impl<E: Expression + FromAst> FromAst for Equation<E> {
    fn grammar() -> anyhow::Result<Grammar> {
        E::grammar()?.infix("=", 0, Assoc::Left)
    }

    fn from_ast(ast: Ast) -> Result<Self, ParseError> {
        match ast {
            Ast::Infix(op, lhs, rhs)
                if op == "=" && !Self::has_equals_sign(&lhs) && !Self::has_equals_sign(&rhs) =>
            {
                Ok(Self::new(E::from_ast(*lhs)?, E::from_ast(*rhs)?))
            }
            ast if Self::has_equals_sign(&ast) => Err(ParseError::new(
                "`=` must be the outermost operator of an equation",
            )),
            _ => Err(ParseError::new(
                "an equation needs `=` between its two sides",
            )),
        }
    }
}

impl<E: Expression + FromAst> FromStr for Equation<E> {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}
