use std::fmt;
use std::str::FromStr;

use crate::{ParseError, parse_ast};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Wedge,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Pow => "^",
            Self::Wedge => "∧",
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnaryOp {
    Neg,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Neg => "-",
        })
    }
}

/// An untyped syntax tree. See the [crate docs](crate) for the grammar.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ast {
    /// A numeric literal, kept as written so the lowering decides how to
    /// read it.
    Number(String),
    Ident(String),
    /// `f(a, b, ...)`
    Call(String, Vec<Ast>),
    /// A parenthesized expression.
    Group(Box<Ast>),
    Unary(UnaryOp, Box<Ast>),
    /// Juxtaposition (`a b`) is [`BinaryOp::Mul`].
    Binary(BinaryOp, Box<Ast>, Box<Ast>),
}

impl Ast {
    /// The text of a possibly negated numeric literal: `3` or `-3`.
    pub fn literal(&self) -> Option<String> {
        match self {
            Self::Number(text) => Some(text.clone()),
            Self::Unary(UnaryOp::Neg, inner) => match inner.as_ref() {
                Self::Number(text) => Some(format!("-{text}")),
                _ => None,
            },
            _ => None,
        }
    }

    /// The value of a possibly negated integer literal.
    pub fn integer(&self) -> Option<isize> {
        self.literal()?.parse().ok()
    }

    /// Flattens a left-to-right chain of operators into its operands.
    ///
    /// `role` classifies each operator: `None` ends the chain, `Some(false)`
    /// continues it and `Some(true)` continues it while marking the right
    /// operand as inverted (`a - b - c` is `a`, `-b`, `-c`). Parentheses are
    /// never looked through. A node that is not a chain yields itself.
    pub fn operands(self, role: impl Fn(BinaryOp) -> Option<bool>) -> Vec<(bool, Ast)> {
        fn collect(
            ast: Ast,
            role: &impl Fn(BinaryOp) -> Option<bool>,
            inverted: bool,
            out: &mut Vec<(bool, Ast)>,
        ) {
            match ast {
                Ast::Binary(op, lhs, rhs) => match role(op) {
                    Some(inverse) => {
                        collect(*lhs, role, inverted, out);
                        collect(*rhs, role, inverted ^ inverse, out);
                    }
                    None => out.push((inverted, Ast::Binary(op, lhs, rhs))),
                },
                ast => out.push((inverted, ast)),
            }
        }

        let mut out = Vec::new();
        collect(self, &role, false, &mut out);
        out
    }
}

impl FromStr for Ast {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_ast(s)
    }
}

/// Renders the tree back into source form. Juxtaposition prints as `*`.
impl fmt::Display for Ast {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Number(text) | Self::Ident(text) => f.write_str(text),
            Self::Call(name, args) => {
                write!(f, "{name}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    arg.fmt(f)?;
                }
                f.write_str(")")
            }
            Self::Group(inner) => write!(f, "({inner})"),
            Self::Unary(op, inner) => write!(f, "{op}{inner}"),
            Self::Binary(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
        }
    }
}
