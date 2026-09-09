use std::fmt;

/// An untyped syntax tree. Operators are carried by their spelling: the
/// [`Grammar`](crate::Grammar) decided how they parse, and the lowering
/// decides what they mean.
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
    /// `op a`
    Prefix(String, Box<Ast>),
    /// `a op b`. Juxtaposition appears as whichever operator the grammar
    /// assigned it.
    Infix(String, Box<Ast>, Box<Ast>),
    /// `a op`
    Postfix(String, Box<Ast>),
}

impl Ast {
    /// The text of a numeric literal, or of one under the prefix operator
    /// `negation`: `3` or `-3`.
    pub fn literal(&self, negation: &str) -> Option<String> {
        match self {
            Self::Number(text) => Some(text.clone()),
            Self::Prefix(op, inner) if op == negation => match inner.as_ref() {
                Self::Number(text) => Some(format!("-{text}")),
                _ => None,
            },
            _ => None,
        }
    }

    /// The value of an integer literal, possibly under `negation`.
    pub fn integer(&self, negation: &str) -> Option<isize> {
        self.literal(negation)?.parse().ok()
    }

    /// Flattens a left-to-right chain of infix operators into its operands.
    ///
    /// `role` classifies each operator: `None` ends the chain, `Some(false)`
    /// continues it and `Some(true)` continues it while marking the right
    /// operand as inverted (`a - b - c` is `a`, `-b`, `-c`). Parentheses are
    /// never looked through. A node that is not a chain yields itself.
    pub fn operands(self, role: impl Fn(&str) -> Option<bool>) -> Vec<(bool, Ast)> {
        fn collect(
            ast: Ast,
            role: &impl Fn(&str) -> Option<bool>,
            inverted: bool,
            out: &mut Vec<(bool, Ast)>,
        ) {
            match ast {
                Ast::Infix(op, lhs, rhs) => match role(&op) {
                    Some(inverse) => {
                        collect(*lhs, role, inverted, out);
                        collect(*rhs, role, inverted ^ inverse, out);
                    }
                    None => out.push((inverted, Ast::Infix(op, lhs, rhs))),
                },
                ast => out.push((inverted, ast)),
            }
        }

        let mut out = Vec::new();
        collect(self, &role, false, &mut out);
        out
    }
}

/// Renders the tree back into source form. Juxtaposition prints as the
/// operator it stands for.
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
            Self::Prefix(op, inner) => write!(f, "{op}{inner}"),
            Self::Infix(op, lhs, rhs) => write!(f, "{lhs} {op} {rhs}"),
            Self::Postfix(op, inner) => write!(f, "{inner}{op}"),
        }
    }
}
