//! A Pratt parser over the token stream. Binding powers, low to high: sums,
//! wedges, products (including juxtaposition), prefix minus, powers.

use crate::ParseError;
use crate::ast::{Ast, BinaryOp, UnaryOp};
use crate::lexer::{Token, tokenize};

const SUM: (u8, u8) = (1, 2);
const WEDGE: (u8, u8) = (3, 4);
const PRODUCT: (u8, u8) = (5, 6);
const PREFIX: u8 = 7;
const POWER: (u8, u8) = (10, 9);

/// Parses `src` into an [`Ast`].
pub fn parse_ast(src: &str) -> Result<Ast, ParseError> {
    let mut parser = Parser {
        tokens: tokenize(src)?,
        pos: 0,
        end: src.len(),
    };
    let ast = parser.expr(0)?;
    match parser.peek() {
        Some((token, at)) => Err(ParseError::at(at, format!("unexpected `{token}`"))),
        None => Ok(ast),
    }
}

struct Parser {
    tokens: Vec<(Token, usize)>,
    pos: usize,
    end: usize,
}

impl Parser {
    fn peek(&self) -> Option<(&Token, usize)> {
        self.tokens.get(self.pos).map(|(token, at)| (token, *at))
    }

    fn next(&mut self) -> Option<(Token, usize)> {
        let item = self.tokens.get(self.pos).cloned();
        self.pos += 1;
        item
    }

    /// The offset an error about the *next* token should point at.
    fn here(&self) -> usize {
        self.peek().map_or(self.end, |(_, at)| at)
    }

    fn expect(&mut self, want: Token) -> Result<(), ParseError> {
        match self.next() {
            Some((token, _)) if token == want => Ok(()),
            Some((token, at)) => Err(ParseError::at(
                at,
                format!("expected `{want}`, found `{token}`"),
            )),
            None => Err(ParseError::at(
                self.end,
                format!("expected `{want}`, found end of input"),
            )),
        }
    }

    fn expr(&mut self, min_bp: u8) -> Result<Ast, ParseError> {
        let mut lhs = self.primary()?;

        while let Some((token, _)) = self.peek() {
            let (op, (lbp, rbp), explicit) = match token {
                Token::Plus => (BinaryOp::Add, SUM, true),
                Token::Minus => (BinaryOp::Sub, SUM, true),
                Token::Wedge => (BinaryOp::Wedge, WEDGE, true),
                Token::Star => (BinaryOp::Mul, PRODUCT, true),
                Token::Slash => (BinaryOp::Div, PRODUCT, true),
                Token::Caret => (BinaryOp::Pow, POWER, true),
                // Juxtaposition: an atom directly after an expression.
                Token::Number(_) | Token::Ident(_) | Token::LParen => {
                    (BinaryOp::Mul, PRODUCT, false)
                }
                Token::RParen | Token::Comma => break,
            };
            if lbp < min_bp {
                break;
            }
            if explicit {
                self.next();
            }
            let rhs = self.expr(rbp)?;
            lhs = Ast::Binary(op, Box::new(lhs), Box::new(rhs));
        }

        Ok(lhs)
    }

    fn primary(&mut self) -> Result<Ast, ParseError> {
        let Some((token, at)) = self.next() else {
            return Err(ParseError::at(
                self.end,
                "expected an expression, found end of input",
            ));
        };
        match token {
            Token::Number(text) => Ok(Ast::Number(text)),
            Token::Ident(name) => match self.peek() {
                Some((Token::LParen, _)) => {
                    self.next();
                    let args = self.arguments()?;
                    Ok(Ast::Call(name, args))
                }
                _ => Ok(Ast::Ident(name)),
            },
            Token::LParen => {
                let inner = self.expr(0)?;
                self.expect(Token::RParen)?;
                Ok(Ast::Group(Box::new(inner)))
            }
            Token::Minus => {
                let inner = self.expr(PREFIX)?;
                Ok(Ast::Unary(UnaryOp::Neg, Box::new(inner)))
            }
            token => Err(ParseError::at(
                at,
                format!("expected an expression, found `{token}`"),
            )),
        }
    }

    /// Call arguments after the opening parenthesis, through the closing one.
    fn arguments(&mut self) -> Result<Vec<Ast>, ParseError> {
        let mut args = Vec::new();
        if let Some((Token::RParen, _)) = self.peek() {
            self.next();
            return Ok(args);
        }
        loop {
            args.push(self.expr(0)?);
            match self.next() {
                Some((Token::Comma, _)) => continue,
                Some((Token::RParen, _)) => return Ok(args),
                Some((token, at)) => {
                    return Err(ParseError::at(
                        at,
                        format!("expected `,` or `)`, found `{token}`"),
                    ));
                }
                None => {
                    return Err(ParseError::at(
                        self.here(),
                        "expected `,` or `)`, found end of input",
                    ));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn num(text: &str) -> Ast {
        Ast::Number(text.into())
    }

    fn id(name: &str) -> Ast {
        Ast::Ident(name.into())
    }

    fn bin(op: BinaryOp, lhs: Ast, rhs: Ast) -> Ast {
        Ast::Binary(op, Box::new(lhs), Box::new(rhs))
    }

    fn neg(inner: Ast) -> Ast {
        Ast::Unary(UnaryOp::Neg, Box::new(inner))
    }

    fn group(inner: Ast) -> Ast {
        Ast::Group(Box::new(inner))
    }

    #[test]
    fn products_bind_tighter_than_sums() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("1 + 2 * x").unwrap(),
            bin(Add, num("1"), bin(Mul, num("2"), id("x")))
        );
        assert_eq!(
            parse_ast("a - b / c").unwrap(),
            bin(Sub, id("a"), bin(Div, id("b"), id("c")))
        );
    }

    #[test]
    fn sums_and_products_are_left_associative() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("a - b + c").unwrap(),
            bin(Add, bin(Sub, id("a"), id("b")), id("c"))
        );
        assert_eq!(
            parse_ast("a / b * c").unwrap(),
            bin(Mul, bin(Div, id("a"), id("b")), id("c"))
        );
    }

    #[test]
    fn powers_are_right_associative_and_tightest() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("x ^ 2 ^ 3").unwrap(),
            bin(Pow, id("x"), bin(Pow, num("2"), num("3")))
        );
        assert_eq!(
            parse_ast("2 * x ^ 2").unwrap(),
            bin(Mul, num("2"), bin(Pow, id("x"), num("2")))
        );
    }

    #[test]
    fn prefix_minus_sits_between_products_and_powers() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("-x ^ 2").unwrap(),
            neg(bin(Pow, id("x"), num("2")))
        );
        assert_eq!(
            parse_ast("-2 * x").unwrap(),
            bin(Mul, neg(num("2")), id("x"))
        );
        assert_eq!(
            parse_ast("2 * -x").unwrap(),
            bin(Mul, num("2"), neg(id("x")))
        );
        assert_eq!(
            parse_ast("x ^ -2").unwrap(),
            bin(Pow, id("x"), neg(num("2")))
        );
        assert_eq!(parse_ast("--x").unwrap(), neg(neg(id("x"))));
    }

    #[test]
    fn juxtaposition_is_multiplication() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("2 x y").unwrap(),
            bin(Mul, bin(Mul, num("2"), id("x")), id("y"))
        );
        assert_eq!(
            parse_ast("2 x ^ 2").unwrap(),
            bin(Mul, num("2"), bin(Pow, id("x"), num("2")))
        );
        assert_eq!(
            parse_ast("2(x + 1)").unwrap(),
            bin(Mul, num("2"), group(bin(Add, id("x"), num("1"))))
        );
    }

    #[test]
    fn wedge_sits_between_sums_and_products() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("x * y ∧ d(x) + z").unwrap(),
            bin(
                Add,
                bin(
                    Wedge,
                    bin(Mul, id("x"), id("y")),
                    Ast::Call("d".into(), vec![id("x")])
                ),
                id("z")
            )
        );
        assert_eq!(parse_ast("a ∧ b").unwrap(), parse_ast("a /\\ b").unwrap());
    }

    #[test]
    fn parentheses_are_kept() {
        use BinaryOp::*;

        assert_eq!(
            parse_ast("(a + b) + c").unwrap(),
            bin(Add, group(bin(Add, id("a"), id("b"))), id("c"))
        );
        assert_eq!(parse_ast("((x))").unwrap(), group(group(id("x"))));
    }

    #[test]
    fn calls_take_comma_separated_arguments() {
        assert_eq!(
            parse_ast("f(x, 2 + y) g()").unwrap(),
            bin(
                BinaryOp::Mul,
                Ast::Call(
                    "f".into(),
                    vec![id("x"), bin(BinaryOp::Add, num("2"), id("y"))]
                ),
                Ast::Call("g".into(), vec![])
            )
        );
    }

    #[test]
    fn literals_and_integers() {
        assert_eq!(parse_ast("-3").unwrap().literal().as_deref(), Some("-3"));
        assert_eq!(parse_ast("2.5").unwrap().literal().as_deref(), Some("2.5"));
        assert_eq!(parse_ast("-(3)").unwrap().literal(), None);
        assert_eq!(parse_ast("-12").unwrap().integer(), Some(-12));
        assert_eq!(parse_ast("2.5").unwrap().integer(), None);
        assert_eq!(parse_ast("x").unwrap().integer(), None);
    }

    #[test]
    fn operands_flatten_chains_but_not_groups() {
        let sum = |op| match op {
            BinaryOp::Add => Some(false),
            BinaryOp::Sub => Some(true),
            _ => None,
        };
        let operands = parse_ast("a - b + (c - d) - e * f").unwrap().operands(sum);
        assert_eq!(
            operands,
            vec![
                (false, id("a")),
                (true, id("b")),
                (false, group(bin(BinaryOp::Sub, id("c"), id("d")))),
                (true, bin(BinaryOp::Mul, id("e"), id("f"))),
            ]
        );
        assert_eq!(
            parse_ast("x").unwrap().operands(sum),
            vec![(false, id("x"))]
        );
    }

    #[test]
    fn displays_source_form() {
        for src in ["1 + 2 * x", "-(x + 1) ^ -2", "f(x, y) * (z)", "a ∧ d(b)"] {
            assert_eq!(parse_ast(src).unwrap().to_string(), src);
        }
        assert_eq!(parse_ast("2 x").unwrap().to_string(), "2 * x");
    }

    #[test]
    fn reports_errors_with_offsets() {
        assert_eq!(
            parse_ast("").unwrap_err(),
            ParseError::at(0, "expected an expression, found end of input")
        );
        assert_eq!(
            parse_ast("x +").unwrap_err(),
            ParseError::at(3, "expected an expression, found end of input")
        );
        assert_eq!(
            parse_ast("* x").unwrap_err(),
            ParseError::at(0, "expected an expression, found `*`")
        );
        assert_eq!(
            parse_ast("(x + 1").unwrap_err(),
            ParseError::at(6, "expected `)`, found end of input")
        );
        assert_eq!(
            parse_ast("x + 1)").unwrap_err(),
            ParseError::at(5, "unexpected `)`")
        );
        assert_eq!(
            parse_ast("f(x y").unwrap_err(),
            ParseError::at(5, "expected `,` or `)`, found end of input")
        );
        assert_eq!(
            parse_ast("f(x; y)").unwrap_err(),
            ParseError::at(3, "unexpected character `;`")
        );
    }
}
