//! A Pratt parser over the token stream, driven by a [`Grammar`].

use crate::ast::Ast;
use crate::lexer::{Token, tokenize};
use crate::{Grammar, ParseError};

/// Parses `src` into an [`Ast`] using `grammar`'s operators.
pub fn parse_ast(src: &str, grammar: &Grammar) -> Result<Ast, ParseError> {
    let mut parser = Parser {
        tokens: tokenize(src, grammar)?,
        pos: 0,
        end: src.len(),
        grammar,
    };
    let ast = parser.expr(0)?;
    match parser.peek() {
        Some((token, at)) => Err(ParseError::at(at, format!("unexpected `{token}`"))),
        None => Ok(ast),
    }
}

struct Parser<'g> {
    tokens: Vec<(Token, usize)>,
    pos: usize,
    end: usize,
    grammar: &'g Grammar,
}

/// What the token after a complete operand does to it.
enum Continuation {
    Postfix(String, u16),
    Infix {
        op: String,
        powers: (u16, u16),
        /// Juxtaposition has no token to consume.
        explicit: bool,
    },
    End,
}

impl Parser<'_> {
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

    fn continuation(&self) -> Continuation {
        match self.peek() {
            Some((Token::Op(symbol), _)) => {
                if let Some(power) = self.grammar.postfix_power(symbol) {
                    Continuation::Postfix(symbol.clone(), power)
                } else if let Some(powers) = self.grammar.infix_powers(symbol) {
                    Continuation::Infix {
                        op: symbol.clone(),
                        powers,
                        explicit: true,
                    }
                } else {
                    Continuation::End
                }
            }
            Some((Token::Number(_) | Token::Ident(_) | Token::LParen, _)) => {
                match self.grammar.juxtaposition_powers() {
                    Some((symbol, powers)) => Continuation::Infix {
                        op: symbol.to_owned(),
                        powers,
                        explicit: false,
                    },
                    None => Continuation::End,
                }
            }
            Some((Token::RParen | Token::Comma, _)) | None => Continuation::End,
        }
    }

    fn expr(&mut self, min_power: u16) -> Result<Ast, ParseError> {
        let mut lhs = self.primary()?;

        loop {
            match self.continuation() {
                Continuation::Postfix(op, power) => {
                    if power < min_power {
                        break;
                    }
                    self.next();
                    lhs = Ast::Postfix(op, Box::new(lhs));
                }
                Continuation::Infix {
                    op,
                    powers: (left, right),
                    explicit,
                } => {
                    if left < min_power {
                        break;
                    }
                    if explicit {
                        self.next();
                    }
                    let rhs = self.expr(right)?;
                    lhs = Ast::Infix(op, Box::new(lhs), Box::new(rhs));
                }
                Continuation::End => break,
            }
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
            Token::Op(symbol) => match self.grammar.prefix_power(&symbol) {
                Some(power) => {
                    let inner = self.expr(power)?;
                    Ok(Ast::Prefix(symbol, Box::new(inner)))
                }
                None => Err(ParseError::at(
                    at,
                    format!("expected an expression, found `{symbol}`"),
                )),
            },
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
    use crate::Assoc;

    /// The usual arithmetic table, plus `!` postfix and `⊕` infix.
    fn grammar() -> Grammar {
        Grammar::new()
            .infix("+", 1, Assoc::Left)
            .infix("-", 1, Assoc::Left)
            .infix("⊕", 1, Assoc::Left)
            .infix("*", 2, Assoc::Left)
            .infix("/", 2, Assoc::Left)
            .juxtaposition("*")
            .prefix("-", 3)
            .infix("^", 4, Assoc::Right)
            .postfix("!", 5)
    }

    fn parse(src: &str) -> Ast {
        parse_ast(src, &grammar()).unwrap()
    }

    fn error(src: &str) -> ParseError {
        parse_ast(src, &grammar()).unwrap_err()
    }

    fn num(text: &str) -> Ast {
        Ast::Number(text.into())
    }

    fn id(name: &str) -> Ast {
        Ast::Ident(name.into())
    }

    fn infix(op: &str, lhs: Ast, rhs: Ast) -> Ast {
        Ast::Infix(op.into(), Box::new(lhs), Box::new(rhs))
    }

    fn neg(inner: Ast) -> Ast {
        Ast::Prefix("-".into(), Box::new(inner))
    }

    fn group(inner: Ast) -> Ast {
        Ast::Group(Box::new(inner))
    }

    #[test]
    fn higher_precedence_binds_tighter() {
        assert_eq!(
            parse("1 + 2 * x"),
            infix("+", num("1"), infix("*", num("2"), id("x")))
        );
        assert_eq!(
            parse("a - b / c"),
            infix("-", id("a"), infix("/", id("b"), id("c")))
        );
        assert_eq!(
            parse("a ⊕ b * c"),
            infix("⊕", id("a"), infix("*", id("b"), id("c")))
        );
    }

    #[test]
    fn left_associative_operators_chain_leftwards() {
        assert_eq!(
            parse("a - b + c"),
            infix("+", infix("-", id("a"), id("b")), id("c"))
        );
        assert_eq!(
            parse("a / b * c"),
            infix("*", infix("/", id("a"), id("b")), id("c"))
        );
    }

    #[test]
    fn right_associative_operators_chain_rightwards() {
        assert_eq!(
            parse("x ^ 2 ^ 3"),
            infix("^", id("x"), infix("^", num("2"), num("3")))
        );
        assert_eq!(
            parse("2 * x ^ 2"),
            infix("*", num("2"), infix("^", id("x"), num("2")))
        );
    }

    #[test]
    fn prefix_operators_take_their_precedence() {
        assert_eq!(parse("-x ^ 2"), neg(infix("^", id("x"), num("2"))));
        assert_eq!(parse("-2 * x"), infix("*", neg(num("2")), id("x")));
        assert_eq!(parse("2 * -x"), infix("*", num("2"), neg(id("x"))));
        assert_eq!(parse("x ^ -2"), infix("^", id("x"), neg(num("2"))));
        assert_eq!(parse("--x"), neg(neg(id("x"))));
    }

    #[test]
    fn postfix_operators_bind_tightest_here() {
        let fact = |inner| Ast::Postfix("!".into(), Box::new(inner));
        assert_eq!(parse("n! + 1"), infix("+", fact(id("n")), num("1")));
        assert_eq!(parse("-n!"), neg(fact(id("n"))));
        assert_eq!(
            parse("(n + 1)!"),
            fact(group(infix("+", id("n"), num("1"))))
        );
    }

    #[test]
    fn juxtaposition_reads_as_the_chosen_operator() {
        assert_eq!(
            parse("2 x y"),
            infix("*", infix("*", num("2"), id("x")), id("y"))
        );
        assert_eq!(
            parse("2 x ^ 2"),
            infix("*", num("2"), infix("^", id("x"), num("2")))
        );
        assert_eq!(
            parse("2(x + 1)"),
            infix("*", num("2"), group(infix("+", id("x"), num("1"))))
        );

        let no_juxtaposition = Grammar::new().infix("+", 1, Assoc::Left);
        assert_eq!(
            parse_ast("2 x", &no_juxtaposition).unwrap_err(),
            ParseError::at(2, "unexpected `x`")
        );
    }

    #[test]
    fn parentheses_are_kept() {
        assert_eq!(
            parse("(a + b) + c"),
            infix("+", group(infix("+", id("a"), id("b"))), id("c"))
        );
        assert_eq!(parse("((x))"), group(group(id("x"))));
    }

    #[test]
    fn calls_take_comma_separated_arguments() {
        assert_eq!(
            parse("f(x, 2 + y) g()"),
            infix(
                "*",
                Ast::Call("f".into(), vec![id("x"), infix("+", num("2"), id("y"))]),
                Ast::Call("g".into(), vec![])
            )
        );
    }

    #[test]
    fn literals_and_integers() {
        assert_eq!(parse("-3").literal("-").as_deref(), Some("-3"));
        assert_eq!(parse("2.5").literal("-").as_deref(), Some("2.5"));
        assert_eq!(parse("-(3)").literal("-"), None);
        assert_eq!(parse("-12").integer("-"), Some(-12));
        assert_eq!(parse("2.5").integer("-"), None);
        assert_eq!(parse("x").integer("-"), None);
    }

    #[test]
    fn operands_flatten_chains_but_not_groups() {
        let sum = |op: &str| match op {
            "+" => Some(false),
            "-" => Some(true),
            _ => None,
        };
        assert_eq!(
            parse("a - b + (c - d) - e * f").operands(sum),
            vec![
                (false, id("a")),
                (true, id("b")),
                (false, group(infix("-", id("c"), id("d")))),
                (true, infix("*", id("e"), id("f"))),
            ]
        );
        assert_eq!(parse("x").operands(sum), vec![(false, id("x"))]);
    }

    #[test]
    fn displays_source_form() {
        for src in ["1 + 2 * x", "-(x + 1) ^ -2", "f(x, y) * (z)", "a ⊕ n!"] {
            assert_eq!(parse(src).to_string(), src);
        }
        assert_eq!(parse("2 x").to_string(), "2 * x");
    }

    #[test]
    fn reports_errors_with_offsets() {
        assert_eq!(
            error(""),
            ParseError::at(0, "expected an expression, found end of input")
        );
        assert_eq!(
            error("x +"),
            ParseError::at(3, "expected an expression, found end of input")
        );
        assert_eq!(
            error("* x"),
            ParseError::at(0, "expected an expression, found `*`")
        );
        assert_eq!(
            error("(x + 1"),
            ParseError::at(6, "expected `)`, found end of input")
        );
        assert_eq!(error("x + 1)"), ParseError::at(5, "unexpected `)`"));
        let prefix_only = Grammar::new().prefix("¬", 1);
        assert_eq!(
            parse_ast("x ¬ y", &prefix_only).unwrap_err(),
            ParseError::at(2, "unexpected `¬`")
        );
        assert_eq!(
            error("f(x y"),
            ParseError::at(5, "expected `,` or `)`, found end of input")
        );
        assert_eq!(error("f(x; y)"), ParseError::at(3, "unexpected `;`"));
    }
}
