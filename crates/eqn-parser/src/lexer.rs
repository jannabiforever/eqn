use std::fmt;

use crate::{Grammar, ParseError};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Number(String),
    Ident(String),
    /// An operator symbol declared by the grammar.
    Op(String),
    LParen,
    RParen,
    Comma,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Number(text) | Self::Ident(text) | Self::Op(text) => text,
            Self::LParen => "(",
            Self::RParen => ")",
            Self::Comma => ",",
        })
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Splits `src` into tokens, each paired with its byte offset. Whitespace is
/// skipped; a literal is digits with an optional fraction (`2.5`); an
/// identifier is a letter or `_` followed by letters, digits or `_`; and
/// anything else must be one of the grammar's operator symbols, matched
/// longest first.
pub fn tokenize(src: &str, grammar: &Grammar) -> Result<Vec<(Token, usize)>, ParseError> {
    let symbols = grammar.symbols();
    let mut tokens = Vec::new();
    let mut at = 0;

    while let Some(c) = src[at..].chars().next() {
        let rest = &src[at..];
        let (token, len) = match c {
            c if c.is_whitespace() => {
                at += c.len_utf8();
                continue;
            }
            '(' => (Token::LParen, 1),
            ')' => (Token::RParen, 1),
            ',' => (Token::Comma, 1),
            c if c.is_ascii_digit() => {
                let mut len = scan(rest, |c| c.is_ascii_digit());
                if rest[len..].starts_with('.') {
                    let fraction = scan(&rest[len + 1..], |c| c.is_ascii_digit());
                    if fraction > 0 {
                        len += 1 + fraction;
                    }
                }
                (Token::Number(rest[..len].to_owned()), len)
            }
            c if is_ident_start(c) => {
                let len = scan(rest, is_ident_continue);
                (Token::Ident(rest[..len].to_owned()), len)
            }
            c => match symbols.iter().find(|symbol| rest.starts_with(*symbol)) {
                Some(symbol) => (Token::Op((*symbol).to_owned()), symbol.len()),
                None => return Err(ParseError::at(at, format!("unexpected `{c}`"))),
            },
        };
        tokens.push((token, at));
        at += len;
    }

    Ok(tokens)
}

/// Byte length of the longest prefix of `s` whose chars all satisfy `pred`.
fn scan(s: &str, pred: impl Fn(char) -> bool) -> usize {
    s.char_indices()
        .find(|&(_, c)| !pred(c))
        .map_or(s.len(), |(i, _)| i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Assoc;

    fn grammar() -> Grammar {
        Grammar::new()
            .infix("+", 1, Assoc::Left)
            .infix("-", 1, Assoc::Left)
            .infix("*", 2, Assoc::Left)
            .infix("/", 2, Assoc::Left)
            .infix("^", 4, Assoc::Right)
            .infix("∧", 2, Assoc::Left)
            .infix("\\oplus", 1, Assoc::Left)
            .infix("**", 4, Assoc::Right)
    }

    fn tokens(src: &str) -> Vec<Token> {
        tokenize(src, &grammar())
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect()
    }

    fn op(symbol: &str) -> Token {
        Token::Op(symbol.into())
    }

    #[test]
    fn tokenizes_operators_and_atoms() {
        assert_eq!(
            tokens("x_1 + 2.5*(y) - z/w^2, θ ∧ d"),
            vec![
                Token::Ident("x_1".into()),
                op("+"),
                Token::Number("2.5".into()),
                op("*"),
                Token::LParen,
                Token::Ident("y".into()),
                Token::RParen,
                op("-"),
                Token::Ident("z".into()),
                op("/"),
                Token::Ident("w".into()),
                op("^"),
                Token::Number("2".into()),
                Token::Comma,
                Token::Ident("θ".into()),
                op("∧"),
                Token::Ident("d".into()),
            ]
        );
    }

    #[test]
    fn matches_the_longest_operator() {
        assert_eq!(
            tokens("a ** b \\oplus c"),
            vec![
                Token::Ident("a".into()),
                op("**"),
                Token::Ident("b".into()),
                op("\\oplus"),
                Token::Ident("c".into()),
            ]
        );
        assert_eq!(
            tokens("a*b"),
            vec![Token::Ident("a".into()), op("*"), Token::Ident("b".into())]
        );
    }

    #[test]
    fn records_byte_offsets() {
        let offsets: Vec<usize> = tokenize("θ + 12", &grammar())
            .unwrap()
            .into_iter()
            .map(|(_, at)| at)
            .collect();
        assert_eq!(offsets, vec![0, 3, 5]);
    }

    #[test]
    fn a_trailing_dot_is_not_part_of_a_number() {
        assert_eq!(
            tokenize("1.x", &grammar()).unwrap_err(),
            ParseError::at(1, "unexpected `.`")
        );
    }

    #[test]
    fn rejects_undeclared_symbols() {
        assert_eq!(
            tokenize("x $ y", &grammar()).unwrap_err(),
            ParseError::at(2, "unexpected `$`")
        );
        assert_eq!(
            tokenize("x + y", &Grammar::new()).unwrap_err(),
            ParseError::at(2, "unexpected `+`")
        );
    }
}
