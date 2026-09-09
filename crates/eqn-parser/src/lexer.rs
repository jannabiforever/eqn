use std::fmt;

use crate::ParseError;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Number(String),
    Ident(String),
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    Wedge,
    LParen,
    RParen,
    Comma,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Number(text) | Self::Ident(text) => text,
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Caret => "^",
            Self::Wedge => "∧",
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
    c.is_alphanumeric() || c == '_' || c == '\''
}

/// Splits `src` into tokens, each paired with its byte offset. Whitespace is
/// skipped; a literal is digits with an optional fraction (`2.5`), and an
/// identifier is a letter or `_` followed by letters, digits, `_` or `'`.
pub fn tokenize(src: &str) -> Result<Vec<(Token, usize)>, ParseError> {
    let mut tokens = Vec::new();
    let mut at = 0;

    while let Some(c) = src[at..].chars().next() {
        let rest = &src[at..];
        let (token, len) = match c {
            c if c.is_whitespace() => {
                at += c.len_utf8();
                continue;
            }
            '+' => (Token::Plus, 1),
            '-' => (Token::Minus, 1),
            '*' => (Token::Star, 1),
            '/' if rest.starts_with("/\\") => (Token::Wedge, 2),
            '/' => (Token::Slash, 1),
            '^' => (Token::Caret, 1),
            '∧' => (Token::Wedge, c.len_utf8()),
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
            c => return Err(ParseError::at(at, format!("unexpected character `{c}`"))),
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

    fn tokens(src: &str) -> Vec<Token> {
        tokenize(src).unwrap().into_iter().map(|(t, _)| t).collect()
    }

    #[test]
    fn tokenizes_operators_and_atoms() {
        assert_eq!(
            tokens("x_1' + 2.5*(y) - z/w^2, θ ∧ d /\\ e"),
            vec![
                Token::Ident("x_1'".into()),
                Token::Plus,
                Token::Number("2.5".into()),
                Token::Star,
                Token::LParen,
                Token::Ident("y".into()),
                Token::RParen,
                Token::Minus,
                Token::Ident("z".into()),
                Token::Slash,
                Token::Ident("w".into()),
                Token::Caret,
                Token::Number("2".into()),
                Token::Comma,
                Token::Ident("θ".into()),
                Token::Wedge,
                Token::Ident("d".into()),
                Token::Wedge,
                Token::Ident("e".into()),
            ]
        );
    }

    #[test]
    fn records_byte_offsets() {
        let offsets: Vec<usize> = tokenize("θ + 12")
            .unwrap()
            .into_iter()
            .map(|(_, at)| at)
            .collect();
        assert_eq!(offsets, vec![0, 3, 5]);
    }

    #[test]
    fn a_trailing_dot_is_not_part_of_a_number() {
        assert_eq!(
            tokenize("1.x").unwrap_err(),
            ParseError::at(1, "unexpected character `.`")
        );
    }

    #[test]
    fn rejects_unknown_characters() {
        assert_eq!(
            tokenize("x $ y").unwrap_err(),
            ParseError::at(2, "unexpected character `$`")
        );
    }
}
