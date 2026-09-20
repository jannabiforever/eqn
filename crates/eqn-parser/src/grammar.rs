use std::collections::HashMap;

use crate::Token;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assoc {
    Left,
    Right,
}

impl Assoc {
    /// The left and right binding powers of an infix operator at
    /// `precedence`: the power on the side away from the associativity is
    /// raised by one, so a chain of the operator groups toward that side.
    fn powers(self, precedence: u8) -> (u16, u16) {
        let base = Grammar::base(precedence);
        match self {
            Self::Left => (base, base + 1),
            Self::Right => (base + 1, base),
        }
    }
}

/// What a symbol does after a complete operand: continues it as an infix
/// operator, or closes it as a postfix one. The two are exclusive, since
/// the parser could not tell them apart.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Trailing {
    Infix { left: u16, right: u16 },
    Postfix { left: u16 },
}

impl Trailing {
    /// The binding power toward the operand on the left.
    pub(crate) fn left(self) -> u16 {
        match self {
            Self::Infix { left, .. } | Self::Postfix { left } => left,
        }
    }
}

/// One symbol's roles at the two places the parser meets it. A symbol may
/// fill both (`-` is commonly prefix and infix), since the two positions
/// never compete for the same token.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Operator {
    /// The right binding power when the symbol opens an operand: `op a`.
    prefix: Option<u16>,
    trailing: Option<Trailing>,
}

/// The operator table a parse runs against: which symbols are operators, and
/// with what fixity, precedence and associativity. Numeric literals,
/// identifiers, calls `f(a, b)` and parentheses are always available; every
/// operator is declared by the expression type that understands it, so this
/// crate names none.
///
/// A symbol may be declared in several roles (`-` is commonly both prefix
/// and infix) but not as both infix and postfix, which would be ambiguous.
/// Higher precedence binds tighter. A declaration that breaks these rules is
/// an error, not a table the parser could misread.
#[derive(Clone, Debug, Default)]
pub struct Grammar {
    operators: HashMap<String, Operator>,
    juxtaposition: Option<String>,
}

impl Grammar {
    pub fn new() -> Self {
        Self::default()
    }

    /// The binding power of a precedence level, leaving room between levels
    /// for associativity.
    fn base(precedence: u8) -> u16 {
        (u16::from(precedence) + 1) * 2
    }

    /// Operator symbols must be lexically distinguishable from the atoms: they
    /// cannot start like an identifier or a number, and cannot contain the
    /// punctuation that is reserved for calls and grouping.
    fn check_symbol(symbol: &str) -> anyhow::Result<()> {
        let Some(first) = symbol.chars().next() else {
            anyhow::bail!("an operator symbol cannot be empty");
        };
        anyhow::ensure!(
            !(Token::opens_ident(first) || first.is_ascii_digit()),
            "operator `{symbol}` would lex as an identifier or a number"
        );
        anyhow::ensure!(
            !symbol
                .chars()
                .any(|c| c.is_whitespace() || "(),".contains(c)),
            "operator `{symbol}` contains whitespace or reserved punctuation"
        );
        Ok(())
    }

    /// The record for `symbol`, empty until a declaration fills a role.
    fn operator(&mut self, symbol: &str) -> &mut Operator {
        self.operators.entry(symbol.to_owned()).or_default()
    }

    /// Declares `symbol` as a prefix operator: `symbol a`.
    pub fn prefix(mut self, symbol: &str, precedence: u8) -> anyhow::Result<Self> {
        Self::check_symbol(symbol)?;
        self.operator(symbol).prefix = Some(Self::base(precedence));
        Ok(self)
    }

    /// Declares `symbol` as an infix operator: `a symbol b`.
    pub fn infix(mut self, symbol: &str, precedence: u8, assoc: Assoc) -> anyhow::Result<Self> {
        Self::check_symbol(symbol)?;
        let operator = self.operator(symbol);
        anyhow::ensure!(
            !matches!(operator.trailing, Some(Trailing::Postfix { .. })),
            "operator `{symbol}` is already postfix; it cannot also be infix"
        );
        let (left, right) = assoc.powers(precedence);
        operator.trailing = Some(Trailing::Infix { left, right });
        Ok(self)
    }

    /// Declares `symbol` as a postfix operator: `a symbol`.
    pub fn postfix(mut self, symbol: &str, precedence: u8) -> anyhow::Result<Self> {
        Self::check_symbol(symbol)?;
        let operator = self.operator(symbol);
        anyhow::ensure!(
            !matches!(operator.trailing, Some(Trailing::Infix { .. })),
            "operator `{symbol}` is already infix; it cannot also be postfix"
        );
        operator.trailing = Some(Trailing::Postfix {
            left: Self::base(precedence),
        });
        Ok(self)
    }

    /// Reads adjacent operands (`2 x`, `2(x + 1)`, `f(x) y`) as the infix
    /// operator `symbol`, which must already be declared.
    pub fn juxtaposition(mut self, symbol: &str) -> anyhow::Result<Self> {
        anyhow::ensure!(
            matches!(self.trailing(symbol), Some(Trailing::Infix { .. })),
            "juxtaposition must name a declared infix operator, not `{symbol}`"
        );
        self.juxtaposition = Some(symbol.to_owned());
        Ok(self)
    }

    /// Declares `symbol` to parse exactly like `existing` in every role the
    /// latter has, while keeping its own spelling in the tree. This is how a
    /// grammar built on another one slots a new operator in at the same
    /// level as one it already has.
    pub fn alias(mut self, symbol: &str, existing: &str) -> anyhow::Result<Self> {
        Self::check_symbol(symbol)?;
        let operator = *self
            .operators
            .get(existing)
            .ok_or_else(|| anyhow::anyhow!("cannot alias `{symbol}` to undeclared `{existing}`"))?;
        self.operators.insert(symbol.to_owned(), operator);
        Ok(self)
    }

    /// Every declared symbol, longest first, for longest-match lexing.
    pub(crate) fn symbols(&self) -> Vec<&str> {
        let mut symbols: Vec<&str> = self.operators.keys().map(String::as_str).collect();
        symbols.sort_unstable_by(|a, b| b.len().cmp(&a.len()).then(a.cmp(b)));
        symbols
    }

    pub(crate) fn prefix_power(&self, symbol: &str) -> Option<u16> {
        self.operators.get(symbol)?.prefix
    }

    pub(crate) fn trailing(&self, symbol: &str) -> Option<Trailing> {
        self.operators.get(symbol)?.trailing
    }

    /// The infix operator juxtaposition stands for, with its spelling.
    pub(crate) fn juxtaposition_operator(&self) -> Option<(&str, Trailing)> {
        let symbol = self.juxtaposition.as_deref()?;
        Some((symbol, self.trailing(symbol)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbols_are_longest_first() -> anyhow::Result<()> {
        let grammar = Grammar::new()
            .infix("+", 1, Assoc::Left)?
            .infix("++", 1, Assoc::Left)?
            .prefix("+", 2)?
            .infix("\\oplus", 1, Assoc::Left)?;
        assert_eq!(grammar.symbols(), ["\\oplus", "++", "+"]);
        Ok(())
    }

    #[test]
    fn alias_copies_every_fixity() -> anyhow::Result<()> {
        let grammar = Grammar::new()
            .infix("-", 1, Assoc::Left)?
            .prefix("-", 3)?
            .alias("\u{2212}", "-")?;
        assert_eq!(grammar.operators["\u{2212}"], grammar.operators["-"]);
        Ok(())
    }

    #[test]
    fn rejects_word_like_symbols() {
        let error = Grammar::new().infix("mod", 1, Assoc::Left).unwrap_err();
        assert_eq!(
            error.to_string(),
            "operator `mod` would lex as an identifier or a number"
        );
    }

    #[test]
    fn rejects_infix_postfix_ambiguity() -> anyhow::Result<()> {
        let error = Grammar::new()
            .infix("!", 1, Assoc::Left)?
            .postfix("!", 2)
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "operator `!` is already infix; it cannot also be postfix"
        );
        Ok(())
    }

    #[test]
    fn juxtaposition_needs_a_declared_operator() {
        let error = Grammar::new().juxtaposition("*").unwrap_err();
        assert_eq!(
            error.to_string(),
            "juxtaposition must name a declared infix operator, not `*`"
        );
    }

    #[test]
    fn alias_needs_a_declared_operator() {
        let error = Grammar::new().alias("\u{2212}", "-").unwrap_err();
        assert_eq!(
            error.to_string(),
            "cannot alias `\u{2212}` to undeclared `-`"
        );
    }
}
