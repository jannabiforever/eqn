use std::collections::HashMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assoc {
    Left,
    Right,
}

/// The operator table a parse runs against: which symbols are operators, and
/// with what fixity, precedence and associativity. Numeric literals,
/// identifiers, calls `f(a, b)` and parentheses are always available; every
/// operator is declared by the expression type that understands it, so this
/// crate names none.
///
/// A symbol may be declared in several fixities (`-` is commonly both prefix
/// and infix) but not as both infix and postfix, which would be ambiguous.
/// Higher precedence binds tighter.
#[derive(Clone, Debug, Default)]
pub struct Grammar {
    prefix: HashMap<String, u16>,
    infix: HashMap<String, (u16, u16)>,
    postfix: HashMap<String, u16>,
    juxtaposition: Option<String>,
}

/// Binding powers leave room between precedence levels for associativity.
fn base(precedence: u8) -> u16 {
    (u16::from(precedence) + 1) * 2
}

/// Operator symbols must be lexically distinguishable from the atoms: they
/// cannot start like an identifier or a number, and cannot contain the
/// punctuation that is reserved for calls and grouping.
fn check_symbol(symbol: &str) {
    let first = symbol
        .chars()
        .next()
        .expect("an operator symbol cannot be empty");
    assert!(
        !(first.is_alphanumeric() || first == '_'),
        "operator `{symbol}` would lex as an identifier or a number"
    );
    assert!(
        !symbol
            .chars()
            .any(|c| c.is_whitespace() || "(),".contains(c)),
        "operator `{symbol}` contains whitespace or reserved punctuation"
    );
}

impl Grammar {
    pub fn new() -> Self {
        Self::default()
    }

    /// Declares `symbol` as a prefix operator: `symbol a`.
    pub fn prefix(mut self, symbol: &str, precedence: u8) -> Self {
        check_symbol(symbol);
        self.prefix.insert(symbol.to_owned(), base(precedence));
        self
    }

    /// Declares `symbol` as an infix operator: `a symbol b`.
    pub fn infix(mut self, symbol: &str, precedence: u8, assoc: Assoc) -> Self {
        check_symbol(symbol);
        assert!(
            !self.postfix.contains_key(symbol),
            "operator `{symbol}` is already postfix; it cannot also be infix"
        );
        let base = base(precedence);
        let powers = match assoc {
            Assoc::Left => (base, base + 1),
            Assoc::Right => (base + 1, base),
        };
        self.infix.insert(symbol.to_owned(), powers);
        self
    }

    /// Declares `symbol` as a postfix operator: `a symbol`.
    pub fn postfix(mut self, symbol: &str, precedence: u8) -> Self {
        check_symbol(symbol);
        assert!(
            !self.infix.contains_key(symbol),
            "operator `{symbol}` is already infix; it cannot also be postfix"
        );
        self.postfix.insert(symbol.to_owned(), base(precedence));
        self
    }

    /// Reads adjacent operands (`2 x`, `2(x + 1)`, `f(x) y`) as the infix
    /// operator `symbol`, which must already be declared.
    pub fn juxtaposition(mut self, symbol: &str) -> Self {
        assert!(
            self.infix.contains_key(symbol),
            "juxtaposition must name a declared infix operator, not `{symbol}`"
        );
        self.juxtaposition = Some(symbol.to_owned());
        self
    }

    /// Declares `symbol` to parse exactly like `existing` in every fixity the
    /// latter has, while keeping its own spelling in the tree. This is how a
    /// grammar built on another one slots a new operator in at the same
    /// level as one it already has.
    pub fn alias(mut self, symbol: &str, existing: &str) -> Self {
        check_symbol(symbol);
        let mut found = false;
        if let Some(&powers) = self.prefix.get(existing) {
            self.prefix.insert(symbol.to_owned(), powers);
            found = true;
        }
        if let Some(&powers) = self.infix.get(existing) {
            self.infix.insert(symbol.to_owned(), powers);
            found = true;
        }
        if let Some(&powers) = self.postfix.get(existing) {
            self.postfix.insert(symbol.to_owned(), powers);
            found = true;
        }
        assert!(found, "cannot alias `{symbol}` to undeclared `{existing}`");
        self
    }

    /// Every declared symbol, longest first, for longest-match lexing.
    pub(crate) fn symbols(&self) -> Vec<&str> {
        let mut symbols: Vec<&str> = self
            .prefix
            .keys()
            .chain(self.infix.keys())
            .chain(self.postfix.keys())
            .map(String::as_str)
            .collect();
        symbols.sort_unstable_by(|a, b| b.len().cmp(&a.len()).then(a.cmp(b)));
        symbols.dedup();
        symbols
    }

    pub(crate) fn prefix_power(&self, symbol: &str) -> Option<u16> {
        self.prefix.get(symbol).copied()
    }

    pub(crate) fn infix_powers(&self, symbol: &str) -> Option<(u16, u16)> {
        self.infix.get(symbol).copied()
    }

    pub(crate) fn postfix_power(&self, symbol: &str) -> Option<u16> {
        self.postfix.get(symbol).copied()
    }

    pub(crate) fn juxtaposition_powers(&self) -> Option<(&str, (u16, u16))> {
        let symbol = self.juxtaposition.as_deref()?;
        Some((symbol, self.infix[symbol]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbols_are_longest_first() {
        let grammar = Grammar::new()
            .infix("+", 1, Assoc::Left)
            .infix("++", 1, Assoc::Left)
            .prefix("+", 2)
            .infix("\\oplus", 1, Assoc::Left);
        assert_eq!(grammar.symbols(), ["\\oplus", "++", "+"]);
    }

    #[test]
    fn alias_copies_every_fixity() {
        let grammar = Grammar::new()
            .infix("-", 1, Assoc::Left)
            .prefix("-", 3)
            .alias("−", "-");
        assert_eq!(grammar.infix_powers("−"), grammar.infix_powers("-"));
        assert_eq!(grammar.prefix_power("−"), grammar.prefix_power("-"));
    }

    #[test]
    #[should_panic(expected = "would lex as an identifier")]
    fn rejects_word_like_symbols() {
        Grammar::new().infix("mod", 1, Assoc::Left);
    }

    #[test]
    #[should_panic(expected = "cannot also be postfix")]
    fn rejects_infix_postfix_ambiguity() {
        Grammar::new().infix("!", 1, Assoc::Left).postfix("!", 2);
    }

    #[test]
    #[should_panic(expected = "must name a declared infix operator")]
    fn juxtaposition_needs_a_declared_operator() {
        Grammar::new().juxtaposition("*");
    }
}
