use crate::set::Set;
use crate::symbol::Symbol;

/// AST rewriter - a strategy pattern
pub trait Rewriter {
    type Expr: Expression;

    // ================================================================================
    // Required methods
    // ================================================================================

    /// Formats an expression using this rewriter's strategy.
    fn rewrite_expr(&self, expr: &mut Self::Expr);

    // ================================================================================
    // Provided methods
    // ================================================================================

    /// Returns a new expression that has been formatted using this rewriter's
    /// strategy.
    fn rewrited_expr(&self, expr: Self::Expr) -> Self::Expr {
        let mut expr = expr;
        self.rewrite_expr(&mut expr);
        expr
    }
}

/// Splices one level of nesting: items for which `split` yields `Ok(inner)`
/// are replaced by their children, the rest pass through. Allocation-free
/// (an empty `Vec` does not allocate).
pub fn flatten<T>(
    items: Vec<T>,
    split: impl Fn(T) -> Result<Vec<T>, T>,
) -> impl Iterator<Item = T> {
    items.into_iter().flat_map(move |item| {
        let (inner, leaf) = match split(item) {
            Ok(inner) => (inner, None),
            Err(leaf) => (Vec::new(), Some(leaf)),
        };
        inner.into_iter().chain(leaf)
    })
}

/// A simple formatter for expressions. Returns identical one.
#[derive_where::derive_where(Default)]
pub struct TrivialRewriter<E: Expression> {
    _marker: std::marker::PhantomData<E>,
}

impl<E: Expression> TrivialRewriter<E> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<E: Expression> Rewriter for TrivialRewriter<E> {
    type Expr = E;

    fn rewrite_expr(&self, _: &mut Self::Expr) {}
}

/// Any expression containing [`Symbol`]s in the domain of a [`Set`].
pub trait Expression: Clone + From<Symbol<Self::Domain>> {
    type Domain: Set;

    // ================================================================================
    // Required methods
    // ================================================================================

    fn degrees_of_freedom(&self) -> usize;
    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self);

    // ================================================================================
    // Provided methods
    // ================================================================================

    fn substituted(mut self, sym: Symbol<Self::Domain>, expr: &Self) -> Self {
        self.substitute(sym, expr);
        self
    }

    fn rewrite_mut<R>(&mut self, rewriter: &R)
    where
        R: Rewriter<Expr = Self>,
    {
        rewriter.rewrite_expr(self);
    }

    fn rewrite<R>(self, rewriter: &R) -> Self
    where
        R: Rewriter<Expr = Self>,
    {
        rewriter.rewrited_expr(self)
    }

    fn rewritten<R>(&self, rewriter: &R) -> Self
    where
        R: Rewriter<Expr = Self>,
    {
        rewriter.rewrited_expr(self.clone())
    }
}
