use std::collections::HashSet;

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

    /// Direct sub-expressions, left to right. Leaves return an empty slice.
    fn children(&self) -> &[Self];
    fn children_mut(&mut self) -> &mut [Self];

    /// The symbol this node *is*, if it is a bare symbol.
    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>>;

    // ================================================================================
    // Provided methods
    // ================================================================================

    /// Every strict sub-expression in pre-order (parents before children,
    /// left to right).
    fn descendants(&self) -> impl Iterator<Item = &Self> {
        let mut stack: Vec<&Self> = self.children().iter().rev().collect();
        std::iter::from_fn(move || {
            let e = stack.pop()?;
            stack.extend(e.children().iter().rev());
            Some(e)
        })
    }

    /// Every strict sub-expression in pre-order, mutably. See
    /// [`DescendantsMut`] for the `while let` protocol.
    fn descendants_mut(&mut self) -> DescendantsMut<'_, Self> {
        DescendantsMut {
            stack: self.children_mut().iter_mut().rev().collect(),
            current: None,
        }
    }

    /// Number of free variables in the expression.
    ///
    /// NOTE: expression `a - a` holds 1 degrees of freedom.
    /// If precision is required, rewrite the expression first.
    ///
    /// # See also
    ///
    /// [`Rewriter`]: if you need to rewrite the expression first.
    fn degrees_of_freedom(&self) -> usize {
        std::iter::once(self)
            .chain(self.descendants())
            .filter_map(Self::as_symbol)
            .collect::<HashSet<_>>()
            .len()
    }

    /// Substitute a symbol with an expression in-place.
    ///
    /// # See also
    ///
    /// [`Rewriter`]: if you need to rewrite the expression first.
    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self) {
        if self.as_symbol() == Some(&sym) {
            *self = expr.clone();
            return;
        }
        let mut walk = self.descendants_mut();
        while let Some(e) = walk.next() {
            if e.as_symbol() == Some(&sym) {
                *e = expr.clone();
                walk.skip_children();
            }
        }
    }

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

/// Pre-order `&mut` walk over a tree, driven by a stack.
///
/// Not an [`Iterator`]: each node returned by [`next`](Self::next) borrows
/// the walker, so it is dead again before the walker descends into its
/// children. That is what makes handing out `&mut` to a node and later to its
/// children sound without `unsafe`. Use it as
///
/// ```ignore
/// let mut walk = expr.descendants_mut();
/// while let Some(e) = walk.next() {
///     // mutate `e`; call `walk.skip_children()` to not descend into it
/// }
/// ```
pub struct DescendantsMut<'a, E> {
    stack: Vec<&'a mut E>,
    /// The node handed out by the last `next`, still to be descended into.
    current: Option<&'a mut E>,
}

impl<E: Expression> DescendantsMut<'_, E> {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<&mut E> {
        if let Some(node) = self.current.take() {
            self.stack.extend(node.children_mut().iter_mut().rev());
        }
        self.current = self.stack.pop();
        self.current.as_deref_mut()
    }

    /// Do not descend into the node returned by the last [`next`](Self::next).
    pub fn skip_children(&mut self) {
        self.current = None;
    }
}
