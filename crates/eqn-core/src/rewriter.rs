use crate::set::Set;
use crate::symbol::Symbol;

pub trait Rewriter {
    type Expr: Expression;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr;
}

#[derive_where::derive_where(Default)]
pub struct TrivialFormatter<E: Expression> {
    _marker: std::marker::PhantomData<E>,
}

impl<E: Expression> TrivialFormatter<E> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<E: Expression> Rewriter for TrivialFormatter<E> {
    type Expr = E;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        expr
    }
}

pub trait Expression: Clone + From<Symbol<Self::Domain>> {
    type Domain: Set;

    fn degrees_of_freedom(&self) -> usize;
    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self);
    fn substituted(mut self, sym: Symbol<Self::Domain>, expr: &Self) -> Self {
        self.substitute(sym, expr);
        self
    }
}
