use crate::set::Set;
use crate::symbol::Symbol;

pub trait Formatter {
    type Expr: Expression;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr;
}

pub struct TrivialFormatter<E: Expression> {
    _marker: std::marker::PhantomData<E>,
}

impl<E: Expression> TrivialFormatter<E> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<E: Expression> Default for TrivialFormatter<E> {
    fn default() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E: Expression> Formatter for TrivialFormatter<E> {
    type Expr = E;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        expr
    }
}

pub trait Expression: Clone {
    type Domain: Set;

    fn degrees_of_freedom(&self) -> usize;
    fn from_symbol(sym: Symbol<Self::Domain>) -> Self;
    fn substitute(&mut self, sym: Symbol<Self::Domain>, expr: &Self);

    fn substituted(mut self, sym: Symbol<Self::Domain>, expr: &Self) -> Self {
        self.substitute(sym, expr);
        self
    }
}
