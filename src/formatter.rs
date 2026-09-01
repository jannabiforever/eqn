pub trait Formatter {
    type Expr;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr;
}

pub struct TrivialFormatter<E> {
    _marker: std::marker::PhantomData<E>,
}

impl<E> TrivialFormatter<E> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<E> Default for TrivialFormatter<E> {
    fn default() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<E> Formatter for TrivialFormatter<E> {
    type Expr = E;

    fn format_expr(&self, expr: Self::Expr) -> Self::Expr {
        expr
    }
}
