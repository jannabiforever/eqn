use std::num::NonZeroUsize;

use super::{CommutativeRing, Element, PolynomialRing, RingExpr};
use crate::symbol::Symbol;

// ================================================================================
// DifferentialRing
// ================================================================================

/// A commutative ring with a family of commuting derivations `∂_i`, indexed
/// by [`Index`](Self::Index). Each `∂_i` is additive and satisfies Leibniz,
/// `∂_i(ab) = (∂_i a) b + a (∂_i b)`, and `∂_i ∂_j = ∂_j ∂_i`. Rust cannot
/// verify these laws; they are the implementor's contract.
pub trait DifferentialRing: CommutativeRing {
    /// Names a derivation.
    type Index;
    /// `∂_i a`.
    fn derive(a: Element<Self>, i: &Self::Index) -> Element<Self>;
}

// ================================================================================
// PolynomialRing is a DifferentialRing over its own symbols
// ================================================================================

/// The polynomial derivation on the raw tree (no normalization -- a
/// [`Rewriter`](crate::rewriter::Rewriter) is the caller's job).
fn derive<R: CommutativeRing>(expr: RingExpr<R>, wrt: &Symbol<R::Domain>) -> RingExpr<R> {
    match expr {
        RingExpr::Const(_) => RingExpr::Const(R::ZERO),
        RingExpr::Symbol(s) => RingExpr::Const(if s == *wrt { R::ONE } else { R::ZERO }),
        RingExpr::Neg(inner) => RingExpr::Neg(Box::new(derive(*inner, wrt))),
        RingExpr::Add(v) => RingExpr::Add(v.into_iter().map(|u| derive(u, wrt)).collect()),
        // Leibniz
        RingExpr::Mul(v) => RingExpr::Add(
            (0..v.len())
                .map(|i| {
                    let mut factors = v.clone();
                    factors[i] = derive(v[i].clone(), wrt);
                    RingExpr::Mul(factors)
                })
                .collect(),
        ),
        RingExpr::Pow { base, exponent } => {
            let d_base = derive((*base).clone(), wrt);
            let reduced = match NonZeroUsize::new(exponent.get() - 1) {
                Some(exponent) => RingExpr::Pow { base, exponent },
                None => RingExpr::Const(R::ONE),
            };
            RingExpr::Mul(vec![
                RingExpr::Const(R::from_usize(exponent.get())),
                reduced,
                d_base,
            ])
        }
    }
}

/// The free commutative `R`-algebra on its symbols, with `∂/∂s`.
impl<R: CommutativeRing> DifferentialRing for PolynomialRing<R> {
    type Index = Symbol<R::Domain>;

    fn derive(a: Element<Self>, i: &Self::Index) -> Element<Self> {
        derive(a, i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rewriter::Rewriter;
    use crate::ring::{CommutativeRingRewriter, IntegerRing, Integers, SemiRing};

    type Expr = RingExpr<IntegerRing>;
    type Poly = PolynomialRing<IntegerRing>;

    fn c(i: i64) -> Expr {
        Expr::Const(i)
    }

    fn xs() -> Symbol<Integers> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Integers> {
        Symbol::new("y")
    }

    fn x() -> Expr {
        Expr::Symbol(xs())
    }

    fn y() -> Expr {
        Expr::Symbol(ys())
    }

    fn pow(base: Expr, exponent: usize) -> Expr {
        Expr::Pow {
            base: Box::new(base),
            exponent: NonZeroUsize::new(exponent).unwrap(),
        }
    }

    fn norm(e: Expr) -> Expr {
        CommutativeRingRewriter::<IntegerRing>::new().rewrited_expr(e)
    }

    #[test]
    fn derive_of_a_power() {
        // d(x^2)/dx = 2x
        assert_eq!(
            norm(Poly::derive(pow(x(), 2), &xs())),
            Expr::Mul(vec![c(2), x()])
        );
    }

    #[test]
    fn derive_of_a_product() {
        // d(x*y)/dx = y
        assert_eq!(norm(Poly::derive(Expr::Mul(vec![x(), y()]), &xs())), y());
    }

    #[test]
    fn derive_of_a_sum_only_sees_its_own_variable() {
        // d(x^3 + y)/dy = 1
        let expr = Expr::Add(vec![pow(x(), 3), y()]);
        assert_eq!(norm(Poly::derive(expr, &ys())), c(1));
    }

    #[test]
    fn derive_of_a_constant_is_zero() {
        assert_eq!(norm(Poly::derive(c(5), &xs())), c(0));
    }

    #[test]
    fn is_zero_and_is_one_after_normalizing() {
        let zero = norm(Expr::Add(vec![x(), Expr::Neg(Box::new(x()))]));
        assert_eq!(zero, Expr::Const(IntegerRing::ZERO));

        let one = norm(Expr::Mul(vec![c(1), c(1)]));
        assert_eq!(one, Expr::Const(IntegerRing::ONE));
    }
}
