// mgca: `FiniteExtension<M>` hold `M::DIM` coordinates.
#![feature(min_generic_const_args, macroless_generic_const_args)]
#![allow(incomplete_features)]

use std::marker::PhantomData;
use std::num::NonZeroUsize;

use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::{CommutativeRing, DifferentialRing, Ring, RingElem, RingExpr, SemiRing};
use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

mod finite_field;

pub use finite_field::{
    CompatibleFiniteField, CompatibleFiniteFieldElement, CompatibleFiniteFieldEmbedding,
    DefiningPolynomial, FiniteField, FiniteFieldAdd, FiniteFieldElement, FiniteFieldElements,
    FiniteFieldMul, FirstCompatible, FirstIrreducible, FirstPrimitive, Fq, FqElement,
    IrreduciblePolynomial, PrimitiveFiniteField, PrimitiveFiniteFieldElement, is_irreducible,
    is_primitive,
};

/// The set of polynomial expressions over `R`, represented by [`RingExpr`]
/// trees.
#[derive(Set)]
#[set(element = RingExpr<R>)]
pub struct Polynomials<R: Ring>(PhantomData<R>);

/// Symbolic addition: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    apply = |a, b| RingExpr::Add(vec![a, b]),
    identity = RingExpr::Const(R::ZERO),
    inverse = |a| RingExpr::Neg(Box::new(a))
)]
pub struct PolyAdd<R: Ring>(PhantomData<R>);

/// Symbolic multiplication: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    apply = |a, b| RingExpr::Mul(vec![a, b]),
    identity = RingExpr::Const(R::ONE)
)]
pub struct PolyMul<R: CommutativeRing>(PhantomData<R>);

/// The commutative ring of polynomials over `R`. Elements are trees, so `Eq`
/// is structural: the ring laws hold modulo [`CommutativeRingRewriter`].
///
/// A newtype rather than the `(Polynomials, PolyAdd, PolyMul)` tuple so this
/// crate can implement foreign traits like [`DifferentialRing`] on it.
pub struct PolynomialRing<R: CommutativeRing>(PhantomData<R>);

impl<R: CommutativeRing> SemiRing for PolynomialRing<R> {
    type Domain = Polynomials<R>;
    type Addition = PolyAdd<R>;
    type Multiplication = PolyMul<R>;
}

impl<R: CommutativeRing> Module for PolynomialRing<R> {
    type Scalars = R;
    type Domain = Polynomials<R>;
    type Addition = PolyAdd<R>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        RingExpr::Mul(vec![RingExpr::Const(scalar), value])
    }
}

// ================================================================================
// PolynomialRing is a DifferentialRing over its own symbols
// ================================================================================

/// The polynomial derivation on the raw tree
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

    fn derive(a: RingElem<Self>, i: &Self::Index) -> RingElem<Self> {
        derive(a, i)
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::algebra::Algebra;
    use eqn_algebra::module::Module;
    use eqn_algebra::operator_impl::{ZAdd, ZMul};
    use eqn_algebra::rewriter::Rewriter;
    use eqn_algebra::ring::{CommutativeRingRewriter, SemiRing};
    use eqn_core::set::Z;

    use super::*;

    #[test]
    fn polynomial_ring_operators_build_trees() {
        type P = PolynomialRing<(Z, ZAdd, ZMul)>;
        let x = RingExpr::<(Z, ZAdd, ZMul)>::Symbol(Symbol::new("x"));
        let y = RingExpr::<(Z, ZAdd, ZMul)>::Symbol(Symbol::new("y"));

        assert_eq!(
            P::add(x.clone(), y.clone()),
            RingExpr::Add(vec![x.clone(), y])
        );
        assert_eq!(P::ONE, RingExpr::Const(1));
        assert_eq!(P::negate(x.clone()), RingExpr::Neg(Box::new(x)));
    }

    #[test]
    fn polynomial_ring_is_commutative() {
        fn assert_commutative_ring<R: CommutativeRing>() {}
        assert_commutative_ring::<PolynomialRing<(Z, ZAdd, ZMul)>>();
    }

    #[test]
    fn polynomial_ring_is_an_algebra_over_its_coefficients() {
        fn assert_algebra<A: Algebra>() {}

        type P = PolynomialRing<(Z, ZAdd, ZMul)>;
        let x = RingExpr::<(Z, ZAdd, ZMul)>::Symbol(Symbol::new("x"));

        assert_algebra::<P>();
        assert_eq!(
            P::scale(3, x.clone()),
            RingExpr::Mul(vec![RingExpr::Const(3), x])
        );
        assert_eq!(norm(P::from_scalar(4)), RingExpr::Const(4));
    }

    #[test]
    fn coefficient_action_satisfies_the_algebra_laws() {
        fn scale(scalar: i64, value: Expr) -> Expr {
            <Poly as Module>::scale(scalar, value)
        }

        let p = Expr::Add(vec![x(), c(2)]);
        let q = Expr::Add(vec![y(), c(-3)]);

        assert_eq!(norm(scale(0, p.clone())), c(0));
        assert_eq!(norm(scale(1, p.clone())), norm(p.clone()));
        assert_eq!(
            norm(scale(2 + 3, p.clone())),
            norm(<Poly as SemiRing>::add(
                scale(2, p.clone()),
                scale(3, p.clone())
            ))
        );
        assert_eq!(
            norm(scale(2 * 3, p.clone())),
            norm(scale(2, scale(3, p.clone())))
        );
        assert_eq!(
            norm(scale(2, <Poly as SemiRing>::add(p.clone(), q.clone()))),
            norm(<Poly as SemiRing>::add(
                scale(2, p.clone()),
                scale(2, q.clone())
            ))
        );

        let product = <Poly as SemiRing>::multiply(p.clone(), q.clone());
        let scaled_product = norm(scale(2, product));
        assert_eq!(
            scaled_product,
            norm(<Poly as SemiRing>::multiply(scale(2, p.clone()), q.clone()))
        );
        assert_eq!(
            scaled_product,
            norm(<Poly as SemiRing>::multiply(p, scale(2, q)))
        );
    }

    type Expr = RingExpr<(Z, ZAdd, ZMul)>;
    type Poly = PolynomialRing<(Z, ZAdd, ZMul)>;

    fn c(i: i64) -> Expr {
        Expr::Const(i)
    }

    fn xs() -> Symbol<Z> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Z> {
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
        CommutativeRingRewriter::<(Z, ZAdd, ZMul)>::new().rewrited_expr(e)
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
        assert_eq!(zero, Expr::Const(<(Z, ZAdd, ZMul) as SemiRing>::ZERO));

        let one = norm(Expr::Mul(vec![c(1), c(1)]));
        assert_eq!(one, Expr::Const(<(Z, ZAdd, ZMul) as SemiRing>::ONE));
    }
}
