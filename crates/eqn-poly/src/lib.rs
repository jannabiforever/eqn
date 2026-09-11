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
    symbol = R::ADD_SYMBOL,
    apply = |a, b| RingExpr::Add(vec![a, b]),
    identity = RingExpr::Const(R::ZERO),
    inverse = |a| RingExpr::Neg(Box::new(a)),
    inverse_symbol = R::SUB_SYMBOL
)]
pub struct PolyAdd<R: Ring>(PhantomData<R>);

/// Symbolic multiplication: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = Polynomials<R>,
    symbol = R::MUL_SYMBOL,
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
    use eqn_algebra::ring::{CommutativeRingRewriter, SemiRing};
    use eqn_core::rewriter::Rewriter;
    use eqn_core::set::Z;

    use super::*;

    type Integers = (Z, ZAdd, ZMul);
    type Expr = RingExpr<Integers>;
    type Poly = PolynomialRing<Integers>;

    fn expr(src: &str) -> Expr {
        src.parse().unwrap()
    }

    fn xs() -> Symbol<Z> {
        Symbol::new("x")
    }

    fn ys() -> Symbol<Z> {
        Symbol::new("y")
    }

    fn norm(e: Expr) -> Expr {
        CommutativeRingRewriter::<Integers>::new().rewrited_expr(e)
    }

    #[test]
    fn polynomial_ring_operators_build_trees() {
        assert_eq!(Poly::add(expr("x"), expr("y")), expr("x + y"));
        assert_eq!(Poly::ONE, expr("1"));
        assert_eq!(Poly::negate(expr("x")), expr("-x"));
    }

    #[test]
    fn polynomial_ring_is_commutative() {
        fn assert_commutative_ring<R: CommutativeRing>() {}
        assert_commutative_ring::<Poly>();
    }

    #[test]
    fn polynomial_ring_is_an_algebra_over_its_coefficients() {
        fn assert_algebra<A: Algebra>() {}

        assert_algebra::<Poly>();
        assert_eq!(Poly::scale(3, expr("x")), expr("3 x"));
        assert_eq!(norm(Poly::from_scalar(4)), expr("4"));
    }

    #[test]
    fn coefficient_action_satisfies_the_algebra_laws() {
        fn scale(scalar: i64, value: Expr) -> Expr {
            <Poly as Module>::scale(scalar, value)
        }

        let p = expr("x + 2");
        let q = expr("y - 3");

        assert_eq!(norm(scale(0, p.clone())), expr("0"));
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

    #[test]
    fn derive_of_a_power() {
        assert_eq!(norm(Poly::derive(expr("x^2"), &xs())), expr("2 x"));
    }

    #[test]
    fn derive_of_a_product() {
        assert_eq!(norm(Poly::derive(expr("x y"), &xs())), expr("y"));
    }

    #[test]
    fn derive_of_a_sum_only_sees_its_own_variable() {
        assert_eq!(norm(Poly::derive(expr("x^3 + y"), &ys())), expr("1"));
    }

    #[test]
    fn derive_of_a_constant_is_zero() {
        assert_eq!(norm(Poly::derive(expr("5"), &xs())), expr("0"));
    }

    #[test]
    fn is_zero_and_is_one_after_normalizing() {
        assert_eq!(norm(expr("x + -x")), Expr::Const(Integers::ZERO));
        assert_eq!(norm(expr("1 * 1")), Expr::Const(Integers::ONE));
    }
}
