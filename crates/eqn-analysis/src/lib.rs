// NOTE: `eqn_core::rewriter` is not re-exported here (unlike `set`/`symbol`)
// because it would collide with this crate's own private `rewriter` module
// below.
use eqn_algebra::field::Field;
use eqn_algebra::module::{Module, ModuleElem, ModuleScalar};
use eqn_algebra::ring::{DifferentialRing, RingElem, SemiRing};
use eqn_core::op::{Associative, BinaryOperator, Commutative};
use eqn_core::rewriter::Expression;
use eqn_core::set::Set;
use eqn_core::symbol::Symbol;

mod rewriter;
// Re-exports
pub use rewriter::ElementaryRewriter;

/// Elementary transcendental functions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Elementary {
    Exp,
    Log,
    Sin,
    Cos,
}

/// An expression tree over a field, closed under the elementary functions
/// and differentiation. `Pow` takes any integer exponent, so `x^-1` is
/// division. `D` is the unevaluated derivative `d(inner)/d(wrt)`; the
/// rewriter eliminates it.
#[derive_where::derive_where(Clone, Debug, Eq, PartialEq)]
pub enum ElementaryExpr<F: Field> {
    Const(<F::Domain as Set>::Element),
    Symbol(Symbol<F::Domain>),
    Neg(Box<Self>),
    Add(Vec<Self>),
    Mul(Vec<Self>),
    Pow {
        base: Box<Self>,
        exponent: isize,
    },
    Fn(Elementary, Box<Self>),
    D {
        wrt: Symbol<F::Domain>,
        inner: Box<Self>,
    },
}

impl<F: Field> ElementaryExpr<F> {
    pub fn elementary(kind: Elementary, arg: Self) -> Self {
        Self::Fn(kind, Box::new(arg))
    }

    pub fn d(wrt: Symbol<F::Domain>, inner: Self) -> Self {
        Self::D {
            wrt,
            inner: Box::new(inner),
        }
    }
}

impl<F: Field> Expression for ElementaryExpr<F> {
    type Domain = F::Domain;

    fn children(&self) -> &[Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &[],
            Self::Neg(inner) | Self::Pow { base: inner, .. } | Self::Fn(_, inner) => {
                std::slice::from_ref(inner)
            }
            Self::D { inner, .. } => std::slice::from_ref(inner),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn children_mut(&mut self) -> &mut [Self] {
        match self {
            Self::Const(_) | Self::Symbol(_) => &mut [],
            Self::Neg(inner) | Self::Pow { base: inner, .. } | Self::Fn(_, inner) => {
                std::slice::from_mut(inner)
            }
            Self::D { inner, .. } => std::slice::from_mut(inner),
            Self::Add(v) | Self::Mul(v) => v,
        }
    }

    fn as_symbol(&self) -> Option<&Symbol<Self::Domain>> {
        match self {
            Self::Symbol(s) => Some(s),
            _ => None,
        }
    }
}

impl<F: Field> From<Symbol<F::Domain>> for ElementaryExpr<F> {
    fn from(value: Symbol<F::Domain>) -> Self {
        Self::Symbol(value)
    }
}

// ================================================================================
// ElementaryFunctionRing: the differential ring of elementary functions
// ================================================================================

/// The set of elementary-function expressions over `F`, represented by
/// [`ElementaryExpr`] trees.
#[derive(Set)]
#[set(element = ElementaryExpr<F>)]
pub struct ElementaryFunctions<F: Field>(std::marker::PhantomData<F>);

/// Symbolic addition: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = ElementaryFunctions<F>,
    apply = |a, b| ElementaryExpr::Add(vec![a, b]),
    identity = ElementaryExpr::Const(F::ZERO),
    inverse = |a| ElementaryExpr::Neg(Box::new(a))
)]
pub struct ElementaryAdd<F: Field>(std::marker::PhantomData<F>);

/// Symbolic multiplication: builds the tree, does not normalize.
#[derive(Associative, BinaryOperator, Commutative)]
#[operator(
    domain = ElementaryFunctions<F>,
    apply = |a, b| ElementaryExpr::Mul(vec![a, b]),
    identity = ElementaryExpr::Const(F::ONE)
)]
pub struct ElementaryMul<F: Field>(std::marker::PhantomData<F>);

/// The differential ring of elementary functions over `F`; a differential
/// field in fact, but coefficient inversion is a rewriting matter, so only
/// the ring is declared.
pub struct ElementaryFunctionRing<F: Field>(std::marker::PhantomData<F>);

impl<F: Field> SemiRing for ElementaryFunctionRing<F> {
    type Domain = ElementaryFunctions<F>;
    type Addition = ElementaryAdd<F>;
    type Multiplication = ElementaryMul<F>;
}

impl<F: Field> Module for ElementaryFunctionRing<F> {
    type Scalars = F;
    type Domain = ElementaryFunctions<F>;
    type Addition = ElementaryAdd<F>;

    fn scale(scalar: ModuleScalar<Self>, value: ModuleElem<Self>) -> ModuleElem<Self> {
        ElementaryExpr::Mul(vec![ElementaryExpr::Const(scalar), value])
    }
}

impl<F: Field> DifferentialRing for ElementaryFunctionRing<F> {
    type Index = Symbol<F::Domain>;

    /// The eager form of [`ElementaryExpr::D`]: both funnel through
    /// [`rewriter::derivative`], the same symbolic differentiation the
    /// rewriter uses to eliminate `D` nodes.
    fn derive(a: RingElem<Self>, i: &Self::Index) -> RingElem<Self> {
        rewriter::derivative(a, i)
    }
}

#[cfg(test)]
mod tests {
    use eqn_algebra::algebra::Algebra;
    use eqn_algebra::operator_impl::{QAdd, QMul};
    use eqn_core::set::{Q, Rational};

    use super::*;

    type Rationals = (Q, QAdd, QMul);
    type Functions = ElementaryFunctionRing<Rationals>;

    #[test]
    fn elementary_function_ring_is_an_algebra_over_its_constants() {
        fn assert_algebra<A: Algebra>() {}

        let x = ElementaryExpr::<Rationals>::Symbol(Symbol::new("x"));
        let scalar = Rational::from(2);

        assert_algebra::<Functions>();
        assert_eq!(
            Functions::scale(scalar.clone(), x.clone()),
            ElementaryExpr::Mul(vec![ElementaryExpr::Const(scalar), x])
        );
    }
}
