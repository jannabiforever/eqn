use crate::set::Set;

// ================================================================================
// Traits
// ================================================================================

pub trait BinaryOperator<S: Set> {
    fn apply(a: S::Element, b: S::Element) -> S::Element;
}

pub trait AssociativeOperator<S: Set>: BinaryOperator<S> {}

pub trait CommutativeOperator<S: Set>: BinaryOperator<S> {}

pub trait IdentityOperator<D: Set>: BinaryOperator<D> {
    const IDENTITY: D::Element;
}

pub trait InverseOperator<D: Set>: BinaryOperator<D> {
    fn inverse(a: D::Element) -> D::Element;
}
