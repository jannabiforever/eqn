use crate::domain::{Domain, NaturalNumber};

// ================================================================================
// Traits
// ================================================================================

pub trait BinaryOperator<D: Domain> {
    fn apply(a: D::Element, b: D::Element) -> D::Element;
}

pub trait AssociativeOperator<D: Domain>: BinaryOperator<D> {}

pub trait CommutativeOperator<D: Domain>: BinaryOperator<D> {}

pub trait IdentityOperator<D: Domain>: BinaryOperator<D> {
    const IDENTITY: D::Element;
}

// ================================================================================
// Structs
// ================================================================================

pub struct AddOperator<D: Domain> {
    _domain_marker: std::marker::PhantomData<D>,
}

impl BinaryOperator<NaturalNumber> for AddOperator<NaturalNumber> {
    fn apply(
        a: <NaturalNumber as Domain>::Element,
        b: <NaturalNumber as Domain>::Element,
    ) -> <NaturalNumber as Domain>::Element {
        a + b
    }
}

impl AssociativeOperator<NaturalNumber> for AddOperator<NaturalNumber> {}

pub struct MultiplyOperator<D: Domain> {
    _domain_marker: std::marker::PhantomData<D>,
}

impl BinaryOperator<NaturalNumber> for MultiplyOperator<NaturalNumber> {
    fn apply(
        a: <NaturalNumber as Domain>::Element,
        b: <NaturalNumber as Domain>::Element,
    ) -> <NaturalNumber as Domain>::Element {
        a * b
    }
}
