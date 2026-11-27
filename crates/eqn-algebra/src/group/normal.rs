use eqn_core::quotient::Congruence;

use super::Group;
use crate::monoid::{Monoid, MonoidElem};

/// A normal subgroup `N` of a group, presented by a normal form for its
/// cosets.
///
/// The normal form is declared a congruence for the group's operation. The
/// class of the identity is then a normal subgroup and the classes are its
/// cosets, so membership in `N` is derived from the normal form.
pub trait NormalSubgroup: Congruence<<Self::Group as Monoid>::Operator> {
    type Group: Group;

    /// Whether `element` lies in `N`.
    fn contains(element: &MonoidElem<Self::Group>) -> bool {
        Self::reduce(element.clone()) == Self::reduce(Self::Group::identity())
    }
}
