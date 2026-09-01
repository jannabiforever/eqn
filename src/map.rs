use crate::domain::Domain;

pub trait Map<D, R>
where
    D: Domain,
    R: Domain,
{
    fn map(&self, d: D::Element) -> R::Element;
}
