use crate::set::Set;

pub trait Map<D, R>
where
    D: Set,
    R: Set,
{
    fn map(&self, d: D::Element) -> R::Element;
}
