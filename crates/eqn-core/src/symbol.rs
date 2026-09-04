use crate::set::Set;

#[derive_where::derive_where(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol<D: Set> {
    _domain_marker: std::marker::PhantomData<D>,
    pub name: String,
}

impl<D: Set> Symbol<D> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            _domain_marker: std::marker::PhantomData,
            name: name.into(),
        }
    }
}

impl<D: Set> AsRef<str> for Symbol<D> {
    fn as_ref(&self) -> &str {
        &self.name
    }
}

impl<D: Set> std::fmt::Display for Symbol<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}
