use crate::set::Set;

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

impl<D: Set> Clone for Symbol<D> {
    fn clone(&self) -> Self {
        Self {
            _domain_marker: std::marker::PhantomData,
            name: self.name.clone(),
        }
    }
}

impl<D: Set> PartialEq for Symbol<D> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<D: Set> Eq for Symbol<D> {}

impl<D: Set> PartialOrd for Symbol<D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<D: Set> Ord for Symbol<D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl<D: Set> std::hash::Hash for Symbol<D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl<D: Set> std::fmt::Display for Symbol<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

impl<D: Set> std::fmt::Debug for Symbol<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Symbol({})", self.name)
    }
}
