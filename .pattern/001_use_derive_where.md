# Rule 001 - Use derive_where

This project inevitably contains a lot of `std::marker::PhantomData`, to obtain
lots of zero-cost polymorphisms. To derive native traits via procedure macro,
use `derive_where::derive_where`.

```rust
#[derive_where::derive_where(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SomeMathmaticalConcept<T>(std::marker::PhantomData<T>);
```

To easily derive `std::fmt::Debug` not exposing the marker field, use
`derive_where(skip)` for specific field.

```rust
#[derive_where::derive_where(Debug)]
pub struct SomeMathmaticalConcept<T> {
    field_to_expose: FieldToExpose,
    #[derive_where::derive_where(skip)]
    _marker: std::marker::PhantomData<T>,
};
```
