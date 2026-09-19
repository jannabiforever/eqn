# Rule 006 - Prefer function annotation

There are two types of annotating a function - with just name, and a closure to
call one. It looks better when it comes to just a single name, because it
doesn't affect the abstraction level, which could lead to better readability.

## Example 01. using `std::ops::*`

```rust
#[derive(BinaryOperator)]
#[operator(domain = Z, apply = |a, b| a + b)]  // bad
pub struct ZAdd;
```

This should be rewritten to

```rust
use std::ops::Add;

#[derive(BinaryOperator)]
#[operator(domain = Z, add = Add::add)]  // good
pub struct ZAdd;
```

For convenience, you might want to provide a `Add::add` for addition-like approach.

## Example 02. inside a `.map(...)`

```rust
pub fn cast_symbols<D: Set>(v: &[Symbol<D>]) -> Vec<Expr<D>>{
    v.iter().map(|s| s.into()).collect() // bad
}
```

This should be rewritten to

```rust
pub fn cast_symbols<D: Set>(v: &[Symbol<D>]) -> Vec<Expr<D>>{
    v.iter().map(Into::into).collect() // good
}
```
