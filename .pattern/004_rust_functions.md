# Rule 004 - Rust functions

There are three types of rust functions: free functions, inherent methods,
trait-associated methods.

Here, we consider free functions as anti-patterns for better scope handling.

So don't do this:

```rust
fn split_power<G: Group>(expr: GroupExpr<G>) -> (GroupExpr<G>, isize) {
    match expr {
        GroupExpr::Inv(base) => (*base, -1),
        GroupExpr::Pow { base, exponent } => (*base, exponent),
        base => (base, 1),
    }
}
```

Instead, do this:

```rust
impl GroupExpr<G: Group> {
    fn split_power(self) -> (GroupExpr<G>, isize) {
        match self {
            GroupExpr::Inv(base) => (base, -1),
            GroupExpr::Pow { base, exponent } => (base, exponent),
            base => (base, 1),
        }
    }
}
```
