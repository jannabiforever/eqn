# Rule 003 - Blanket implementation

As canonical expressions lie, algebras and spaces are encoded as tuples.

For example, in measure theory, `(X, \Sigma)` represents a measurable space.
So the api must provide immediate inference for the tuple, such as

```rust
impl MeasurableSpace for (X, Sigma)
where
    X: Set,
    Sigma: SigmaAlgebra<X>
{
    fn some_trait_function(&self) -> Return {
        ...
    }
}
```

so that the users would just call the methods as

```rust
use MeasurableSpace;

let head_tail_measure_space = (HeadTailSet, HeadTailSetSigmaAlgebra);
head_tail_measure_space.some_trait_function();
```
