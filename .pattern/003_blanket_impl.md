# Rule 003 - Blanket implementation

A structure is the tuple of its operations. The carrier is not a component:
every operation carries its domain, so the operations determine the set, and
a tuple with the carrier in it would have one value per element instead of
one value per structure. The tuple of operations is zero-sized, so its one
value is the structure.

A monoid is a one-tuple and a ring is a pair, and the api must provide
immediate inference for the tuple:

```rust
impl<Op> Monoid for (Op,)
where
    Op: BinaryOperator + Associative + Identity,
{
    type Domain = Op::Domain;
    type Operator = Op;
}
```

so that users name a structure by its operations and call the associated
functions on the type:

```rust
type Integers = (ZAdd, ZMul);

Integers::add(2, 3);
```

A structure with data of its own, such as a module with its scalars, is a
struct that implements the trait directly.
