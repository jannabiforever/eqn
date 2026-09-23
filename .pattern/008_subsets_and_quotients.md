# Rule 008 - Subsets and quotients

A set is a type; its values are its elements. Membership is the typing
judgment `x: S`, decided by the compiler, so `Set` carries no membership
predicate and this library has no `\in`. A name for a set is a type alias,
never a second type.

## A subset is a predicate

```rust
pub trait Subset {
    type Superset: Set;
    fn contains(element: &Self::Superset) -> bool;
}
```

A substructure is `Subset` plus a marker for its closure laws: a submonoid
contains the identity and is closed under the operation, an ideal absorbs
multiplication. The marker carries `type Parent`, the ambient structure, and
nothing else. `contains` is declared once, here, and never again on a
structure trait.

A `Subset` is not a domain. Its elements are elements of the superset, so
`Symbol<S>` or `Expr::Const` over it would let a non-member through. When a
substructure must be a domain, to carry symbols or to compute inside it, it
gets its own element type: a newtype whose private constructor is the erased
proof in `\Sigma (x : A), P(x)`, and whose equality is structural.

An inclusion that changes the carrier, such as `\mathbb{Z} \subset
\mathbb{Q}`, is a `Map`, never a `Subset`.

## One thing the compiler refuses

- Pin a parent group by its parts, `Monoid<Domain = D, Operator = Op>`, not
  by the tuple `(Op,)`. Inside a trait definition
  `<(Op,) as Monoid>::Domain` does not normalize (E0271).

## Why markers lose nothing

A law is a mere proposition: any two proofs of it are equal. A structure is
therefore determined by its data, and the proof can be erased into a marker
trait without losing information. This is Rule 1 of `AGENT.md`, and it is
also why a witness of membership can be a private constructor rather than a
field.
