# Rule 008 - Subsets and quotients

A set is a type; its values are its elements. `Set` marks a type whose `Eq`
is equality of canonical representations. Membership is the typing judgment
`x: S`, decided by the compiler, so `Set` carries no membership predicate and
this library has no `\in`. A name for a set is a type alias, never a second
type.

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

## A quotient is a new type

The parent keeps its structural `Eq`. The quotient is a different type whose
equality is equality of chosen representatives. Its input is a normal form;
an equivalence is the specification the normal form must meet:

```rust
pub trait Equivalence<X: Set> {
    fn equivalent(a: &X, b: &X) -> bool;
}

pub trait NormalForm<X: Set> {
    fn reduce(a: X) -> X;
}
```

`EqClass<X, N>` is the one class type. It holds the representative that the
normal form `N` chooses, so its `Eq`, `Hash` and `Ord` are those of `X`. A
quotient is a set only through a normal form. An equivalence is the
specification a normal form is tested against: `Modulo<S>` is the left-coset
relation of a subgroup, and a normal form for `G/N` must agree with
`Modulo<N>`. A `PartialEq` written by hand on a representative is the setoid
pattern and is not used.

An identity is a function, `identity()`, not a `const`: the identity of a
quotient is the reduced form of the parent's, and reduction is not `const`.

An ideal is a normal subgroup of the ring's additive group that absorbs
multiplication, so a quotient ring adds its classes with the group quotient
operator. A subgroup of an abelian group is normal, as a blanket impl.

## Two things the compiler refuses

- No blanket `impl<N: NormalForm<X>> Equivalence<X> for N`. It conflicts
  (E0119) with the impl on any generic adapter such as `Modulo<S>`, because
  a downstream crate may implement `NormalForm` for `Modulo<T>`. The
  agreement between a normal form and a relation is a test, not an impl.
- Pin a parent group by its parts, `Monoid<Domain = D, Operator = Op>`, not
  by the tuple `(Op,)`. Inside a trait definition
  `<(Op,) as Monoid>::Domain` does not normalize (E0271).

## Why markers lose nothing

A law is a mere proposition: any two proofs of it are equal. A structure is
therefore determined by its data, and the proof can be erased into a marker
trait without losing information. This is Rule 1 of `AGENT.md`, and it is
also why a witness of membership can be a private constructor rather than a
field.
