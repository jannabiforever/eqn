# Rule 008 - Sets and quotients

## A set is a type

A set is a type; its values are its elements. `Set` marks a type whose `Eq`
is equality of canonical representations. Membership in a set is the typing
judgment `x: S`, decided by the compiler, so `Set` carries no membership
predicate. How a set is named is Rule 009.

A set carved out of another by a predicate, when one is needed, is its own
type: a newtype whose private constructor is the erased proof in
`\Sigma (x : A), P(x)`, and whose equality is structural. An inclusion that
changes the carrier, such as `\mathbb{Z} \subset \mathbb{Q}`, is a `Map`.

## A quotient is a normal form that is a congruence

The parent keeps its structural `Eq`. The quotient is a different type whose
equality is equality of chosen representatives. Its input is a normal form,
and a quotient structure asks one law more of it: each operation of the
parent respects the classes.

```rust
pub trait NormalForm<X: Set> {
    fn reduce(element: X) -> X;
}

/// reduce(Op(a, b)) == reduce(Op(reduce(a), reduce(b)))
pub trait Congruence<Op: BinaryOperator>: NormalForm<Op::Domain> {}
```

`Quotient<X, N>` is the one quotient type, the set `X / N`. A value is a
class, held by the representative that the normal form `N` chooses, so its
`Eq`, `Hash` and `Ord` are those of `X`. A quotient is a set only through a
normal form. A `PartialEq` written by hand on a representative is the setoid
pattern and is not used.

A normal subgroup is a normal form that is a congruence for its group's
operation, and an ideal is one that is a congruence for both ring
operations. Each carries its parent structure (`type Group`, `type Ring`)
and nothing else, so a ring ideal is four impls: `NormalForm`, a
`Congruence` for each operation, and `Ideal`. The class of the identity is
then a normal subgroup and the classes are its cosets, so membership is
derived from the normal form, never declared: `x` lies in the subgroup when
`reduce(x) == reduce(identity())`, and an ideal is proper when `1` does not
lie in it. Every ideal is a normal subgroup of the ring's additive group, as
a blanket impl, so a quotient ring adds its classes with the group quotient
operator.

An equivalence is the specification a normal form is tested against:

```rust
pub trait Equivalence<X: Set> {
    fn equivalent(a: &X, b: &X) -> bool;
}
```

`Modulo<N>` is the left-coset relation of a normal subgroup: `a` and `b` are
related when `a^{-1} b` lies in `N`. The normal form of `N` must agree with
it, and a normal form that is a congruence does.

The congruence law is declared, never proven. Every congruence has a test
that feeds representatives `reduce` changes through the parent operation and
checks the law on a grid of elements. `Quotient::new` reduces its input, so a
test that compares two products of classes never reaches the law.

An identity is a function, `identity()`, not a `const`: the identity of a
quotient is the reduced form of the parent's, and reduction is not `const`.

## One thing the compiler refuses

- No blanket `impl<N: NormalForm<X>> Equivalence<X> for N`. It conflicts
  (E0119) with the impl on any generic adapter such as `Modulo<N>`, because
  a downstream crate may implement `NormalForm` for `Modulo<T>`. The
  agreement between a normal form and a relation is a test, not an impl.

## Why markers lose nothing

A law is a mere proposition: any two proofs of it are equal. A structure is
therefore determined by its data, and the proof can be erased into a marker
trait without losing information. This is Rule 1 of `AGENT.md`, and it is
also why a witness of membership can be a private constructor rather than a
field.
