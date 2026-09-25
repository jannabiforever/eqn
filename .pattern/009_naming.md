# Rule 009 - Naming

A type is a set, so a type is named as its set is named, never after one of
its elements. `Z` is the integers, `Fp<P>` is `\mathbb{F}_p`, and
`Quotient<X, N>` is `X / N`. A name that says "element", "class" or "coset"
names a value, not a type.

A set with a name of its own is its own type, not an alias of the machine
type that represents it. `Z` wraps `i64` because the integers are not the
64-bit integers: the representation can change without the set changing. A
set with no symbol of its own is named by the noun for what it contains, in
the singular, as Mathlib does: `Polynomial<R>` is `R[X]`, and `Symbol<D>` is
the set of symbols over `D`.

A structure is the tuple of its operations (Rule 003), named, when it is
named at all, by what it is: `PrimeField<P>` is `(FpAdd<P>, FpMul<P>)` and
`QuotientGroup<N>` is `(QuotientOp<N>,)`. An operator is the set's name
followed by its operation: `ZAdd`, `QMul`, `FpAdd<P>`, `FqMul<P, N, M>`. So a
set, its operators and its structure read as one family: `Z`, `ZAdd`,
`ZMul`, `(ZAdd, ZMul)`.
