# AGENT.md

## What this project is

A Rust library for mathematical structures: sets with operators, the laws
those operators satisfy, and expression trees rewritten using exactly those
laws. Think SymPy, but with the algebra stated first and the type system
holding the author to it.

## Rule 1. Reach for the highest inferability

- **Minimal complete axioms.** A new structure is the structure one rung
  below plus the laws that distinguish it. A hypothesis no existing marker
  expresses becomes a new marker trait, never a method or a comment.
  Markers lose nothing: a law is a mere proposition, any two proofs of it
  are equal, so a structure is determined by its data and the proof can be
  erased.
- **Relations are bounds.** If mathematics relates two notions, express the
  relation as a trait bound, a conversion, or an adapter type whose impl
  states the theorem, so the compiler infers the second from the first.
  Never ask an implementor to state what the bounds already prove.
- **Hypotheses on constants are compile-time.** A hypothesis about a const
  generic is forced in a `const` block, so violating it fails to compile.
  A run-time assertion is for a hypothesis about a value.

## Rule 2. Test the laws you cannot encode

Some laws cannot be checked by the compiler or decided in finite time.
Associativity is declared, not verified. Continuity of a map is not
expressible at all. For every such law:

- Every concrete instance of a structure has a test that exercises the law
  on real elements.
- No test restates what the compiler decides. A trait bound, a blanket
  impl and an associated constant are checked when the crate compiles.
- Test names are propositions that could be false. If a name cannot be
  false, rename it.

## Rule 3. Respect the code patterns

Every rule in `.pattern/` is binding. Read the folder before writing code,
and reread it before finishing. It covers `derive_where`, comment style,
blanket impls on tuples, the ban on free functions, law tests, subsets and
quotients, and naming.

## Before you finish

`cargo fmt --check`, `cargo clippy --workspace --all-targets -- -D warnings`,
`cargo test --workspace`. Then reread every doc comment you touched and ask
whether a reader with an algebra textbook and no access to the code would
agree it is true.
