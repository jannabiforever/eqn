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
- **Relations are bounds.** If mathematics relates two notions, express the
  relation as a trait bound or a conversion, so the compiler infers the
  second from the first. Never ask an implementor to state what the bounds
  already prove.

## Rule 2. Test the laws you cannot encode

Some laws cannot be checked by the compiler or decided in finite time.
Associativity is declared, not verified. Continuity of a map is not
expressible at all. For every such law:

- Every concrete instance of a structure has a test that exercises the law
  on real elements.
- Every blanket impl has a test that a concrete type satisfies its bound.
- Test names are propositions that could be false. If a name cannot be
  false, rename it.

## Rule 3. Respect the code patterns

Every rule in `.pattern/` is binding. Read the folder before writing code,
and reread it before finishing. It covers `derive_where`, comment style,
blanket impls on tuples, the ban on free functions, and law tests.

## Before you finish

`cargo fmt --check`, `cargo clippy --workspace --all-targets -- -D warnings`,
`cargo test --workspace`. Then reread every doc comment you touched and ask
whether a reader with an algebra textbook and no access to the code would
agree it is true.
