# EQN

A Rust library that declares algebraic structures as types and rewrites
expressions using only the laws those types declare. The equation solver
built on the same premises is the work ahead.

[SymPy](https://www.sympy.org) manipulates expressions and hopes the algebra
behind them holds. Here the algebra is stated first, the way a textbook
states it, and the type system holds the author to it. A law the type does
not declare is a law the rewriter cannot use. EQN is not a proof assistant:
a declared law is tested on elements, never proven.

## Crates

| Crate          | Contents                                                                                                                                                                                                                                                                                     |
| -------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `eqn-core`     | `Set` and `Subset`, `BinaryOperator`, the law markers (`Associative`, `Commutative`, `Identity`, `Inverse`), `Map`, `Symbol`, the `Expression` / `Rewriter` traits every tree implements, and `Quotient`, a quotient by an `Equivalence` or a `NormalForm`. Concrete sets `N`, `Z` and `Q`, exact at any size, `R`, and the inclusions between them. |
| `eqn-macros`   | Derives for the above: `#[derive(Set)]`, `#[derive(BinaryOperator)]` with `#[operator(domain, apply, identity, inverse)]`, and the marker derives.                                                                                                                                           |
| `eqn-algebra`  | Monoid, group, ring, field, module, algebra, and their substructures, ideals, and quotients. One rewriter per structure, one more for each law that unlocks a stronger canonical form. Prime fields `F_p` and the field-extension hierarchy up to Galois.                                    |
| `eqn-poly`     | `PolynomialRing<R>`, the free commutative `R`-algebra on its symbols with `\partial / \partial s`. Finite fields `F_{p^n}` as `F_p[x]/(M)`, with irreducible, primitive, and pseudo-Conway defining polynomials found by search.                                                             |
| `eqn-analysis` | `ElementaryExpr<F>`: exp, log, sin, cos over a field, with symbolic differentiation. Its rewriter eliminates every unevaluated derivative and yields a sorted sum of products.                                                                                                               |
| `eqn-diffgeom` | A `Manifold` is its `DifferentialRing` of functions. `DifferentialForm<M>`, `Chart<M>` with the contract `\partial_i x^j = \delta_{ij}`, and the exterior derivative, where `d^2 = 0` falls out of the coefficient ring's own `derive`.                                                      |

## A small example

```rust
use eqn_algebra::group::{AbelianGroupRewriter, GroupExpr, GroupRewriter};
use eqn_algebra::operator_impl::ZAdd;
use eqn_core::rewriter::Expression;
use eqn_core::set::Z;
use eqn_core::symbol::Symbol;

// x + y - x, written in the group's operation.
let expr = "x + y - x".parse::<GroupExpr<(ZAdd,)>>().unwrap();

// The abelian rewriter may reorder terms, so x cancels -x.
assert_eq!(expr.rewritten(&AbelianGroupRewriter::new()), Symbol::new("y").into());

// GroupRewriter, which lacks the commutative law, leaves the conjugate alone.
assert_ne!(expr.rewritten(&GroupRewriter::new()), Symbol::new("y").into());
```

## Building

The library compiles on stable Rust. The workspace still tracks a pinned
nightly (see `rust-toolchain.toml`) because `.rustfmt.toml` uses nightly-only
formatting options; nothing in the crates themselves needs it. A `flake.nix`
and `.devcontainer` provide the same toolchain.

```bash
cargo test --workspace
```

CI runs `cargo fmt --check`, `cargo clippy --workspace --all-targets -D
warnings`, and the tests on both the pinned nightly and stable. All four must
pass. There are no warnings in this repository, allowed or otherwise.
