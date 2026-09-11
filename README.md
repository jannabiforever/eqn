# EQN

A Rust library for computing with mathematical structures, stated the way a
textbook states them.

EQN is to [SymPy](https://www.sympy.org) what a proof is to a worked example.
SymPy manipulates expressions and hopes the algebra behind them holds.

Expressions come afterwards, and the rewriter that simplifies them is allowed
to use exactly the laws the structure declares and nothing else.

## Crates

| Crate          | Contents                                                                                                                                                                                                                                                  |
| -------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `eqn-core`     | `Set`, `BinaryOperator`, the law markers (`Associative`, `Commutative`, `Identity`, `Inverse`), `Map`, `Symbol`, and the `Expression` / `Rewriter` traits every tree implements. Concrete sets `N`, `Z`, `Q`, `R`.                                        |
| `eqn-macros`   | Derives for the above: `#[derive(Set)]`, `#[derive(BinaryOperator)]` with `#[operator(domain, apply, identity, inverse)]`, and the marker derives.                                                                                                        |
| `eqn-algebra`  | Monoid, group, ring, field, module, algebra, and their substructures, ideals, and quotients. One rewriter per structure, one more for each law that unlocks a stronger canonical form. Prime fields `F_p` and the field-extension hierarchy up to Galois. |
| `eqn-poly`     | `PolynomialRing<R>`, the free commutative `R`-algebra on its symbols with `\partial / \partial s`. Finite fields `F_{p^n}` as `F_p[x]/(M)`, with irreducible, primitive, and pseudo-Conway defining polynomials found by search.                          |
| `eqn-analysis` | `ElementaryExpr<F>`: exp, log, sin, cos over a field, with symbolic differentiation. Its rewriter eliminates every unevaluated derivative and yields a sorted sum of products.                                                                            |
| `eqn-diffgeom` | A `Manifold` is its `DifferentialRing` of functions. `DifferentialForm<M>`, `Chart<M>` with the contract `\partial_i x^j = \delta_{ij}`, and the exterior derivative, where `d^2 = 0` falls out of the coefficient ring's own `derive`.                   |

## A small example

```rust
use eqn_algebra::group::{AbelianGroupRewriter, GroupExpr};
use eqn_algebra::operator_impl::ZAdd;
use eqn_core::rewriter::Expression;
use eqn_core::set::Z;
use eqn_core::symbol::Symbol;

// x * y * x^{-1}, written in the group's operation.
let expr = "x * y * x^{-1}".parse::<GroupExpr<(Z, ZAdd)>>().unwrap();

// The abelian rewriter may reorder factors, so x cancels x^{-1}.
// GroupRewriter, which lacks the commutative law, would leave it alone.
assert_eq!(expr.rewritten(&AbelianGroupRewriter), Symbol::new("y").into());
```

## Building

The workspace tracks a pinned nightly (see `rust-toolchain.toml`) for
`min_generic_const_args`, which lets a field extension carry its degree and a
manifold its dimension as associated constants. A `flake.nix` and
`.devcontainer` provide the same toolchain.

```bash
cargo test --workspace
```

CI runs `cargo fmt --check`, `cargo clippy --workspace --all-targets -D
warnings`, and the tests. All three must pass. There are no warnings in this
repository, allowed or otherwise.
