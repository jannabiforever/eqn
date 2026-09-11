# Rule 002 - Comment style

## Doc comments

Doc comments, they open with the mathematical object ("A two-sided ideal of a
ring."), state the hypotheses, and then say what the code does with them. They
do not advertise, hedge, or repeat the signature. A `NOTE` marks a deliberate
choice that could be mistaken for an oversight. A `TODO` marks a known gap.
Nothing else is annotated.

**Never make them lie**. As code evolves, too specific, technical comments
could become outdated or misleading. This kind of comments are not allowed
in this project. So be abstract on what's going on. Abstract concept doesn't
change even if the coverage changes. Bad comments, are even worse than no
comments.

For example, this kind of comments:

```rust
/// A natural number. Natural numbers are encoded with usize for convenience.
pub struct NaturalNumber(usize);
```

are very concrete and speicfic about what really is going on, therefore
vulnerable on changes. So instead, do this:

```rust
/// A natural number.
pub struct NaturalNumber(usize);
```

or even this: (in case the name of it represents itself well enough)

```rust
pub struct NaturalNumber(usize);
```

## Comment style

Non-ascii character in this project is considered an anti-pattern. If you need
any mathematical notation, use latex.

```rust
/// Represents a partial derivative expression, \partial_i
pub struct PartialDerivative(usize);
```
