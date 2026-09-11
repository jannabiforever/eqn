# Rule 005 - Law tests

Rust checks that an operator _declared_ `Associative`. It cannot check that
it _is_. Every law the compiler cannot verify is covered by a test, in one of
three shapes.

## Concrete instances exercise the law on real elements

Enumerate a small, representative set of elements and check the law on every
combination. For a finite structure, check all of them.

```rust
#[test]
fn inverse_satisfies_both_group_laws() {
    for value in [-10, -1, 0, 1, 10] {
        let inverse = IntegerAdditionGroup::inverse(value);
        assert_eq!(IntegerAdditionGroup::apply(inverse, value), IntegerAdditionGroup::IDENTITY);
        assert_eq!(IntegerAdditionGroup::apply(value, inverse), IntegerAdditionGroup::IDENTITY);
    }
}
```

## Blanket impls get a bound check

A blanket impl is a theorem: "anything with these bounds is a `Group`". Its
test is that a concrete type is accepted by the bound. An empty generic
function is the whole assertion.

```rust
#[test]
fn quotient_of_an_abelian_group_is_abelian() {
    fn assert_abelian<G: AbelianGroup>() {}

    assert_abelian::<IntegersModTwo>();
}
```

## Derived structures test well-definedness

When a structure is built from another (a quotient, a coset, a residue
class), test that the result does not depend on the choices made in the
construction.

```rust
#[test]
fn quotient_operation_does_not_depend_on_representatives() {
    let product = IntegersModTwo::apply(modulo_two(1), modulo_two(2));
    let same_product = IntegersModTwo::apply(modulo_two(3), modulo_two(4));

    assert_eq!(product, same_product);
}
```

## Names are propositions

A test name is a claim that could be false:
`rotations_are_normal_in_the_triangle_symmetry_group`,
`coset_equality_is_an_equivalence_relation`. Names like `test_quotient` or
`it_works` are not allowed.
