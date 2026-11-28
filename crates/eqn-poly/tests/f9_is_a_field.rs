use eqn_algebra::field::Field;
use eqn_algebra::ring::SemiRing;
use eqn_poly::finite_field::PrimitiveFiniteField;

type F9 = PrimitiveFiniteField<3, 2>;

#[test]
fn the_generator_of_f9_has_multiplicative_order_eight() {
    let a = F9::generator();

    assert_eq!(F9::pow(a.clone(), 8), F9::one());
    for k in 1..8 {
        assert_ne!(F9::pow(a.clone(), k), F9::one());
    }
}

#[test]
fn every_nonzero_element_of_f9_times_its_inverse_is_one() {
    for i in 1..9 {
        let value = F9::from_values([i % 3, i / 3]);

        assert_eq!(F9::multiply(value.clone(), F9::invert(value)), F9::one());
    }
}

#[test]
fn the_generator_of_f9_is_a_root_of_the_defining_polynomial() {
    assert_eq!(
        F9::evaluate_base_polynomial(&F9::modulus(), F9::generator()),
        F9::zero()
    );
}
