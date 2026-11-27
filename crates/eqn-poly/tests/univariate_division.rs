use eqn_algebra::field::{Fp, PrimeField};
use eqn_core::symbol::Symbol;
use eqn_poly::Polynomial;
use eqn_poly::univariate::Univariate;

type F3 = PrimeField<3>;

#[test]
fn x_cubed_plus_one_is_x_plus_one_times_x_squared_minus_x_plus_one_over_f3() {
    let dividend = Univariate::try_from("x^3 + 1".parse::<Polynomial<F3>>().unwrap()).unwrap();
    let divisor = Univariate::<F3>::new([1, 1].map(Fp::new).to_vec());

    let (quotient, remainder) = dividend.div_rem(&divisor);

    assert_eq!(quotient, Univariate::new([1, 2, 1].map(Fp::new).to_vec()));
    assert_eq!(remainder, Univariate::zero());
}

#[test]
fn a_polynomial_in_x_and_y_is_not_univariate_and_the_refusal_names_y() {
    let polynomial = "x*y + 1".parse::<Polynomial<F3>>().unwrap();

    assert_eq!(Univariate::try_from(polynomial), Err(Symbol::new("y")));
}
