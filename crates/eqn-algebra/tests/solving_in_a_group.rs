use eqn_algebra::group::GroupExpr;
use eqn_algebra::group::rewriter::AbelianGroupRewriter;
use eqn_algebra::group::solver::AbelianGroupSolver;
use eqn_algebra::operator_impl::ZAdd;
use eqn_core::rewriter::Expression;
use eqn_core::set::Z;
use eqn_core::solver::{Equation, SolutionSet};
use eqn_core::symbol::Symbol;

type Expr = GroupExpr<(ZAdd,)>;

#[test]
fn a_plus_x_equals_b_is_solved_by_b_minus_a() {
    let equation: Equation<Expr> = "a + x = b".parse().unwrap();
    let difference: Expr = "b - a".parse().unwrap();

    assert_eq!(
        equation.solve_for(&Symbol::new("x"), &AbelianGroupSolver::new()),
        SolutionSet::Finite(vec![difference.rewritten(&AbelianGroupRewriter::new())])
    );
}

#[test]
fn a_conjugate_cancels_when_solving_in_an_abelian_group() {
    let equation: Equation<Expr> = "x + y - x = 3".parse().unwrap();

    assert_eq!(
        equation.solve_for(&Symbol::new("y"), &AbelianGroupSolver::new()),
        SolutionSet::Finite(vec![Expr::Const(Z::from(3))])
    );
}
