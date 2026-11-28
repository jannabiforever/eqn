use eqn_core::rewriter::{Expression, Rewriter};
use eqn_core::solver::{Equation, SolutionSet, Solver};
use eqn_core::symbol::Symbol;

use super::rewriter::{AbelianGroupRewriter, GroupRewriter};
use super::{AbelianGroup, Group, GroupExpr};

impl<G: Group> GroupExpr<G> {
    /// The values of `unknown` that satisfy `equation`, found by the laws
    /// `rewriter` normalizes with. In a group `lhs = rhs` exactly when
    /// `lhs rhs^{-1} = e`, and `A f B = e` exactly when `f = A^{-1} B^{-1}`;
    /// a factor `f` that is the unknown, its inverse or a power of it is
    /// isolated this way.
    fn isolate<R>(
        equation: Equation<Self>,
        unknown: &Symbol<G::Domain>,
        rewriter: &R,
    ) -> SolutionSet<Self>
    where
        R: Rewriter<Expr = Self>,
    {
        let product =
            Self::Op(vec![equation.lhs, Self::Inv(Box::new(equation.rhs))]).rewrite(rewriter);
        let factors = match &product {
            Self::Op(factors) => factors.as_slice(),
            product => std::slice::from_ref(product),
        };
        let occurrences: Vec<usize> = factors
            .iter()
            .enumerate()
            .filter(|(_, factor)| {
                std::iter::once(*factor)
                    .chain(factor.descendants())
                    .any(|e| e.as_symbol() == Some(unknown))
            })
            .map(|(i, _)| i)
            .collect();
        let condition =
            || SolutionSet::Condition(Equation::new(product.clone(), Self::Const(G::identity())));

        match occurrences[..] {
            [] => match &product {
                Self::Const(value) if *value == G::identity() => SolutionSet::All,
                Self::Const(_) => SolutionSet::Finite(vec![]),
                _ => condition(),
            },
            [i] => {
                let inverse = |factors: &[Self]| Self::Inv(Box::new(Self::Op(factors.to_vec())));
                let value = Self::Op(vec![inverse(&factors[..i]), inverse(&factors[i + 1..])])
                    .rewrite(rewriter);
                match &factors[i] {
                    Self::Symbol(_) => SolutionSet::Finite(vec![value]),
                    Self::Inv(base) if base.as_symbol() == Some(unknown) => {
                        SolutionSet::Finite(vec![Self::Inv(Box::new(value)).rewrite(rewriter)])
                    }
                    // NOTE: an n-th root is not a group notion.
                    power @ Self::Pow { base, .. } if base.as_symbol() == Some(unknown) => {
                        SolutionSet::Condition(Equation::new(power.clone(), value))
                    }
                    _ => condition(),
                }
            }
            _ => condition(),
        }
    }
}

/// Solves equations in a group by the group laws alone, which keep the order
/// of factors.
#[derive_where::derive_where(Default)]
pub struct GroupSolver<G: Group> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: Group> GroupSolver<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: Group> Solver for GroupSolver<G> {
    type Expr = GroupExpr<G>;

    fn solve(
        &self,
        equation: Equation<Self::Expr>,
        unknown: &Symbol<G::Domain>,
    ) -> SolutionSet<Self::Expr> {
        GroupExpr::isolate(equation, unknown, &GroupRewriter::new())
    }
}

/// Solves equations in an abelian group, where factors also commute.
#[derive_where::derive_where(Default)]
pub struct AbelianGroupSolver<G: AbelianGroup> {
    _marker: std::marker::PhantomData<G>,
}

impl<G: AbelianGroup> AbelianGroupSolver<G> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<G: AbelianGroup> Solver for AbelianGroupSolver<G> {
    type Expr = GroupExpr<G>;

    fn solve(
        &self,
        equation: Equation<Self::Expr>,
        unknown: &Symbol<G::Domain>,
    ) -> SolutionSet<Self::Expr> {
        GroupExpr::isolate(equation, unknown, &AbelianGroupRewriter::new())
    }
}

#[cfg(test)]
mod tests {
    use eqn_core::op::BinaryOperator;
    use eqn_core::quotient::{Congruence, NormalForm, Quotient};
    use eqn_parser::ParseError;

    use super::super::tests::*;
    use super::*;
    use crate::group::normal::NormalSubgroup;
    use crate::group::quotient::QuotientGroup;
    use crate::monoid::MonoidElem;
    use crate::operator_impl::QMul;

    fn equation(src: &str) -> Equation<Expr> {
        src.parse().unwrap()
    }

    fn x<D: eqn_core::set::Set>() -> Symbol<D> {
        Symbol::new("x")
    }

    fn error<E>(src: &str) -> ParseError
    where
        E: Expression + eqn_parser::FromAst + std::fmt::Debug,
    {
        src.parse::<Equation<E>>().unwrap_err().downcast().unwrap()
    }

    struct MultiplesOfSix;

    impl NormalForm<i64> for MultiplesOfSix {
        fn reduce(value: i64) -> i64 {
            value.rem_euclid(6)
        }
    }

    impl Congruence<Addition> for MultiplesOfSix {}

    impl NormalSubgroup for MultiplesOfSix {
        type Group = IntegerAdditionGroup;
    }

    type IntegersModSix = QuotientGroup<MultiplesOfSix>;

    #[test]
    fn reduction_mod_six_is_a_congruence_for_addition() {
        for a in -12..=12 {
            for b in -12..=12 {
                assert_eq!(
                    MultiplesOfSix::reduce(Addition::apply(a, b)),
                    MultiplesOfSix::reduce(Addition::apply(
                        MultiplesOfSix::reduce(a),
                        MultiplesOfSix::reduce(b)
                    ))
                );
            }
        }
    }

    /// `expr` with each integer constant `n` carried to `element(n)` in `H`.
    fn carried<H: Group>(expr: Expr, element: &impl Fn(i64) -> MonoidElem<H>) -> GroupExpr<H> {
        match expr {
            Expr::Const(n) => GroupExpr::Const(element(n)),
            Expr::Symbol(symbol) => GroupExpr::Symbol(Symbol::new(symbol.name)),
            Expr::Inv(inner) => GroupExpr::Inv(Box::new(carried(*inner, element))),
            Expr::Op(factors) => {
                GroupExpr::Op(factors.into_iter().map(|f| carried(f, element)).collect())
            }
            Expr::Pow { base, exponent } => GroupExpr::Pow {
                base: Box::new(carried(*base, element)),
                exponent,
            },
        }
    }

    /// `src` read over the integers, then carried into `H` by `element`.
    fn equation_in<H: Group>(
        src: &str,
        element: impl Fn(i64) -> MonoidElem<H>,
    ) -> Equation<GroupExpr<H>> {
        let Equation { lhs, rhs } = equation(src);
        Equation::new(carried(lhs, &element), carried(rhs, &element))
    }

    /// The elements `g` with `lhs[x := g] = rhs[x := g]`, found by trying
    /// each one.
    fn satisfying<G: Group>(
        equation: &Equation<GroupExpr<G>>,
        elements: &[MonoidElem<G>],
    ) -> Vec<MonoidElem<G>> {
        let rewriter = GroupRewriter::new();
        elements
            .iter()
            .filter(|g| {
                let Equation { lhs, rhs } = equation
                    .clone()
                    .substituted(x(), &GroupExpr::Const((*g).clone()));
                lhs.rewrite(&rewriter) == rhs.rewrite(&rewriter)
            })
            .cloned()
            .collect()
    }

    fn assert_solves_exactly<G, S>(
        solver: &S,
        equation: Equation<GroupExpr<G>>,
        elements: &[MonoidElem<G>],
    ) where
        G: Group,
        S: Solver<Expr = GroupExpr<G>>,
    {
        let solved = match equation.clone().solve_for(&x(), solver) {
            SolutionSet::Finite(values) => {
                let found: Vec<_> = elements
                    .iter()
                    .filter(|g| values.contains(&GroupExpr::Const((*g).clone())))
                    .cloned()
                    .collect();
                assert_eq!(found.len(), values.len(), "{values:?} for {equation:?}");
                found
            }
            SolutionSet::All => elements.to_vec(),
            SolutionSet::Condition(condition) => satisfying(&condition, elements),
        };
        assert_eq!(solved, satisfying(&equation, elements), "{equation:?}");
    }

    fn assert_satisfies<S, R>(solver: &S, rewriter: &R, src: &str)
    where
        S: Solver<Expr = Expr>,
        R: Rewriter<Expr = Expr>,
    {
        let SolutionSet::Finite(solutions) = equation(src).solve_for(&x(), solver) else {
            panic!("`{src}` was not solved");
        };
        let [solution] = &solutions[..] else {
            panic!("`{src}` has one solution, not {solutions:?}");
        };
        let Equation { lhs, rhs } = equation(src).substituted(x(), solution);
        assert_eq!(lhs.rewrite(rewriter), rhs.rewrite(rewriter), "{src}");
    }

    #[test]
    fn the_isolated_solution_satisfies_the_equation() {
        for src in ["x + a = b", "a + x + b = c", "inv(x) = a", "a - x = b"] {
            assert_satisfies(&GroupSolver::new(), &GroupRewriter::new(), src);
            assert_satisfies(
                &AbelianGroupSolver::new(),
                &AbelianGroupRewriter::new(),
                src,
            );
        }
    }

    #[test]
    fn the_factors_around_the_unknown_are_inverted_in_order() {
        assert_eq!(
            equation("a x b = c").solve_for(&x(), &GroupSolver::new()),
            SolutionSet::Finite(vec![expr("inv(a) c inv(b)")])
        );
    }

    #[test]
    fn every_solution_in_a_finite_group_is_found_and_nothing_else() {
        let symmetry = |n: i64| symmetries()[n as usize];
        for src in [
            "1 x 3 = 4",
            "3 x 4 = 0",
            "inv(x) 2 = 5",
            "3 x^2 = 3",
            "x x = 0",
            "x x x = 0",
            "x 3 inv(x) = 4",
            "x 1 = x 2",
            "x = x",
            "1 = 2",
        ] {
            let equation = equation_in::<D3>(src, symmetry);
            assert_solves_exactly(&GroupSolver::new(), equation, &symmetries());
        }

        let residue = Quotient::<i64, MultiplesOfSix>::new;
        let residues: Vec<_> = (0..6).map(residue).collect();
        for src in [
            "x + 2 = 5",
            "2 + x + 3 = 1",
            "inv(x) = 1",
            "4 - x = 1",
            "x + x = 4",
            "x + x + x = 0",
            "x + 1 = x",
            "x + 3 - x = 3",
            "1 = 7",
        ] {
            let equation = equation_in::<IntegersModSix>(src, residue);
            assert_solves_exactly(&GroupSolver::new(), equation.clone(), &residues);
            assert_solves_exactly(&AbelianGroupSolver::new(), equation, &residues);
        }
    }

    #[test]
    fn an_unknown_that_cancels_leaves_a_condition_on_the_parameters() {
        assert_eq!(
            equation("x + a = x + b").solve_for(&x(), &AbelianGroupSolver::new()),
            SolutionSet::Condition(equation("a + inv(b) = 0"))
        );
    }

    #[test]
    fn contradictions_have_no_solution_and_identities_have_every_element() {
        let (group, abelian) = (GroupSolver::new(), AbelianGroupSolver::new());

        assert_eq!(
            equation("x + 1 = x").solve_for(&x(), &abelian),
            SolutionSet::Finite(vec![])
        );
        for (src, expected) in [
            ("2 = 3", SolutionSet::Finite(vec![])),
            ("x = x", SolutionSet::All),
            ("3 = 3", SolutionSet::All),
        ] {
            assert_eq!(equation(src).solve_for(&x(), &group), expected, "{src}");
            assert_eq!(equation(src).solve_for(&x(), &abelian), expected, "{src}");
        }
    }

    #[test]
    fn a_power_of_the_unknown_is_returned_as_a_condition() {
        let expected = SolutionSet::Condition(equation("x^2 = 4"));

        assert_eq!(
            equation("x + x = 4").solve_for(&x(), &GroupSolver::new()),
            expected
        );
        assert_eq!(
            equation("x + x = 4").solve_for(&x(), &AbelianGroupSolver::new()),
            expected
        );
    }

    #[test]
    fn only_the_abelian_solver_sees_through_a_conjugate() {
        assert_eq!(
            equation("x + a - x = b").solve_for(&x(), &GroupSolver::new()),
            SolutionSet::Condition(equation("x + a - x - b = 0"))
        );
        assert_eq!(
            equation("x + a - x = b").solve_for(&x(), &AbelianGroupSolver::new()),
            SolutionSet::Condition(equation("a + inv(b) = 0"))
        );
    }

    #[test]
    fn solutions_are_in_normal_form() {
        fn expressions(set: SolutionSet<Expr>) -> Vec<Expr> {
            match set {
                SolutionSet::Finite(values) => values,
                SolutionSet::All => vec![],
                SolutionSet::Condition(Equation { lhs, rhs }) => vec![lhs, rhs],
            }
        }

        for src in [
            "a + x + b = c + 2",
            "inv(x) + a = b",
            "a - x = b + 2",
            "x + x = a + 4",
            "x + a = x + b",
            "x + a - x = b",
            "(x + a)^2 = b",
        ] {
            for e in expressions(equation(src).solve_for(&x(), &GroupSolver::new())) {
                assert_eq!(e.rewritten(&GroupRewriter::new()), e, "{src}");
            }
            for e in expressions(equation(src).solve_for(&x(), &AbelianGroupSolver::new())) {
                assert_eq!(e.rewritten(&AbelianGroupRewriter::new()), e, "{src}");
            }
        }
    }

    #[test]
    fn equations_parse_with_the_expressions_own_grammar() {
        type Mul = GroupExpr<(QMul,)>;

        assert_eq!(
            equation("x + a = -3"),
            Equation::new(expr("x + a"), expr("-3"))
        );
        assert_eq!(
            "x / y = 2".parse::<Equation<Mul>>().unwrap(),
            Equation::new("x / y".parse().unwrap(), "2".parse().unwrap())
        );
        assert_eq!(
            error::<Mul>("x + y = 2"),
            ParseError::at(2, "unexpected `+`")
        );
        assert_eq!(
            error::<Expr>("= b"),
            ParseError::at(0, "expected an expression, found `=`")
        );
        assert_eq!(
            error::<Expr>("a ="),
            ParseError::at(3, "expected an expression, found end of input")
        );
    }

    #[test]
    fn an_equation_has_exactly_one_equals_sign() {
        let not_outermost = ParseError::new("`=` must be the outermost operator of an equation");

        for src in ["a = b = c", "a = (b = c)", "inv(a = b) = c", "(a = b)"] {
            assert_eq!(error::<Expr>(src), not_outermost, "{src}");
        }
        assert_eq!(
            error::<Expr>("x + a"),
            ParseError::new("an equation needs `=` between its two sides")
        );
    }

    #[test]
    fn substitution_reaches_both_sides() {
        let mut substituted = equation("x + a = inv(x)");
        substituted.substitute(x(), &expr("b"));

        assert_eq!(substituted, equation("b + a = inv(b)"));
        assert_eq!(
            equation("x = a").substituted(Symbol::new("a"), &expr("x")),
            equation("x = x")
        );
    }
}
