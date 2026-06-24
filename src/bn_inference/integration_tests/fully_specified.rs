use biodivine_algo_smt_inference::bn_inference::constraints::{StateIsFixedPoint, ValueComparison};
use biodivine_algo_smt_inference::bn_inference::integration_tests::build_test_solver;
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_algo_smt_inference::smt_solver::DynMonotoneBoundedIntSolver;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, RegulatoryGraph};
use z3::SatResult;

#[test]
fn fully_specified_positive() {
    // Test that fully specified functions can be encoded/decoded and are honored by the solver.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -> out
        b -| out
        $out: a & !b
    "#,
    )
    .unwrap();

    let out = psbn.as_graph().find_variable("out").unwrap();

    let mut solver = build_test_solver();

    let problem = InferenceProblem::from_partially_specified_network(&psbn).unwrap();
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true).unwrap();

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let inferred = encoder
        .decode_boolean_network(&solver, &model, true)
        .unwrap();

    // For complex functions, the translation could produce a different syntax; but this function
    // is so simple the output should be deterministically the same.
    assert_eq!(
        inferred.get_update_function(out),
        psbn.get_update_function(out)
    );
}

#[test]
fn fully_specified_with_fix() {
    // Test that setting a fully specified function can enforce specific values for other functions.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -> out
        b -| out
        $out: a & !b
    "#,
    )
    .unwrap();

    let a = psbn.as_graph().find_variable("a").unwrap();
    let b = psbn.as_graph().find_variable("b").unwrap();
    let out = psbn.as_graph().find_variable("out").unwrap();

    let mut solver = build_test_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&psbn).unwrap();

    // Assert that there is a fixed-point with `out=1`; This should enforce `$a: true` and `$b: false`.
    assert!(problem.declare_state("test_state"));
    problem
        .assert_constraint(StateIsFixedPoint::new("test_state"))
        .unwrap();
    problem
        .assert_constraint(ValueComparison::variable_assignment("test_state", out, 1))
        .unwrap();

    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true).unwrap();

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let inferred = encoder
        .decode_boolean_network(&solver, &model, true)
        .unwrap();

    assert_eq!(
        inferred.get_update_function(out),
        psbn.get_update_function(out)
    );
    assert_eq!(inferred.get_update_function(a), &Some(FnUpdate::mk_true()),);
    assert_eq!(inferred.get_update_function(b), &Some(FnUpdate::mk_false()),);
}

#[test]
fn fully_specified_breaks_monotonicity() {
    // Test that fully specified functions that break monotonicity will fail during encoding.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -> out
        b -| out
        $out: a & b
    "#,
    )
    .unwrap();

    let mut solver = build_test_solver();

    let problem = InferenceProblem::from_partially_specified_network(&psbn).unwrap();
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true);
    assert!(
        encoder
            .err()
            .unwrap()
            .to_string()
            .contains("Monotonicity mismatch")
    );
}

#[test]
fn fully_specified_breaks_essentiality() {
    // Test that fully specified functions that break essentiality will fail during encoding.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -> out
        b -| out
        $out: a
    "#,
    )
    .unwrap();

    let mut solver = build_test_solver();

    let problem = InferenceProblem::from_partially_specified_network(&psbn).unwrap();
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true);

    assert!(
        encoder
            .err()
            .unwrap()
            .to_string()
            .contains("Essentiality mismatch")
    );
}

#[test]
fn int_domain_encoding_basic() {
    // A basic test to verify that int variables with uninterpreted functions can be encoded.

    let rg = RegulatoryGraph::try_from("a -> b").unwrap();

    let mut problem = InferenceProblem::<DynMonotoneBoundedIntSolver>::new();
    problem.declare_variable("a", (0, 2));
    problem.declare_variable("b", (0, 1));
    problem.initialize_regulatory_graph(&rg).unwrap();

    assert!(problem.declare_state("s"));
    problem
        .assert_constraint(StateIsFixedPoint::new("s"))
        .unwrap();

    let mut solver = build_test_solver();
    let _encoder = InferenceProblemEncoder::new(problem, &mut solver, false).unwrap();

    assert_eq!(solver.check(), SatResult::Sat);
}
