use crate::bn_inference::integration_tests::build_test_optimization_solver;
use biodivine_algo_smt_inference::bn_inference::integration_tests::build_test_solver;
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ModelAnnotation, VariableId};
use std::collections::BTreeMap;
use z3::SatResult;

/// Create a simple fully specified network that has variables `a`, `b`, `c`
/// and a single fixed-point `010`.
fn make_one_fixed_point_network() -> (BooleanNetwork, VariableId, VariableId, VariableId) {
    let bn = BooleanNetwork::try_from(
        r#"
            a -?? c
            b -?? c
            $a: false
            $b: true
            $c: a & b
        "#,
    )
    .unwrap();
    (
        bn,
        VariableId::from_index(0),
        VariableId::from_index(1),
        VariableId::from_index(2),
    )
}

/// Same as [`make_one_fixed_point_network`] but the network has
/// two fixed-points, `010` and `111`
fn make_two_fixed_points_network() -> (BooleanNetwork, VariableId, VariableId, VariableId) {
    let bn = BooleanNetwork::try_from(
        r#"
        a -?? a
        a -?? c
        b -?? c
        $a: a
        $b: true
        $c: a & b
        "#,
    )
    .unwrap();
    (
        bn,
        VariableId::from_index(0),
        VariableId::from_index(1),
        VariableId::from_index(2),
    )
}

/// Test that we can find a single fixed-point.
#[test]
fn one_fixed_point_must_positive() -> Result<(), anyhow::Error> {
    let (bn, a, b, c) = make_one_fixed_point_network();

    let mut solver = build_test_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 0 :
        #! comparison : equal : `fix/b`: 1 :
        #! comparison : equal : `fix/c`: 0 :
    "#,
    );
    problem.initialize_constraints(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let fix = encoder.decode_state("fix", &model);
    assert_eq!(fix, BTreeMap::from_iter([(a, 0), (b, 1), (c, 0)]));
    Ok(())
}

/// Test that we can detect that a fixed-point does not exist.
#[test]
fn one_fixed_point_must_negative() -> Result<(), anyhow::Error> {
    let (bn, _, _, _) = make_one_fixed_point_network();

    let mut solver = build_test_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 1 :
        #! comparison : equal : `fix/b`: 1 :
        #! comparison : equal : `fix/c`: 0 :
    "#,
    );
    problem.initialize_constraints(&bn, &properties)?;
    let _encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Unsat);

    Ok(())
}

/// Test that we can detect a fixed-point (010) within distance one of specification (110).
#[test]
fn one_fixed_point_may() -> Result<(), anyhow::Error> {
    let (bn, a, b, c) = make_one_fixed_point_network();

    let mut solver = build_test_optimization_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 1 : weight : 0.5
        #! comparison : equal : `fix/b`: 1 : weight : 0.5
        #! comparison : equal : `fix/c`: 0 : weight : 0.5
    "#,
    );
    problem.initialize_constraints_and_weights(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let fix = encoder.decode_state("fix", &model);
    assert_eq!(fix, BTreeMap::from_iter([(a, 0), (b, 1), (c, 0)]));
    Ok(())
}

/// Test that we can find two distinct fixed-points.
#[test]
fn two_fixed_point_must_positive() -> Result<(), anyhow::Error> {
    let (bn, a, b, c) = make_two_fixed_points_network();

    let mut solver = build_test_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix1
        #! state : fixed_point : fix1 :
        #! comparison : equal : `fix1/a`: 0 :
        #! comparison : equal : `fix1/b`: 1 :
        #! comparison : equal : `fix1/c`: 0 :

        #! state : declare : fix2
        #! state : fixed_point : fix2 :
        #! comparison : equal : `fix2/a`: 1 :
        #! comparison : equal : `fix2/b`: 1 :
        #! comparison : equal : `fix2/c`: 1 :
    "#,
    );
    problem.initialize_constraints(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        encoder.decode_state("fix1", &model),
        BTreeMap::from_iter([(a, 0), (b, 1), (c, 0)])
    );
    assert_eq!(
        encoder.decode_state("fix2", &model),
        BTreeMap::from_iter([(a, 1), (b, 1), (c, 1)])
    );
    Ok(())
}

// Test that we can detect two fixed points (010 and 111) within distance one and two
// of a specification (000 and 101).
#[test]
fn two_fixed_point_may() -> Result<(), anyhow::Error> {
    let (bn, a, b, c) = make_two_fixed_points_network();

    let mut solver = build_test_optimization_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix1
        #! state : fixed_point : fix1 :
        #! comparison : equal : `fix1/a`: 0 : weight : 0.5
        #! comparison : equal : `fix1/b`: 0 : weight : 0.5
        #! comparison : equal : `fix1/c`: 0 : weight : 0.5

        #! state : declare : fix2
        #! state : fixed_point : fix2 :
        #! comparison : equal : `fix2/a`: 1 : weight : 0.5
        #! comparison : equal : `fix2/b`: 0 : weight : 0.5
        #! comparison : equal : `fix2/c`: 1 : weight : 0.5
    "#,
    );
    problem.initialize_constraints_and_weights(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        encoder.decode_state("fix1", &model),
        BTreeMap::from_iter([(a, 0), (b, 1), (c, 0)])
    );
    assert_eq!(
        encoder.decode_state("fix2", &model),
        BTreeMap::from_iter([(a, 1), (b, 1), (c, 1)])
    );
    Ok(())
}

/// Test that we can detect one fixed-point out of two (010 and 111) within distance
/// two of specification (001) where the final fixed-point is determined by
/// specification weights.
#[test]
fn one_in_two_fixed_point_optimize() -> Result<(), anyhow::Error> {
    let (bn, a, b, c) = make_two_fixed_points_network();

    let mut solver = build_test_optimization_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    // First, build the specification such that `010` is the optimal fixed-point.
    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 0 : weight : 0.66
        #! comparison : equal : `fix/b`: 0 : weight : 0.25
        #! comparison : equal : `fix/c`: 1 : weight : 0.25
    "#,
    );
    problem.initialize_constraints_and_weights(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        encoder.decode_state("fix", &model),
        BTreeMap::from_iter([(a, 0), (b, 1), (c, 0)])
    );

    let mut solver = build_test_optimization_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    // Second, rebuild the specification to prefer `111`.
    // 0.25 + 0.25 < 0.66 + 0.25
    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 0 : weight : 0.25
        #! comparison : equal : `fix/b`: 0 : weight : 0.25
        #! comparison : equal : `fix/c`: 1 : weight : 0.66
    "#,
    );
    problem.initialize_constraints_and_weights(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        encoder.decode_state("fix", &model),
        BTreeMap::from_iter([(a, 1), (b, 1), (c, 1)])
    );

    Ok(())
}

#[test]
fn essentiality_positive() -> Result<(), anyhow::Error> {
    let (mut bn, a, _b, c) = make_one_fixed_point_network();
    // Make a -> c essential
    bn.as_graph_mut().remove_regulation(a, c).unwrap();
    bn.as_graph_mut().add_string_regulation("a -? c").unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    InferenceProblemEncoder::new(problem, &mut solver, true)?;
    assert_eq!(solver.check(), SatResult::Sat);

    Ok(())
}

#[test]
fn essentiality_negative() -> Result<(), anyhow::Error> {
    let (mut bn, a, b, c) = make_one_fixed_point_network();
    // Make a -> c essential
    bn.as_graph_mut().remove_regulation(a, c).unwrap();
    bn.as_graph_mut().add_string_regulation("a -? c").unwrap();
    // But don't use it in the actual update function.
    bn.set_update_function(c, Some(FnUpdate::Var(b))).unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    let result = InferenceProblemEncoder::new(problem, &mut solver, true);
    assert!(result.err().unwrap().to_string().contains("Essentiality"));
    Ok(())
}

#[test]
fn monotonicity_positive() -> Result<(), anyhow::Error> {
    let (mut bn, a, _b, c) = make_one_fixed_point_network();
    // Make a -> c an activation
    bn.as_graph_mut().remove_regulation(a, c).unwrap();
    bn.as_graph_mut().add_string_regulation("a ->? c").unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    InferenceProblemEncoder::new(problem, &mut solver, true)?;
    assert_eq!(solver.check(), SatResult::Sat);

    // Now make the update function negative in `a` and check that the solver is not sat.
    bn.set_update_function(c, Some(FnUpdate::Var(a).negation()))
        .unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    let result = InferenceProblemEncoder::new(problem, &mut solver, true);
    assert!(result.err().unwrap().to_string().contains("Monotonicity"));
    Ok(())
}

#[test]
fn monotonicity_negative() -> Result<(), anyhow::Error> {
    let (mut bn, a, _, c) = make_one_fixed_point_network();
    // Make a -> c an inhibition
    bn.as_graph_mut().remove_regulation(a, c).unwrap();
    bn.as_graph_mut().add_string_regulation("a -|? c").unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    let result = InferenceProblemEncoder::new(problem, &mut solver, true);
    assert!(result.err().unwrap().to_string().contains("Monotonicity"));

    // Now make the update function negative in `a` and check that the solver is sat.
    bn.set_update_function(c, Some(FnUpdate::Var(a).negation()))
        .unwrap();

    let mut solver = build_test_solver();
    let problem = InferenceProblem::from_partially_specified_network(&bn)?;
    InferenceProblemEncoder::new(problem, &mut solver, true)?;
    assert_eq!(solver.check(), SatResult::Sat);

    Ok(())
}
