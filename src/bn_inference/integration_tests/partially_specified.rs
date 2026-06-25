use crate::bn_inference::integration_tests::build_test_optimization_solver;
use biodivine_algo_smt_inference::bn_inference::integration_tests::build_test_solver;
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation, VariableId};
use std::collections::BTreeMap;
use z3::SatResult;

/// Create a simple partially specified network that has variables `a`, `b`, `c`
/// and a single fixed-point (`010` or `011`, depending on chosen function).
///
/// The essentiality and monotonicity constraints should leave only two possible
/// interpretations for the `f` function.
fn make_one_fixed_point_network() -> (BooleanNetwork, VariableId, VariableId, VariableId) {
    let bn = BooleanNetwork::try_from(
        r#"
            a -> c
            b -> c
            $a: false
            $b: true
            $c: f(a, b)
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

#[test]
fn one_fixed_point_both_possible() -> Result<(), anyhow::Error> {
    // Check that both fixed-points of the one-fixed-point network are actually possible.
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

    let fun = encoder.decode_update_function(c, &solver, &model)?;
    let (bdd_ctx, fun_bdd) = fun.as_bdd();
    let expected = bdd_ctx.eval_expression_string("x_0 & x_1");
    assert_eq!(expected, fun_bdd);

    let mut solver = build_test_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 0 :
        #! comparison : equal : `fix/b`: 1 :
        #! comparison : equal : `fix/c`: 1 :
    "#,
    );
    problem.initialize_constraints(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let fix = encoder.decode_state("fix", &model);
    assert_eq!(fix, BTreeMap::from_iter([(a, 0), (b, 1), (c, 1)]));

    let fun = encoder.decode_update_function(c, &solver, &model)?;
    let (bdd_ctx, fun_bdd) = fun.as_bdd();
    let expected = bdd_ctx.eval_expression_string("x_0 | x_1");
    assert_eq!(expected, fun_bdd);

    Ok(())
}

#[test]
fn one_fixed_point_optimize() -> Result<(), anyhow::Error> {
    // Select a specification (110) that has distance 1 to 010 and distance 2 to 011, meaning
    // this should prefer the AND interpretation.

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

    let fun = encoder.decode_update_function(c, &solver, &model)?;
    let (bdd_ctx, fun_bdd) = fun.as_bdd();
    let expected = bdd_ctx.eval_expression_string("x_0 & x_1");
    assert_eq!(expected, fun_bdd);

    // And now do the same thing the other way around. Specification 111 has distance one to 011,
    // but distance 2 to 010, so the OR interpretation should be preferred.

    let mut solver = build_test_optimization_solver();
    let mut problem = InferenceProblem::from_partially_specified_network(&bn)?;

    let properties = ModelAnnotation::from_model_string(
        r#"
        #! state : declare : fix
        #! state : fixed_point : fix :
        #! comparison : equal : `fix/a`: 1 : weight : 0.5
        #! comparison : equal : `fix/b`: 1 : weight : 0.5
        #! comparison : equal : `fix/c`: 1 : weight : 0.5
    "#,
    );
    problem.initialize_constraints_and_weights(&bn, &properties)?;
    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;

    assert_eq!(solver.check(), SatResult::Sat);

    let model = solver.get_model().unwrap();
    let fix = encoder.decode_state("fix", &model);
    assert_eq!(fix, BTreeMap::from_iter([(a, 0), (b, 1), (c, 1)]));

    let fun = encoder.decode_update_function(c, &solver, &model)?;
    let (bdd_ctx, fun_bdd) = fun.as_bdd();
    let expected = bdd_ctx.eval_expression_string("x_0 | x_1");
    assert_eq!(expected, fun_bdd);

    Ok(())
}
