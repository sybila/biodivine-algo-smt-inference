use crate::bn_inference::InferenceProblemIterator;
use crate::bn_inference::constraints::StateIsFixedPoint;
use biodivine_algo_smt_inference::bn_inference::constraints::{
    CmpOp, ComparedValue, ValueComparison,
};
use biodivine_algo_smt_inference::bn_inference::integration_tests::build_test_solver;
use biodivine_algo_smt_inference::bn_inference::{
    BlockingAtom, InferenceProblem, InferenceProblemEncoder,
};
use biodivine_lib_param_bn::BooleanNetwork;
use std::collections::{BTreeMap, HashSet};

#[test]
fn iterate_all_naive_fixed_points() -> Result<(), anyhow::Error> {
    // Take a complete network with two variables and show that it can have exactly 4 distinct
    // fixed points.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -?? a
        a -?? b
        b -?? b
        b -?? a
    "#,
    )
    .unwrap();

    let mut solver = build_test_solver();

    let mut problem = InferenceProblem::from_partially_specified_network(&psbn)?;
    problem.declare_state("fix");
    problem.assert_constraint(StateIsFixedPoint::new("fix"))?;

    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;
    let iterator = InferenceProblemIterator::new(&encoder, solver, &[BlockingAtom::AllStates])?;

    let mut states = HashSet::new();
    for model in iterator {
        states.insert(encoder.decode_state("fix", &model));
    }

    assert_eq!(states.len(), 4);
    Ok(())
}

#[test]
fn iterate_unconstrainted_function() -> Result<(), anyhow::Error> {
    // Take a function without any restrictions and show that it generates a single partial
    // specification (in it, no points are restricted, meaning our algorithm should pick false
    // as a representative function from this class).

    let psbn = BooleanNetwork::try_from(
        r#"
        a -?? a
        a -?? b
        b -?? b
        b -?? a
    "#,
    )
    .unwrap();

    let a = psbn.as_graph().find_variable("a").unwrap();

    let mut solver = build_test_solver();

    let problem = InferenceProblem::from_partially_specified_network(&psbn)?;

    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;
    let mut iterator = InferenceProblemIterator::new(
        &encoder,
        solver,
        &[BlockingAtom::FunctionPoints("a".to_string())],
    )?;

    let mut functions = HashSet::new();
    while let Some(model) = iterator.next() {
        functions.insert(encoder.decode_update_function(a, iterator.solver(), &model)?);
    }

    assert_eq!(functions.len(), 1);
    let function = functions.into_iter().next().unwrap();
    assert!(function.terms.is_empty());
    Ok(())
}

#[test]
fn iterate_monotone_function_and_inputs() -> Result<(), anyhow::Error> {
    // Take an unrestricted but monotone function with constant inputs. Show that for different
    // input combinations, we get different functions and different fixed points. Specifically,
    // we should get three fixed-points with OR functions, and one fixed-point with AND function.

    let psbn = BooleanNetwork::try_from(
        r#"
        a -> out
        b -> out
    "#,
    )
    .unwrap();

    let a = psbn.as_graph().find_variable("a").unwrap();
    let b = psbn.as_graph().find_variable("b").unwrap();
    let out = psbn.as_graph().find_variable("out").unwrap();

    let mut solver = build_test_solver();

    let mut problem = InferenceProblem::from_partially_specified_network(&psbn)?;

    // Assert that there is a fixed-point with `out=1`.
    assert!(problem.declare_state("fix"));
    problem.assert_constraint(StateIsFixedPoint::new("fix"))?;
    problem.assert_constraint(ValueComparison::variable_assignment("fix", out, 1))?;

    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;
    let mut iterator = InferenceProblemIterator::new(
        &encoder,
        solver,
        &[
            BlockingAtom::FunctionPoints("out".to_string()),
            BlockingAtom::VariableInState("fix".to_string(), "a".to_string()),
            BlockingAtom::VariableInState("fix".to_string(), "b".to_string()),
        ],
    )?;

    let mut results = Vec::new();
    while let Some(model) = iterator.next() {
        let fix = encoder.decode_state("fix", &model);
        results.push(fix);
    }

    assert_eq!(results.len(), 4);

    // Two fixed points with (1,1) inputs --- `AND` and `OR`:
    assert_eq!(
        results
            .iter()
            .filter(|fix| fix.get(&a) == Some(&1) && fix.get(&b) == Some(&1))
            .count(),
        2
    );

    // One fixed point for the other combinations:
    assert!(results.contains(&BTreeMap::from_iter([(a, 0), (b, 1), (out, 1)])));
    assert!(results.contains(&BTreeMap::from_iter([(a, 1), (b, 0), (out, 1)])));

    Ok(())
}

#[test]
fn iterate_partially_specified_function() -> Result<(), anyhow::Error> {
    // This reports only one solution, because all the other solutions are in the same
    // "partial specification class". Due to our function "completion" algorithm, the
    // reported function will always be "&".

    let psbn = BooleanNetwork::try_from(
        r#"
        a -?? out
        b -?? out
    "#,
    )
    .unwrap();

    let a = psbn.as_graph().find_variable("a").unwrap();
    let b = psbn.as_graph().find_variable("b").unwrap();
    let out = psbn.as_graph().find_variable("out").unwrap();

    let mut solver = build_test_solver();

    let mut problem = InferenceProblem::from_partially_specified_network(&psbn)?;

    // Assert that f_out(1,1) = 1
    assert!(problem.declare_state("s"));
    problem.assert_constraint(ValueComparison::variable_assignment("s", a, 1))?;
    problem.assert_constraint(ValueComparison::variable_assignment("s", b, 1))?;
    problem.assert_constraint(ValueComparison::variable_assignment("s", out, 1))?;
    problem.assert_constraint(ValueComparison::new(
        ComparedValue::UpdateFunctionOutputInState("s".to_string(), out),
        CmpOp::Equal,
        ComparedValue::Constant(1),
    ))?;

    let encoder = InferenceProblemEncoder::new(problem, &mut solver, true)?;
    let mut iterator = InferenceProblemIterator::new(
        &encoder,
        solver,
        &[BlockingAtom::FunctionPoints("out".to_string())],
    )?;

    let mut functions = Vec::new();
    while let Some(model) = iterator.next() {
        functions.push(encoder.decode_update_function(out, iterator.solver(), &model)?);
    }

    assert_eq!(functions.len(), 1);
    let function = functions.into_iter().next().unwrap();
    let (bdd_ctx, fun_bdd) = function.as_bdd();
    assert_eq!(bdd_ctx.eval_expression_string("x_0 & x_1"), fun_bdd);

    Ok(())
}
