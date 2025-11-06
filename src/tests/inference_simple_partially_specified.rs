use crate::{InferenceProblem, StateSpecification};
use biodivine_lib_param_bn::{BooleanNetwork, ParameterId, VariableId};
use num_rational::BigRational;
use num_traits::FromPrimitive;
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
fn one_fixed_point_both_possible() {
    // Check that both fixed-points of the one-fixed-point network are actually possible.
    let (bn, a, b, c) = make_one_fixed_point_network();
    let f = ParameterId::from_index(0);

    let mut specification = StateSpecification::default();
    specification.assert_must(a, false);
    specification.assert_must(b, true);
    specification.assert_must(c, false);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![false, true, false]);
    assert_eq!(
        problem.extract_uninterpreted_symbol(&model, f),
        "[else -> (and (:var 0) (:var 1))]"
    );

    let mut specification = StateSpecification::default();
    specification.assert_must(a, false);
    specification.assert_must(b, true);
    specification.assert_must(c, true);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![false, true, true]);
    assert_eq!(
        problem.extract_uninterpreted_symbol(&model, f),
        "[else -> (not (and (not (:var 0)) (not (:var 1))))]"
    );
}

#[test]
fn one_fixed_point_optimize() {
    // Select a specification (110) that has distance 1 to 010 and distance 2 to 011, meaning
    // this should prefer the AND interpretation.

    let (bn, a, b, c) = make_one_fixed_point_network();
    let f = ParameterId::from_index(0);

    let one_half = BigRational::from_f32(0.5).unwrap();
    let mut specification = StateSpecification::default();
    specification.assert_may(a, true, &one_half);
    specification.assert_may(b, true, &one_half);
    specification.assert_may(c, false, &one_half);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![false, true, false]);
    assert_eq!(
        problem.extract_uninterpreted_symbol(&model, f),
        "[else -> (and (:var 0) (:var 1))]"
    );

    // And now do the same thing the other way around. Specification 111 has distance one to 011,
    // but distance 2 to 010, so the OR interpretation should be preferred.

    let one_half = BigRational::from_f32(0.5).unwrap();
    let mut specification = StateSpecification::default();
    specification.assert_may(a, true, &one_half);
    specification.assert_may(b, true, &one_half);
    specification.assert_may(c, true, &one_half);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![false, true, true]);
    assert_eq!(
        problem.extract_uninterpreted_symbol(&model, f),
        "[else -> (not (and (not (:var 0)) (not (:var 1))))]"
    );
}
