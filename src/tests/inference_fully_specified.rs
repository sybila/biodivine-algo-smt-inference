use crate::InferenceProblem;
use crate::state_specification::StateSpecification;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, VariableId};
use num_rational::BigRational;
use num_traits::FromPrimitive;
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
fn one_fixed_point_must_positive() {
    let (bn, a, b, c) = make_one_fixed_point_network();

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
}

/// Test that we can detect that a fixed-point does not exist.
#[test]
fn one_fixed_point_must_negative() {
    let (bn, a, b, c) = make_one_fixed_point_network();

    let mut specification = StateSpecification::default();
    specification.assert_must(a, true);
    specification.assert_must(b, true);
    specification.assert_must(c, false);

    let mut problem = InferenceProblem::new(bn.clone());
    let _fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Unsat);
}

/// Test that we can detect a fixed-point (010) within distance one of specification (110).
#[test]
fn one_fixed_point_may() {
    let (bn, a, b, c) = make_one_fixed_point_network();

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
    // Note that a=0, even though specification requires a=1.
    assert_eq!(fix.extract_state(&model), vec![false, true, false]);
}

/// Test that we can find two distinct fixed-points.
#[test]
fn two_fixed_point_must_positive() {
    let (bn, a, b, c) = make_two_fixed_points_network();

    let mut spec_one = StateSpecification::default();
    spec_one.assert_must(a, false);
    spec_one.assert_must(b, true);
    spec_one.assert_must(c, false);

    let mut spec_two = StateSpecification::default();
    spec_two.assert_must(a, true);
    spec_two.assert_must(b, true);
    spec_two.assert_must(c, true);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix_one = problem.make_state("fix-1");
    let fix_two = problem.make_state("fix-2");
    problem.assert_fixed_point("fix-1");
    problem.assert_fixed_point("fix-2");
    problem.assert_state_observation("fix-1", &spec_one);
    problem.assert_state_observation("fix-2", &spec_two);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix_one.extract_state(&model), vec![false, true, false]);
    assert_eq!(fix_two.extract_state(&model), vec![true, true, true]);
}

// Test that we can detect two fixed points (010 and 111) within distance one and two
// of a specification (000 and 101).
#[test]
fn two_fixed_point_may() {
    let (bn, a, b, c) = make_two_fixed_points_network();

    let one_half = BigRational::from_f32(0.5).unwrap();
    let mut spec_one = StateSpecification::default();
    spec_one.assert_may(a, false, &one_half);
    spec_one.assert_may(b, false, &one_half);
    spec_one.assert_may(c, false, &one_half);

    let mut spec_two = StateSpecification::default();
    spec_two.assert_may(a, true, &one_half);
    spec_two.assert_may(b, false, &one_half);
    spec_two.assert_may(c, true, &one_half);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix_one = problem.make_state("fix-1");
    let fix_two = problem.make_state("fix-2");
    problem.assert_fixed_point("fix-1");
    problem.assert_fixed_point("fix-2");
    problem.assert_state_observation("fix-1", &spec_one);
    problem.assert_state_observation("fix-2", &spec_two);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix_one.extract_state(&model), vec![false, true, false]);
    assert_eq!(fix_two.extract_state(&model), vec![true, true, true]);
}

/// Test that we can detect one fixed-point out of two (010 and 111) within distance
/// two of specification (001) where the final fixed-point is determined by
/// specification weights.
#[test]
fn one_in_two_fixed_point_optimize() {
    let (bn, a, b, c) = make_two_fixed_points_network();

    // 0.25 + 0.25 < 0.66 + 0.25
    let two_over_three = BigRational::from_f32(0.66).unwrap();
    let one_over_four = BigRational::from_f32(0.25).unwrap();

    // First, build the specification such that `010` is the optimal fixed-point.
    let mut specification = StateSpecification::default();
    specification.assert_may(a, false, &two_over_three);
    specification.assert_may(b, false, &one_over_four);
    specification.assert_may(c, true, &one_over_four);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![false, true, false]);

    // Second, rebuild the specification to prefer `111`.
    let mut specification = StateSpecification::default();
    specification.assert_may(a, false, &one_over_four);
    specification.assert_may(b, false, &one_over_four);
    specification.assert_may(c, true, &two_over_three);

    let mut problem = InferenceProblem::new(bn.clone());
    let fix = problem.make_state("fix");
    problem.assert_fixed_point("fix");
    problem.assert_state_observation("fix", &specification);

    let solver = problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);
    let model = solver.get_model().unwrap();
    assert_eq!(fix.extract_state(&model), vec![true, true, true]);
}
