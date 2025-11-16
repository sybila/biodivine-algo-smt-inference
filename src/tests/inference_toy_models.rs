use crate::Dataset;
use biodivine_lib_param_bn::{BooleanNetwork, ParameterId};
use std::fs;
use z3::SatResult;

const TOY_BN_4V_PATH: &str = "data/toy_models/4v-activ-fully-spec.aeon";
const TOY_PSBN_4V_PATH: &str = "data/toy_models/4v-activ-psbn.aeon";
const TOY_SPEC_4V_PATH: &str = "data/toy_models/4v-activ-specification.csv";

#[test]
/// Run the test on a fully specified 4-variable model with activations only.
/// The model has three fixed points '0000', '0100', '1111'.
/// The specification requires two fixed points '0110' (fp_1) and '0001' (fp_2)
/// with confidence weight 0.5 on each bit value.
fn test_toy_bn_4v_bn() {
    let bn_string = fs::read_to_string(TOY_BN_4V_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let dataset_spec = Dataset::load_dataset(TOY_SPEC_4V_PATH).unwrap();

    let inference_problem = dataset_spec.to_inference_problem(&bn).unwrap();
    let fix_one = inference_problem.get_state("fp_1");
    let fix_two = inference_problem.get_state("fp_2");

    // Result should be SAT, with both fixed points different in single bit
    // from the specification
    let solver = inference_problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        fix_one.extract_state(&model),
        vec![false, true, false, false]
    );
    assert_eq!(
        fix_two.extract_state(&model),
        vec![false, false, false, false]
    );
}

#[test]
/// Run the test on a 4-variable PSBN with activations only.
/// The specification requires two fixed points '0110' (fp_1) and '0001' (fp_2)
/// with confidence weight 0.5 on each bit value.
/// There should be two colors (with same fixed points) that can fit the closest
/// specification at Hamming distance 2.
fn test_toy_psbn_4v_bn() {
    let bn_string = fs::read_to_string(TOY_PSBN_4V_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let f = ParameterId::from_index(0);
    let dataset_spec = Dataset::load_dataset(TOY_SPEC_4V_PATH).unwrap();

    let inference_problem = dataset_spec.to_inference_problem(&bn).unwrap();
    let fix_one = inference_problem.get_state("fp_1");
    let fix_two = inference_problem.get_state("fp_2");

    // Result should be SAT, with both fixed points different in single bit
    // from the specification
    let solver = inference_problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);

    let model = solver.get_model().unwrap();
    assert_eq!(
        fix_one.extract_state(&model),
        vec![false, true, false, false]
    );
    assert_eq!(
        fix_two.extract_state(&model),
        vec![false, false, false, false]
    );
    let (bdd_ctx, bdd_fn) = inference_problem.extract_uninterpreted_symbol(&model, f);
    let expected = bdd_ctx.eval_expression_string("x_1");
    assert_eq!(bdd_fn, expected);

    // TODO: check for the second sat model
}
