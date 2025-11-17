use crate::Dataset;
use biodivine_lib_param_bn::{BooleanNetwork, ParameterId};
use std::fs;
use z3::SatResult;

const TOY_BN_4V_PATH: &str = "data/toy_models/4v-activ-fully-spec.aeon";
const TOY_PSBN_4V_PATH: &str = "data/toy_models/4v-activ-psbn.aeon";
const TOY_SPEC_4V_PATH: &str = "data/toy_models/4v-activ-specification.csv";

const MYELOID_BN_PATH: &str = "data/myeloid/myeloid-fully-specified.aeon";
const MYELOID_DATA_SAT_PATH: &str = "data/myeloid/dataset-fps-adjusted-SAT.csv";
const MYELOID_DATA_UNSAT_PATH: &str = "data/myeloid/dataset-fps-original-UNSAT.csv";

#[test]
/// Run the test on a fully specified 4-variable model with activations only.
/// The model has three fixed points '0000', '0100', '1111'.
/// The specification requires two fixed points '0110' (fp_1) and '0001' (fp_2)
/// with confidence weight 0.5 on each bit value.
fn test_toy_bn_4v_bn() {
    let bn_string = fs::read_to_string(TOY_BN_4V_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let dataset_spec = Dataset::load_from_csv(TOY_SPEC_4V_PATH).unwrap();

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
    let dataset_spec = Dataset::load_from_csv(TOY_SPEC_4V_PATH).unwrap();

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

#[test]
/// Run the inference on a fully specified Myeloid model.
/// For this test, we use a specification that requires four different fixed points which
/// are all directly satisfied.
fn test_myeloid_bn_sat() {
    let bn_string = fs::read_to_string(MYELOID_BN_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let dataset_spec = Dataset::load_from_csv(MYELOID_DATA_SAT_PATH).unwrap();

    let inference_problem = dataset_spec.to_inference_problem(&bn).unwrap();

    // Result should be SAT, the model completely satisfying the specification
    let solver = inference_problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);

    let model = solver.get_model().unwrap();
    for (obs_id, obs) in dataset_spec.observations {
        let fix_state = inference_problem.get_state(&obs_id);
        // All required fixpoint states match the original specification directly
        assert_eq!(
            fix_state.extract_state(&model),
            obs.value_map.values().cloned().collect::<Vec<bool>>()
        );
    }
}

#[test]
/// Run the inference on a fully specified Myeloid model.
/// For this test, we use a specification that requires four different fixed points,
/// and one of the values needs to be flipped for it to be satisfied.
fn test_myeloid_bn_unsat() {
    let bn_string = fs::read_to_string(MYELOID_BN_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let dataset_spec = Dataset::load_from_csv(MYELOID_DATA_UNSAT_PATH).unwrap();

    let inference_problem = dataset_spec.to_inference_problem(&bn).unwrap();

    // Result should be SAT, the model differing in one bit from the specification
    // The different bit is GATA2 value (first value) in Megakaryocyte observation
    let solver = inference_problem.build_solver();
    assert_eq!(solver.check(&[]), SatResult::Sat);

    // Find index of GATA2 (variables in SMT state are alphabetical)
    let mut variables = dataset_spec.variables.clone();
    variables.sort();
    let gata_idx = variables.iter().position(|v| v == "GATA2").unwrap();

    let model = solver.get_model().unwrap();
    for (obs_id, obs) in dataset_spec.observations {
        let fix_state = inference_problem.get_state(&obs_id);
        let mut fix_orig_spec = obs.value_map.values().cloned().collect::<Vec<bool>>();
        if obs_id.as_str() == "Megakaryocyte" {
            // Megakaryocyte fixpoint in the model does not match the original specification
            assert_ne!(fix_state.extract_state(&model), fix_orig_spec);
            // But if we swap the GATA2 to false, it matches
            fix_orig_spec[gata_idx] = false;
            assert_eq!(fix_state.extract_state(&model), fix_orig_spec);
        } else {
            // All other required fixpoint states match the original specification directly
            assert_eq!(fix_state.extract_state(&model), fix_orig_spec);
        }
    }
}
