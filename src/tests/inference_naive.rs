use crate::Dataset;
use crate::run_naive_inference;

use biodivine_lib_param_bn::BooleanNetwork;
use std::fs;

const TOY_MODEL_4V_PATH: &str = "data/toy_models/4v-activ-fully-spec.aeon";
const TOY_SPEC_4V_PATH: &str = "data/toy_models/4v-activ-specification.csv";

#[test]
/// Run the test on a fully specified 4-variable model with activations only.
/// The model has three fixed points '0000', '0100', '1111'.
/// The specification requires two fixed points '0110' (fp_1) and '0001' (fp_2)
/// with confidence weight 0.5 on each bit value.
fn test_toy_model_4v_bn() {
    let bn_string = fs::read_to_string(TOY_MODEL_4V_PATH).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let dataset_spec = Dataset::load_dataset(TOY_SPEC_4V_PATH).unwrap();

    // There is a single optimal specification with 01*0 and 000*
    let mut optimal_solutions = run_naive_inference(&bn, &dataset_spec).unwrap();
    let expected_removed_constraints = vec![
        ("fp_1".to_string(), "v_3".to_string()),
        ("fp_2".to_string(), "v_4".to_string()),
    ];
    let maybe_solution_set = optimal_solutions.remove(&expected_removed_constraints);
    // There is only one solution model satisfying this specification
    assert!(maybe_solution_set.is_some());
    if let Some(solution_set) = maybe_solution_set {
        assert!(solution_set.is_singleton());
    }
    // There are no other optimal specifications
    assert!(optimal_solutions.is_empty())
}
