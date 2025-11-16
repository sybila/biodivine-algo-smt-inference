use std::collections::BTreeMap;

use crate::Dataset;
use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::symbolic_async_graph::{GraphColors, SymbolicAsyncGraph};
use biodivine_lib_param_bn::{BooleanNetwork, VariableId};
use itertools::Itertools;

pub fn run_naive_inference(
    bn: &BooleanNetwork,
    dataset_spec: &Dataset,
) -> Result<BTreeMap<Vec<(String, String)>, GraphColors>, String> {
    // Build the ASTG
    let stg = SymbolicAsyncGraph::new(bn)?;

    // Build list of indexable specification entries (observation_id, variable_name) pairs
    let mut indices: Vec<(String, String)> = Vec::new();
    for (obs_id, observation) in &dataset_spec.observations {
        for var_name in observation.values.keys() {
            indices.push((obs_id.clone(), var_name.clone()));
        }
    }

    // Compute all fixed points symbolically
    let fixed_points = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());

    // Try progressively removing constraints (making N of the fixed-point
    // values non-determined instead)

    // We collect all optimal specifications and their solution sets
    // (note that some solutions may be present for different specification variants)
    let mut optimal_solutions: BTreeMap<Vec<(String, String)>, GraphColors> = BTreeMap::new();
    for num_to_remove in 0..=indices.len() {
        if !optimal_solutions.is_empty() {
            break; // break once solutions are found in previous iteration
        }

        // Iterate all N-combinations of indices to remove
        for ignore_set in indices.clone().into_iter().combinations(num_to_remove) {
            let loosened_dataset_spec = loosen_specification(dataset_spec, &ignore_set);
            let current_spec = loosened_dataset_spec.to_specification_list(bn)?;

            // Start with all colors, refine with fixed-point constraints
            let mut satisfying_colors = fixed_points.colors();
            for (_, fp_subspec) in current_spec {
                let subspace_values: Vec<(VariableId, bool)> = fp_subspec
                    .make_optional_assertion_map() // assuming all values are optional
                    .into_iter()
                    .map(|(var_id, (value, _weight))| (var_id, value))
                    .collect();
                let spec_vertices = stg.mk_subspace(&subspace_values).vertices();
                let matched_colors = fixed_points.intersect_vertices(&spec_vertices).colors();
                satisfying_colors = satisfying_colors.intersect(&matched_colors);
                if satisfying_colors.is_empty() {
                    break;
                }
            }

            if !satisfying_colors.is_empty() {
                optimal_solutions.insert(ignore_set, satisfying_colors);
            }
        }
    }
    Ok(optimal_solutions)
}

/// Remove specific (observation_id, variable) entries from the full specification.
fn loosen_specification(
    full_specification: &Dataset,
    ignore_indices: &[(String, String)],
) -> Dataset {
    let mut loosened_specification = full_specification.clone();
    for (obs_id, var_name) in ignore_indices {
        if let Some(obs) = loosened_specification.observations.get_mut(obs_id) {
            obs.values.remove(var_name);
        }
    }
    loosened_specification
}
