use biodivine_lib_smt::{Dataset, loosen_specification};

use biodivine_lib_param_bn::biodivine_std::traits::Set;
use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::{BooleanNetwork, VariableId};

use itertools::Itertools;
use std::fs;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Parse CLI arguments
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("Usage: {} <psbn_file> <specification_csv>", args[0]);
        std::process::exit(1);
    }
    let psbn_path = &args[1];
    let csv_path = &args[2];

    // Parse the BN from the AEON file
    let bn_string = fs::read_to_string(psbn_path)?;
    let bn = BooleanNetwork::try_from(bn_string.as_str())?;
    // Parse the observations (fixed-point specification) from CSV
    let dataset_spec = Dataset::load_from_csv(csv_path)?;

    run_inference(&bn, &dataset_spec)?;

    Ok(())
}

fn run_inference(
    bn: &BooleanNetwork,
    dataset_spec: &Dataset,
) -> Result<(), Box<dyn std::error::Error>> {
    // Build the ASTG
    let stg = SymbolicAsyncGraph::new(bn)?;
    println!("Total variables: {}", bn.variables().count());
    println!("Total colors: {}", stg.unit_colors().exact_cardinality());
    println!("------");

    println!("Specified fixed-point observations:");
    println!("{}", dataset_spec.to_debug_string());
    println!("------");

    // Build list of indexable specification entries (observation_id, variable_name) pairs
    let mut indices: Vec<(String, String)> = Vec::new();
    for (obs_id, observation) in &dataset_spec.observations {
        for var_name in observation.value_map.keys() {
            indices.push((obs_id.clone(), var_name.clone()));
        }
    }

    // Compute all fixed points symbolically
    let fixed_points = FixedPoints::symbolic(&stg, stg.unit_colored_vertices());
    println!(
        "Total colored fixed points: {}",
        fixed_points.exact_cardinality()
    );
    println!(
        "Unique fixed point states: {}",
        fixed_points.vertices().exact_cardinality()
    );
    println!(
        "Unique fixed point colors: {}",
        fixed_points.colors().exact_cardinality()
    );
    println!("------");

    // Try progressively removing constraints (making N of the fixed-point
    // values non-determined instead)
    // We stop this "constraint loosening" once closest specification is found
    let mut found_solution = false;
    for num_to_remove in 0..=indices.len() {
        if found_solution {
            break;
        }

        println!("\nTrying with {} values removed:", num_to_remove);
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

            // If some colors satisfy this specification, inform the user
            if !satisfying_colors.is_empty() {
                found_solution = true;
                println!("\tFound matching specification!");
                println!("\t-> Removed values: {:?}", ignore_set);
                println!(
                    "\t-> Matching specification: {}",
                    loosened_dataset_spec.to_debug_string()
                );
                println!(
                    "\t-> {} colors satisfy this specification",
                    satisfying_colors.exact_cardinality()
                );
                println!()
                // TODO: sat color iterator
            }
        }
    }

    if !found_solution {
        println!("No matching specification found");
    }

    Ok(())
}
