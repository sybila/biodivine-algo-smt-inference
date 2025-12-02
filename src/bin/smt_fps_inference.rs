use biodivine_algo_smt_inference::{Dataset, FixedPointBlocker};
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use clap::Parser;
use std::fs;

// TODO: make this CLI arg
const LIMIT: usize = 1;

/// Structure to collect CLI arguments
#[derive(Parser)]
#[clap(about = "Run SMT-based BN inference using a provided PSBN and fixed-point specification.")]
struct Arguments {
    /// Path to a file with a PSBN model in AEON format.
    psbn_path: String,

    /// Path to a file with fixed-point dataset in CSV format.
    specification_path: String,
}

/// Run SMT inference, iterating over all fixed-point solutions,
/// from optimal to least.
///
/// TODO: for now, we only iterate solutions until `LIMIT` Hamming distance is exceeded
/// TODO: for now, the blocking strategy is set for fixed-point states only
fn run_smt_inference(bn: &BooleanNetwork, dataset_spec: &Dataset) -> Result<(), String> {
    // Build the ASTG and print summary
    let stg = SymbolicAsyncGraph::new(bn)?;
    println!("Total variables: {}", bn.variables().count());
    println!("Total colors: {}", stg.unit_colors().exact_cardinality());
    println!("------");

    println!("Specified fixed-point observations:");
    println!("{}", dataset_spec.to_debug_string());
    println!("------");

    let inference_problem = dataset_spec.to_inference_problem(bn)?;

    // Use the FixedPointBlocker strategy to iterate over solutions
    let blocker_strategy = FixedPointBlocker;
    let mut solution_count = 0;

    // Iterate solutions, processing each via the callback.
    // The callback summarizes the solution model fixed points, and
    // computes Hamming distance to the original specification.
    inference_problem.get_solutions(&blocker_strategy, |model| {
        solution_count += 1;
        println!("\n=== Solution {} ===", solution_count);

        // Go over all the specified fixed points and find their version in the model
        // Compute total missmatches (Hamming dist)
        let mut total_mismatches: usize = 0;
        for (obs_id, obs) in &dataset_spec.observations {
            let fix_state = inference_problem.get_state(obs_id);
            let fix_state_model = fix_state.extract_state(model);
            println!("{obs_id}: {:?}", fix_state_model);

            let var_map = fix_state.make_smt_var_map();
            for (var_name, required_value) in &obs.value_map {
                // Map variable name -> VariableId using the BooleanNetwork (bn)
                let var_id = bn.as_graph().find_variable(var_name).unwrap();

                if let Some(smt_var) = var_map.get(&var_id) {
                    let interp = model.get_const_interp(smt_var).unwrap();
                    let model_val = interp.as_bool().unwrap();
                    if model_val != *required_value {
                        total_mismatches += 1;
                    }
                }
            }
        }
        println!("Summed Hamming distance from specification: {total_mismatches}");

        // Stop iteration if mismatches exceed limit
        if total_mismatches > LIMIT {
            Err("Hamming distance threshold exceeded".to_string())
        } else {
            Ok(())
        }
    })?;

    if solution_count == 0 {
        println!("No matching specification found");
    } else {
        println!("\nTotal solutions found: {}", solution_count);
    }

    Ok(())
}

fn main() {
    // Parse CLI arguments
    let args = Arguments::parse();
    println!("Input PSBN model: `{}`", args.psbn_path);
    println!("Input specification data: `{}`", args.specification_path);

    // Parse the PSBN from the AEON file
    let bn_string = fs::read_to_string(&args.psbn_path).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();

    // Parse the observations (fixed-point specification) from CSV
    let dataset_spec = Dataset::load_from_csv(&args.specification_path).unwrap();

    if let Err(e) = run_smt_inference(&bn, &dataset_spec) {
        println!("Error: {}", e);
    }
}
