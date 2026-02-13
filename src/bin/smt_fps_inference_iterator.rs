use biodivine_algo_smt_inference::{BlockingStrategy, Dataset, EncodingMode};
use biodivine_lib_param_bn::BooleanNetwork;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use clap::Parser;
use clap::builder::PossibleValuesParser;
use std::fs;

/// Structure to collect CLI arguments
#[derive(Parser)]
#[clap(
    about = "Run SMT-based BN inference using a provided PSBN and ideal fixed-point \
    specification. Enumerate N optimal solutions using a selected blocking strategy."
)]
struct Arguments {
    /// Path to a file with a PSBN model in AEON format.
    psbn_path: String,

    /// Path to a file with fixed-point dataset specification in CSV format.
    specification_path: String,

    /// Blocking strategy to use for enumeration.
    #[clap(value_parser = PossibleValuesParser::new(["fixed_points", "interpretation", "combined"]))]
    blocking_strategy: String,

    /// Maximum solutions that will be enumerated.
    #[clap(long = "limit", default_value_t = 1)]
    limit: usize,
}

/// Run SMT inference, iterating over top `limit` solutions based selected blocking
/// strategy, from optimal to least.
fn run_smt_inference(
    bn: &BooleanNetwork,
    dataset_spec: &Dataset,
    blocking_str: &str,
    limit: usize,
) -> Result<(), String> {
    // Build the ASTG and print summary
    let stg = SymbolicAsyncGraph::new(bn)?;
    println!("Total variables: {}", bn.variables().count());
    println!("Total colors: {}", stg.unit_colors().exact_cardinality());
    println!("------");

    println!("Specified fixed-point observations:");
    println!("{}", dataset_spec.to_debug_string());
    println!("------");

    // TODO: add CLI option to choose whether use hard X soft constraints on fixed points
    //let inference_problem = dataset_spec.to_inference_problem(bn, None)?;
    let dummy_weight = 0.5;
    let inference_problem = dataset_spec.to_inference_problem(bn, Some(dummy_weight))?;

    // Use the FixedPointBlocker strategy to iterate over solutions
    let blocker_strategy = make_blocker(blocking_str)?;
    let mut solution_count = 0;

    // Iterate solutions, processing each via the callback.
    // The callback summarizes the solution model fixed points and
    // function interpretations
    inference_problem.get_solutions(
        EncodingMode::Instantiation,
        &blocker_strategy,
        Some(limit),
        |model| {
            solution_count += 1;

            // Go over all the fixed points and function symbols in the model
            let mut fix_state_models_str = Vec::new();
            for obs_id in dataset_spec.observations.keys() {
                let fix_state = inference_problem.get_state(obs_id);
                let fix_state_model = fix_state.extract_state(model);
                fix_state_models_str.push(format!("{obs_id}: {:?}", fix_state_model));
            }

            let mut fn_interpretations_str = Vec::new();
            for param_id in bn.parameters() {
                let param_name = bn.get_parameter(param_id).get_name();
                let (bdd_ctx, fn_bdd) =
                    inference_problem.extract_uninterpreted_symbol(model, param_id);
                let bdd_expression = fn_bdd.to_boolean_expression(&bdd_ctx);
                fn_interpretations_str.push(format!(
                    "{}: {:?}",
                    param_name,
                    bdd_expression.to_string()
                ));
            }

            println!("\n=== Solution {} ===", solution_count);
            for fix_state_model_print in fix_state_models_str {
                println!("{fix_state_model_print}");
            }
            for fn_model_print in fn_interpretations_str {
                println!("{fn_model_print}");
            }
            println!("======");
            Ok(())
        },
    )?;

    if solution_count == 0 {
        println!("No matching specification found");
    } else {
        println!("\nTotal solutions found: {solution_count} (selected max limit: {limit})");
    }

    Ok(())
}

fn make_blocker(blocking_str: &str) -> Result<BlockingStrategy, String> {
    match blocking_str {
        "fixed_points" => Ok(BlockingStrategy::FixedPoints),
        "interpretation" => Ok(BlockingStrategy::Interpretation),
        "combined" => Ok(BlockingStrategy::Combined),
        _ => Err(format!("Unsupported blocking strategy: {blocking_str}")),
    }
}

fn main() {
    // Parse CLI arguments
    let args = Arguments::parse();
    println!("Input PSBN model: `{}`", args.psbn_path);
    println!("Input specification data: `{}`", args.specification_path);
    println!("Selected blocking strategy: {}", args.blocking_strategy);
    println!("Max number of solutions to enumerate: {}", args.limit);

    // Parse the PSBN from the AEON file
    let bn_string = fs::read_to_string(&args.psbn_path).unwrap();
    let bn = BooleanNetwork::try_from(bn_string.as_str()).unwrap();
    let bn = bn.name_implicit_parameters();

    // Parse the observations (fixed-point specification) from CSV
    // TODO: currently only uniform 0.5 weights are supported
    let dataset_spec = Dataset::load_from_csv_uniform_weights(&args.specification_path).unwrap();

    if let Err(e) = run_smt_inference(&bn, &dataset_spec, &args.blocking_strategy, args.limit) {
        println!("\n{e}");
    }
}
