use biodivine_algo_smt_inference::deprecated::EncodingMode;
use biodivine_algo_smt_inference::deprecated::blocking::BlockingStrategy;
use biodivine_algo_smt_inference::deprecated::observations::{Dataset, Observation};
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation};
use clap::Parser;
use clap::builder::PossibleValuesParser;
use std::collections::BTreeMap;

#[derive(Parser)]
#[clap(about = "SMT benchmarking prototype for BN inference (solution enumeration).")]
struct Arguments {
    /// Path to AEON file with a PSBN model and fixed point annotations.
    model_path: String,

    /// Solver class to use.
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "instantiation"]))]
    solver: String,

    /// Enable verbose output (otherwise, only number of solutions is printed at the end).
    #[clap(short, long)]
    verbose: bool,

    /// Maximum solutions that will be enumerated (note that enumeration is a bottleneck
    /// at the moment).
    #[clap(short, long, default_value_t = 1)]
    limit: usize,
}

#[allow(clippy::iter_over_hash_type)]
fn main() {
    let args = Arguments::parse();

    let solution_limit = args.limit;
    let solver_mode = if args.solver == "quantified" {
        EncodingMode::Quantified
    } else {
        EncodingMode::Instantiation
    };

    let model_string = std::fs::read_to_string(&args.model_path).unwrap();
    let psbn = BooleanNetwork::try_from(model_string.as_str()).unwrap();
    let psbn = psbn.name_implicit_parameters();

    if args.verbose {
        println!("Loading observations and collecting fixed-point specification...");
    }
    let annotations = ModelAnnotation::from_model_string(&model_string);
    let mut observations = BTreeMap::new();
    if let Some(fix_node) = annotations.get_child(&["fix"]) {
        for (fp_id, fp_values) in fix_node.children() {
            let json_str = fp_values.value().expect("Missing annotation value");
            let map: BTreeMap<String, u32> =
                serde_json::from_str(json_str).expect("Failed to parse fixed-point string as JSON");
            let map = map.into_iter().map(|(k, v)| (k, v > 0)).collect();
            observations.insert(fp_id.to_string(), Observation::from_value_map(map));
        }
    }
    let dataset = Dataset::new(observations);
    // Use data as hard constraints
    let inference = dataset.to_inference_problem(&psbn, None).unwrap();

    if args.verbose {
        println!("Building and starting solver...");
    }

    // Iterate over SAT BN interpretations using a simple interpretation blocking strategy.
    // The callback just logs a new solution, the commented out part would also print the
    // BN instance extracted from the z3 model.
    let mut solution_count = 0;
    let _ = inference.get_solutions(
        solver_mode,
        &BlockingStrategy::Interpretation,
        Some(solution_limit),
        |_model| {
            solution_count += 1;
            if args.verbose {
                println!("Found new SAT solution ({solution_count}).");
                // println!("{:?}", model);
            }

            /*
            // Reconstruct the BN instance using the interpretations of the z3 model
            // This works well as long as all update functions are just an uninterpreted
            // function applied to variable's regulators.
            let bn_instance = inference.extract_bn_instance_simplified(model);
            print!("\n{}", bn_instance.to_string());
            println!("===========");
            */
            Ok(())
        },
    );

    if solution_count == 0 {
        if args.verbose {
            println!("No satisfying solution was found.");
        } else {
            println!("0");
        }
    } else if args.verbose {
        println!("Total solutions found: {solution_count} (limit was set to {solution_limit})");
    } else {
        println!("{solution_count}");
    }
}
