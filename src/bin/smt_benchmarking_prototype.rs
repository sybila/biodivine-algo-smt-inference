use biodivine_algo_smt_inference::EncodingMode;
use biodivine_algo_smt_inference::{Dataset, Observation};
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation};
use clap::Parser;
use clap::builder::PossibleValuesParser;
use std::collections::BTreeMap;
use z3::SatResult;

#[derive(Parser)]
#[clap(about = "SMT benchmarking prototype for BN inference (single solution).")]
struct Arguments {
    /// Path to AEON file with a PSBN model and fixed point annotations.
    model_path: String,

    /// Solver class to use.
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "instantiation"]))]
    solver: String,

    /// Enable verbose output (otherwise, only "0" or "1" is printed at the end).
    #[clap(short, long)]
    verbose: bool,

    /// Optional path to save the resulting sat BN instance.
    #[clap(short, long)]
    output_path: Option<String>,
}

fn main() {
    let args = Arguments::parse();

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
            let value_dict_str = fp_values.value().expect("Missing annotation value");
            // Convert Python literal format to JSON format.
            let json_str = value_dict_str
                .replace('\'', "\"")
                .replace(": True", ": true")
                .replace(": False", ": false");

            let map: BTreeMap<String, bool> = serde_json::from_str(&json_str)
                .expect("Failed to parse fixed-point string as JSON");
            observations.insert(fp_id.to_string(), Observation::from_value_map(map));
        }
    }
    let dataset = Dataset::new(observations);
    // Use data as hard constraints
    let inference = dataset.to_inference_problem(&psbn, None).unwrap();

    if args.verbose {
        println!("Building solver using `{}` encoding..", args.solver);
    }
    let solver = if args.solver == "quantified" {
        inference.build_solver(EncodingMode::Quantified)
    } else {
        inference.build_solver(EncodingMode::Instantiation)
    };

    if args.verbose {
        solver.register_model_handler(Box::new(move |_| {
            println!("Solver made progress!");
        }));
    }

    if args.verbose {
        println!("Checking for solution...");
    }
    let result = solver.check();
    if args.verbose {
        println!("Has solution? {:?}", result);
    } else {
        let res = if result == SatResult::Sat { 1 } else { 0 };
        println!("{}", res);
    }

    // If we have a model and output path was given, save it
    if result == SatResult::Sat
        && let Some(output_path) = args.output_path
    {
        let model = solver.get_model().unwrap();
        println!("{:?}", model);
        if args.verbose {
            println!("Saving BN at: {output_path}");
        }

        // Reconstruct the BN instance using the functions extracted from the z3 model
        // This works well as long as all update functions are just an uninterpreted
        // function applied to variable's regulators.
        let bn_instance = inference.extract_bn_instance_simplified(&model);
        std::fs::write(output_path, bn_instance.to_string()).unwrap();
    }
}
