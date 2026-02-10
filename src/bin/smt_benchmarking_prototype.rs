use biodivine_algo_smt_inference::EncodingMode;
use biodivine_algo_smt_inference::{Dataset, Observation};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ModelAnnotation};
use clap::Parser;
use clap::builder::PossibleValuesParser;
use std::collections::BTreeMap;
use z3::SatResult;

#[derive(Parser)]
#[clap(about = "SMT benchmarking prototype for BN inference.")]
struct Arguments {
    /// Path to AEON file with a PSBN model and fixed point annotations.
    model_path: String,
    /// Solver class to use.
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "instantiation"]))]
    solver: String,
    /// Enable verbose output.
    #[clap(short, long)]
    verbose: bool,
    /// Path to save the resulting BN model.
    #[clap(short, long)]
    output_path: Option<String>,
}

fn main() {
    let args = Arguments::parse();

    let model_string = std::fs::read_to_string(&args.model_path).unwrap();
    let model = BooleanNetwork::try_from(model_string.as_str()).unwrap();
    let model = model.name_implicit_parameters();

    // Load observation data and create constraints
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
    let inference = dataset.to_inference_problem(&model, None).unwrap();

    if args.verbose {
        println!("Building solver...");
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

    if result == SatResult::Sat {
        if let Some(output_path) = args.output_path {
            let model = solver.get_model().unwrap();
            let psbn = inference.get_network();
            let mut bn_instance = psbn.clone();
            for variable in psbn.variables() {
                let update_fn = psbn.get_update_function(variable).clone().unwrap();
                if let FnUpdate::Param(param_id, args) = update_fn {
                    let (bdd_ctx, fn_bdd) = inference.extract_uninterpreted_symbol(&model, param_id);
                    let mut bdd_string = fn_bdd.to_boolean_expression(&bdd_ctx).to_string();
                    println!("{}: {bdd_string}", psbn.get_variable_name(variable));
                    let mut renaming = BTreeMap::new();
                    for (i, arg) in args.iter().enumerate() {
                        assert!(matches!(arg, FnUpdate::Var(_)));
                        renaming.insert(format!("x_{}", i), format!("({})", arg.to_string(psbn)));
                    }

                    let mut keys: Vec<_> = renaming.keys().cloned().collect();
                    keys.sort_by_key(|k| std::cmp::Reverse(k.len()));
                    for key in keys {
                        bdd_string = bdd_string.replace(&key, &renaming[&key]);
                    }

                    let update = FnUpdate::try_from_str(&bdd_string, &bn_instance).unwrap();
                    bn_instance.set_update_function(variable, Some(update)).unwrap();
                } else {
                    panic!("Unexpected update fn format.");
                }
            }
            std::fs::write(output_path, bn_instance.to_string()).unwrap();
        }
    }
}
