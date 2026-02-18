use biodivine_algo_smt_inference::{Dataset, Observation};
use biodivine_algo_smt_inference::{
    EncodingMode, InstantiationMonotoneSMTSolver, LazyInstantiationMonotoneSMTSolver,
    substitute_fn_args,
};
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ModelAnnotation};
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
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "instantiation", "lazy"]))]
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
    let solver_mode: EncodingMode = if args.solver == "quantified" {
        EncodingMode::Quantified
    } else if args.solver == "instantiation" {
        EncodingMode::Instantiation
    } else {
        EncodingMode::LazyInstantiation
    };

    let mut solver = inference.build_solver(solver_mode);
    if args.verbose {
        solver.set_verbose();
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
        // println!("{:?}", model);

        // Reconstruct the BN instance using the functions extracted from the z3 model
        // and output the extracted BN
        // For the two instantiation-based solvers, we must repair monotonicity in the model
        // TODO: do this via trait or something
        let bn_instance = if args.solver == "instantiation"
            && let Some(inst_solver) = solver
                .as_any()
                .downcast_ref::<InstantiationMonotoneSMTSolver>()
        {
            if args.verbose {
                println!("Repairing monotonicity...");
            }

            let monotone_fn_map = inst_solver.repair_monotonicity(&model);

            let psbn = inference.get_network();
            let mut bn_instance = psbn.clone();
            for variable in psbn.variables() {
                let var_name = psbn.get_variable_name(variable);
                let update_fn = psbn.get_update_function(variable).clone().unwrap();
                if let FnUpdate::Param(_, fn_args) = update_fn {
                    let uninterpreted_fn_id = format!("f_{var_name}"); // id in SMT encoding
                    let fn_dnf_str = monotone_fn_map.get(&uninterpreted_fn_id).unwrap();

                    // We need to substitute variable names in the fn expression string (x_0, x_1,..)
                    // with the actual function arguments
                    let update = substitute_fn_args(fn_dnf_str, fn_args, psbn);
                    bn_instance
                        .set_update_function(variable, Some(update))
                        .unwrap();
                } else {
                    panic!("Unexpected update fn format.");
                }
            }
            bn_instance
        } else if args.solver == "lazy"
            && let Some(lazy_solver) = solver
                .as_any()
                .downcast_ref::<LazyInstantiationMonotoneSMTSolver>()
        {
            if args.verbose {
                println!("Repairing monotonicity...");
            }

            let monotone_fn_map = lazy_solver.repair_monotonicity(&model);

            let psbn = inference.get_network();
            let mut bn_instance = psbn.clone();
            for variable in psbn.variables() {
                let var_name = psbn.get_variable_name(variable);
                let update_fn = psbn.get_update_function(variable).clone().unwrap();
                if let FnUpdate::Param(_, fn_args) = update_fn {
                    let uninterpreted_fn_id = format!("f_{var_name}"); // id in SMT encoding
                    let fn_dnf_str = monotone_fn_map.get(&uninterpreted_fn_id).unwrap();

                    // We need to substitute variable names in the fn expression string (x_0, x_1,..)
                    // with the actual function arguments
                    let update = substitute_fn_args(fn_dnf_str, fn_args, psbn);
                    bn_instance
                        .set_update_function(variable, Some(update))
                        .unwrap();
                } else {
                    panic!("Unexpected update fn format.");
                }
            }
            bn_instance
        } else {
            inference.extract_bn_instance_simplified(&model)
        };
        if args.verbose {
            println!("Saving BN at: {output_path}");
        }
        std::fs::write(&output_path, bn_instance.to_string()).unwrap();
    }
}
