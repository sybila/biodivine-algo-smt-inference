use biodivine_algo_smt_inference::bn_inference::InferenceProblem;
use biodivine_algo_smt_inference::bn_inference::constraints::{
    StateHasExactObservation, StateIsFixedPoint, StateObservation,
};
use biodivine_algo_smt_inference::smt_solver::{
    DynMonotoneSolver, InstantiatedMonotoneSolver, QuantifiedMonotoneSolver,
};
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
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "quantified-optimized", "instantiation"]))]
    solver: String,

    /// Enable verbose output (otherwise, only "0" or "1" is printed at the end).
    #[clap(short, long)]
    verbose: bool,

    /// Optional path to save the resulting sat BN instance.
    #[clap(short, long)]
    output_path: Option<String>,
}

fn main() -> Result<(), anyhow::Error> {
    let args = Arguments::parse();

    let model_string = std::fs::read_to_string(&args.model_path)?;
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
        println!("Building solver using `{}` encoding..", args.solver);
    }

    let mut inference_problem =
        InferenceProblem::<DynMonotoneSolver>::from_influence_graph(psbn.as_graph())?;
    let mut solver: DynMonotoneSolver = match args.solver.as_str() {
        "quantified" => Box::new(QuantifiedMonotoneSolver::new(z3::Solver::new(), false)),
        "quantified-optimized" => Box::new(QuantifiedMonotoneSolver::new(z3::Solver::new(), true)),
        "instantiation" => Box::new(InstantiatedMonotoneSolver::new(z3::Solver::new())),
        _ => panic!("Unknown solver: {}", args.solver),
    };

    // Declare all fixed-points:
    for (name, observation) in dataset.observations {
        assert!(inference_problem.declare_state(name.as_str()));
        let observation = observation
            .value_map
            .iter()
            .map(|(k, v)| (inference_problem.find_variable(k).unwrap(), u32::from(*v)))
            .collect::<Vec<_>>();
        let observation = StateObservation::from_exact(observation);
        let obs_constraint = StateHasExactObservation::new(name.as_str(), observation);
        let fix_constraint = StateIsFixedPoint::new(name.as_str());
        inference_problem.assert_constraint(obs_constraint)?;
        inference_problem.assert_constraint(fix_constraint)?;
    }

    inference_problem.build_solver(&mut solver)?;

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

    // If we have a model and an output path was given, save it
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
        std::fs::write(output_path, bn_instance.to_string())?;
    }

    Ok(())
}
