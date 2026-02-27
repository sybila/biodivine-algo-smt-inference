use biodivine_algo_smt_inference::bn_inference::constraints::{
    StateHasExactObservation, StateIsFixedPoint, StateObservation,
};
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_algo_smt_inference::smt_solver::{
    AbstractSolver, BoundedIntSolver, DynMonotoneBoundedIntSolver, InstantiatedMonotoneSolver,
    QuantifiedMonotoneSolver,
};
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
    #[clap(value_parser = PossibleValuesParser::new(["quantified", "quantified-optimized", "quantified-merge", "instantiation", "instantiation-lazy"]))]
    solver: String,

    /// Enable verbose output (otherwise, only "0" or "1" is printed at the end).
    #[clap(short, long)]
    verbose: bool,

    #[clap(short, long, default_value = "false")]
    propagate_observations: bool,

    /// Optional path to save the resulting sat BN instance.
    #[clap(short, long)]
    output_path: Option<String>,
}

fn main() -> Result<(), anyhow::Error> {
    env_logger::init();
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
            observations.insert(fp_id.to_string(), map);
        }
    }

    if args.verbose {
        println!("Building solver using `{}` encoding..", args.solver);
    }

    let mut inference_problem = InferenceProblem::<DynMonotoneBoundedIntSolver>::new();
    let inner_solver = BoundedIntSolver::new_strict(z3::Solver::new());
    let mut solver: DynMonotoneBoundedIntSolver = match args.solver.as_str() {
        "quantified" => Box::new(QuantifiedMonotoneSolver::new(inner_solver, false)),
        "quantified-optimized" => Box::new(QuantifiedMonotoneSolver::new(inner_solver, true)),
        "quantified-merge" => Box::new(QuantifiedMonotoneSolver::new_merge(inner_solver, true)),
        "instantiation" => Box::new(InstantiatedMonotoneSolver::new(inner_solver)),
        "instantiation-lazy" => Box::new(InstantiatedMonotoneSolver::new_lazy(inner_solver)),
        _ => panic!("Unknown solver: {}", args.solver),
    };

    // We have to explicitly initialize the inference problem with influence graph constraints
    // to make sure the variable domains are correctly included.

    // Declare all variables:
    for var in psbn.variables() {
        let name = psbn.get_variable_name(var);
        let max_value = annotations
            .get_value(&["variable", name, "max_value"])
            .map(|it| it.parse::<u32>().unwrap())
            .unwrap_or(1);
        let var_p = inference_problem.declare_variable(name.as_str(), (0, max_value));
        assert_eq!(var_p, var);
    }

    inference_problem.initialize_regulations(psbn.as_graph())?;

    // Declare all fixed-points:
    for (name, observation) in observations {
        assert!(inference_problem.declare_state(name.as_str()));
        let observation = psbn
            .variables()
            .filter_map(|var| {
                observation
                    .get(psbn.get_variable_name(var))
                    .map(|it| (var, *it))
            })
            .collect::<Vec<_>>();
        let observation = StateObservation::from_exact(observation);
        // Here, we ignore observation weights and just assert them all as hard constraints:
        let obs_constraint =
            StateHasExactObservation::new(name.as_str(), observation.all_observations());
        let fix_constraint = StateIsFixedPoint::new(name.as_str());
        inference_problem.assert_constraint(obs_constraint)?;
        inference_problem.assert_constraint(fix_constraint)?;
    }

    println!("Inference problem initialized. Creating constraints.");

    let encoder =
        InferenceProblemEncoder::new(&inference_problem, &mut solver, args.propagate_observations)?;

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
        match encoder.decode_boolean_network(&solver, &model, true) {
            Ok(bn) => {
                std::fs::write(output_path, bn.to_string())?;
            }
            Err(err) => {
                println!("Unable to decode boolean network. {err}",);
            }
        }

        for var in psbn.variables() {
            let function = encoder.decode_update_function(var, &solver, &model)?;
            println!("=== Function table {} ===", psbn.get_variable_name(var));
            println!("{}", function);
        }
    }

    Ok(())
}
