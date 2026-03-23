use biodivine_algo_smt_inference::bn_inference::BlockingStrategy;
use biodivine_algo_smt_inference::bn_inference::{
    InferenceProblem, InferenceProblemEncoder, InferenceSolverIterator,
};
use biodivine_algo_smt_inference::smt_solver::{
    BoundedIntSolver, DynMonotoneBoundedIntOptimizeSolver, InstantiatedMonotoneSolver,
    QuantifiedMonotoneSolver,
};
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation};
use clap::Parser;
use clap::builder::PossibleValuesParser;
use log::info;
use std::rc::Rc;

#[derive(Parser)]
#[clap(about = "SMT benchmarking prototype for BN inference (multiple solutions).")]
struct Arguments {
    /// Path to an AEON file with a PSBN model and fixed point annotations.
    model_path: String,

    /// Used SMT encoding type.
    #[clap(long, short, value_parser = PossibleValuesParser::new(["instantiated-eager", "instantiated-lazy", "quantified-individual", "quantified-merge"]), default_value = "instantiated-eager")]
    solver: String,

    /// Automatically eliminates some simple Boolean universal quantifiers
    #[clap(long, default_value = "true")]
    boolean_quantifier_optimization: Option<bool>,

    /// When lazy instantiation is enabled, this option enforces that a fresh solver is used
    /// for every iteration. This is typically *worse* than reusing an existing solver (hence
    /// the option is off by default). However, in rare cases it can be helpful to reset
    /// the solver state between iterations.
    ///
    /// For other solvers, the option is ignored.
    #[clap(long, default_value = "false")]
    force_lazy_reinitialization: Option<bool>,

    /// Automatically propagates exact state observations, simplifying the SMT query
    #[clap(long, default_value = "true")]
    propagate_observations: Option<bool>,

    /// If set to `true`, the solver will print the inferred update functions for all variables.
    #[clap(long, default_value = "false")]
    print_update_rules: bool,

    /// If set to `true`, the solver will also print the inferred state valuations.
    #[clap(long, default_value = "false")]
    print_state_valuations: bool,

    /// Log level verbosity. Flag `-v` sets log level to 'info'. Manually, you can specify: trace, debug, info, warn, or error.
    #[arg(long, short, num_args = 0..=1, default_missing_value = "info", require_equals = true)]
    verbose: Option<String>,

    /// Blocking strategy to use for enumeration.
    #[clap(value_parser = PossibleValuesParser::new(["state-valuations", "function-points", "combined"]), default_value = "state-valuations")]
    blocker: String,

    /// Maximum solutions that will be enumerated.
    #[clap(long = "limit", default_value_t = 1)]
    limit: usize,
}

fn main() -> Result<(), anyhow::Error> {
    let args = Arguments::parse();

    // Handle verbose logging - if specified, override env_logger settings.
    // Otherwise, adhere to settings read from `RUST_LOG`.
    if let Some(ref log_level_str) = args.verbose {
        let filter = match log_level_str.as_str() {
            "trace" => log::LevelFilter::Trace,
            "debug" => log::LevelFilter::Debug,
            "info" => log::LevelFilter::Info,
            "warn" => log::LevelFilter::Warn,
            "error" => log::LevelFilter::Error,
            _ => log::LevelFilter::Info,
        };

        env_logger::Builder::from_default_env()
            .filter_module("biodivine_algo_smt_inference", filter)
            .filter_module("inference_problem_solver_iterative", filter)
            .init();
    } else {
        env_logger::init();
    }

    let model_string = std::fs::read_to_string(&args.model_path)?;
    let psbn = BooleanNetwork::try_from(model_string.as_str()).unwrap();
    let psbn = psbn.name_implicit_parameters();
    let psbn = Rc::new(psbn);
    let annotations = ModelAnnotation::from_model_string(&model_string);

    info!("Building solver using `{}` encoding..", args.solver);

    let mut inference_problem = InferenceProblem::<DynMonotoneBoundedIntOptimizeSolver>::new();

    let base_solver = BoundedIntSolver::new_strict(z3::Optimize::new());
    let mut solver: DynMonotoneBoundedIntOptimizeSolver = match args.solver.as_str() {
        "quantified-individual" => Box::new(QuantifiedMonotoneSolver::new(
            base_solver,
            args.boolean_quantifier_optimization.unwrap_or(true),
        )),
        "quantified-merge" => Box::new(QuantifiedMonotoneSolver::new_merge(
            base_solver,
            args.boolean_quantifier_optimization.unwrap_or(true),
        )),
        "instantiated-eager" => Box::new(InstantiatedMonotoneSolver::new(base_solver)),
        "instantiated-lazy" => Box::new(InstantiatedMonotoneSolver::new_lazy(
            base_solver,
            args.force_lazy_reinitialization.unwrap_or(false),
        )),
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
    inference_problem.initialize_constraints_and_weights(&psbn, &annotations)?;

    info!("Inference problem initialized. Creating constraints.");

    let encoder = InferenceProblemEncoder::new(
        inference_problem,
        &mut solver,
        args.propagate_observations.unwrap_or(true),
    )?;

    let encoder = Rc::new(encoder);

    info!(
        "Checking for up to {} solutions using {} blocking strategy...",
        args.limit, args.blocker
    );

    let blocking_strategy = get_blocking_strategy(&args.blocker);
    let mut solution_iterator = InferenceSolverIterator::new(&encoder, solver, blocking_strategy);
    let all_models = solution_iterator.get_n_solutions(
        Some(args.limit),
        args.print_state_valuations,
        args.print_update_rules,
        |_| Ok(()),
    );

    // Print 1/0 as the last piece of output:
    println!("{}", all_models.len());
    Ok(())
}

fn get_blocking_strategy(blocking_str: &str) -> BlockingStrategy {
    match blocking_str {
        "state-valuations" => BlockingStrategy::StateValuation,
        "function-points" => BlockingStrategy::FunctionPoints,
        "combined" => BlockingStrategy::Combined,
        _ => panic!("Unsupported blocking strategy: {blocking_str}"),
    }
}
