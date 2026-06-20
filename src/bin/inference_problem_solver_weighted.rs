use biodivine_algo_smt_inference::bn_inference::constraints::SoftConstraint;
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_algo_smt_inference::smt_solver::{
    AbstractOptimizeSolver, AbstractSolver, BoundedIntSolver, DynMonotoneBoundedIntOptimizeSolver,
    InstantiatedMonotoneSolver, QuantifiedMonotoneSolver,
};
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation};
use clap::Parser;
use clap::builder::PossibleValuesParser;
use log::{debug, error, info};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::time::Instant;
use z3::{Model, SatResult, set_global_param};

#[derive(Parser)]
#[clap(about = "SMT benchmarking prototype for BN inference (single solution).")]
struct Arguments {
    /// Path to an AEON file with a PSBN model and fixed point annotations.
    model_path: String,

    /// If specified, a satisfying BN is saved to this file (only supported for Boolean inference problems).
    #[clap(short, long)]
    output_path: Option<String>,

    /// Used SMT monotonicity encoding type.
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

    /// If set to `true`, the solver will also print a summary of violated soft constraints.
    /// If `verbose` is set to `debug`, it also prints every violated constraint.
    #[clap(long, default_value = "false")]
    print_soft_constraints: bool,

    /// If set to `true`, the solver will also print every intermediate solution, using the
    /// same print settings as for the final solution (except for printing/saving update rules).
    #[clap(long, default_value = "false")]
    print_intermediate_results: bool,

    /// If set to `true`, turns every variable with more than three outgoing regulations into
    /// a multivalued variable with domain size proportional to regulation count.
    #[clap(long, default_value = "false")]
    auto_expand_domains: bool,

    /// Log level verbosity. Flag `-v` sets log level to 'info'. Manually, you can specify: trace, debug, info, warn, or error.
    /// Settings 'info', 'debug' and 'trace' also enable verbose logging within Z3.
    #[arg(long, short, num_args = 0..=1, default_missing_value = "info", require_equals = true)]
    verbose: Option<String>,
}

fn main() -> Result<(), anyhow::Error> {
    let args = Arguments::parse();
    let args = Rc::new(args);
    let start = Instant::now();

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
            .filter_module("inference_problem_solver_weighted", filter)
            .init();
    } else {
        env_logger::init();
    }

    // If the log level is at least `Debug`, enable verbose logging in Z3.
    if log::max_level() >= log::LevelFilter::Info {
        set_global_param("verbose", "1");
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
        let targets = psbn.as_graph().targets(var).len();
        let max_value = if args.auto_expand_domains && targets >= 3 {
            info!(
                "Setting max. value of {name} with {targets} targets to {}.",
                targets - 1
            );
            targets as u32
        } else {
            max_value
        };

        let var_p = inference_problem.declare_variable(name.as_str(), (0, max_value));
        assert_eq!(var_p, var);
    }

    inference_problem.initialize_regulations(psbn.as_graph())?;
    inference_problem.initialize_constraints_and_weights(&psbn, &annotations)?;

    // TODO: fully specified functions are ignored for now (all updates are considered uninterpreted)
    //inference_problem.initialize_update_expressions(&psbn)?;

    info!("Inference problem initialized. Creating constraints.");

    let encoder = InferenceProblemEncoder::new(
        inference_problem,
        &mut solver,
        args.propagate_observations.unwrap_or(true),
    )?;

    let encoder = Rc::new(encoder);

    info!("Checking for solution...");

    if args.print_intermediate_results {
        let args_copy = args.clone();
        let psbn_copy = psbn.clone();
        let encoder_copy = encoder.clone();
        solver.register_model_handler(Box::new(move |result| {
            let elapsed = start.elapsed();
            info!("New solution found. Elapsed: {}ms.", elapsed.as_millis());

            report_solution(&args_copy, &psbn_copy, &encoder_copy, None, result)
                .expect("Failed to report solution");
        }));
    }

    let result = solver.check();

    info!("Has solution? {:?}", result);

    if result == SatResult::Sat {
        let model = solver.get_model().unwrap();
        report_solution(
            &args,
            psbn.as_ref(),
            encoder.as_ref(),
            Some(&solver),
            &model,
        )?;
    }

    // TODO: This code should be simplified once we have a nicer way of handling priority classes:
    let mut priority_classes = BTreeSet::new();
    for c in encoder.problem.constraints() {
        let Some(c) = c.downcast_ref::<SoftConstraint<DynMonotoneBoundedIntOptimizeSolver>>()
        else {
            continue;
        };
        priority_classes.insert(c.priority_class);
    }
    for cls in 0..priority_classes.len() {
        println!(
            "Priority class `{cls}` penalty bounds: [{:?}, {:?}]",
            solver.get_lower(cls as u32),
            solver.get_upper(cls as u32),
        );
    }

    // Print 1/0 as the last piece of output:
    match result {
        SatResult::Unsat => println!("0"),
        SatResult::Unknown => println!("?"),
        SatResult::Sat => println!("1"),
    }

    Ok(())
}

fn report_solution(
    args: &Arguments,
    psbn: &BooleanNetwork,
    encoder: &InferenceProblemEncoder<DynMonotoneBoundedIntOptimizeSolver>,
    solver: Option<&DynMonotoneBoundedIntOptimizeSolver>,
    model: &Model,
) -> Result<(), anyhow::Error> {
    // TODO: Find a way to evaluate functions without needing the solver.
    if let Some(solver) = solver {
        if let Some(output_path) = args.output_path.clone() {
            match encoder.decode_boolean_network(solver, model, true) {
                Ok(bn) => {
                    let bn = bn.inline_constants(true, true);
                    std::fs::write(output_path, bn.to_string())?;
                }
                Err(err) => {
                    error!("Unable to decode boolean network. {err}",);
                }
            }
        }

        if args.print_update_rules {
            for var in psbn.variables() {
                if let Some(update_expr) = encoder.update_function(var).as_fn_update() {
                    // Fully specified functions are printed as is
                    println!(
                        "=== Function expression {} (fully specified) ===",
                        psbn.get_variable_name(var)
                    );
                    println!("{}\n", update_expr.to_string(psbn));
                } else {
                    // Uninterpreted functions are extracted from the inferred solutions
                    let function = encoder.decode_update_function(var, solver, model)?;
                    println!(
                        "=== Function table {} (inferred) ===",
                        psbn.get_variable_name(var)
                    );
                    println!("{}", function);
                }
            }
        }
    }

    if args.print_state_valuations {
        println!("=== State table ===");
        for state in encoder.problem.states() {
            let decoded = encoder.decode_state(&state, model);
            let named = decoded
                .into_iter()
                .map(|(a, b)| (psbn.get_variable_name(a), b))
                .collect::<BTreeMap<_, _>>();
            println!("`{state}`: {:?}", named);
        }
    }

    if args.print_soft_constraints {
        println!("=== Constraint satisfaction ===");
        print_violated_clauses(encoder, model)?;
    }

    Ok(())
}

/// Print summary statistics about violated soft constraints (and the actual constraints).
fn print_violated_clauses<SOLVER: AbstractOptimizeSolver + 'static>(
    encoder: &InferenceProblemEncoder<SOLVER>,
    model: &Model,
) -> Result<(), anyhow::Error> {
    #[derive(Default)]
    struct ViolationStats {
        total: BigRational,
        violated: BigRational,
        violated_constraints: u32,
        total_constraints: u32,
    }

    let mut per_class_data: BTreeMap<u32, ViolationStats> = BTreeMap::new();

    for constraint in encoder.problem.constraints() {
        let Some(constraint) = constraint.downcast_ref::<SoftConstraint<SOLVER>>() else {
            continue;
        };

        let data = per_class_data.entry(constraint.priority_class).or_default();
        data.total += &constraint.weight;
        data.total_constraints += 1;

        let formula = constraint.constraint.mk_assertion(encoder)?;

        let is_satisfied = model
            .eval(&formula, true)
            .and_then(|it| it.as_bool())
            .expect("Constraint cannot be evaluated.");

        if !is_satisfied {
            data.violated_constraints += 1;
            data.violated += &constraint.weight;
            debug!("Violated: `{constraint:?}`");
        }
    }

    for (cls, data) in per_class_data.iter() {
        println!(
            "Priority class `{cls}` model penalty: `{}` out of `{}` across `{}` out of `{}` constraints.",
            data.violated, data.total, data.violated_constraints, data.total_constraints,
        );
    }

    Ok(())
}
