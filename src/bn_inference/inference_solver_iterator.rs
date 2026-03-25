use std::collections::BTreeMap;
use std::str::FromStr;

use anyhow::anyhow;
use log::info;
use z3::ast::Dynamic;

use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::{AbstractMonotoneSolver, collect_asserted_fn_calls};

#[derive(Debug, Clone)]
pub enum BlockingStrategy {
    // Block state valuations, either just for a specified BN variable or for all.
    StateValuations(Option<String>),
    // Block function interpretation, either just for a function of the specified
    // BN variable or for all functions.
    FunctionPoints(Option<String>),
}

impl BlockingStrategy {
    pub fn validate<SOLVER: AbstractMonotoneSolver + 'static>(
        &self,
        problem: &InferenceProblem<SOLVER>,
    ) -> Result<(), anyhow::Error> {
        match &self {
            BlockingStrategy::StateValuations(Some(var)) => {
                if problem.find_variable(var).is_none() {
                    Err(anyhow!("Invalid BN variable {var} in blocking strategy."))
                } else {
                    Ok(())
                }
            }
            BlockingStrategy::FunctionPoints(Some(var)) => {
                if let Some(var_id) = problem.find_variable(var) {
                    if problem[var_id].has_update_expr() {
                        Err(anyhow!(
                            "Can not iterate over functions for variable {var}, its function is fully specified."
                        ))
                    } else {
                        Ok(())
                    }
                } else {
                    Err(anyhow!("Invalid BN variable {var} in blocking strategy."))
                }
            }
            _ => Ok(()),
        }
    }
}

// This trait tells Clap how to turn the User's String into your Enum
impl FromStr for BlockingStrategy {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<&str> = s.splitn(2, ':').collect();

        match parts[0] {
            "state-valuations" => {
                let name = parts.get(1).map(|&s| s.to_string());
                Ok(BlockingStrategy::StateValuations(name))
            }
            "function-points" => {
                let name = parts.get(1).map(|&s| s.to_string());
                Ok(BlockingStrategy::FunctionPoints(name))
            }
            _ => Err(format!(
                "Unknown blocker: {}. Valid: state-valuations, function-points, combined",
                parts[0]
            )),
        }
    }
}

/// Iterates through solutions provided by a prepared solver, using an encoder
/// and a particular blocking strategy to ensure uniqueness.
///
/// This wrapper maintains the solver state and applies the [`BlockingStrategy`]
/// after each successful SAT result to exclude previously found models from
/// the search space.
pub struct InferenceSolverIterator<'a, SOLVER> {
    /// Referencing the associated inference encoder.
    pub encoder: &'a InferenceProblemEncoder<SOLVER>,

    /// The solver instance used for finding solutions.
    /// TODO: currently the solver is fully owned, but reference may be sufficient.
    ///       Intuitively, I'd prefer full ownership as is.
    pub solver: SOLVER,

    /// Strategy used to exclude found models from subsequent iterations.
    pub blocking_strategy: BlockingStrategy,

    // Precomputed map of all unique function occurances. This is only useful for
    // blocking strategies involving functions.
    unique_fn_calls: BTreeMap<String, Vec<Dynamic>>,
}

impl<'a, SOLVER: AbstractMonotoneSolver + 'static> InferenceSolverIterator<'a, SOLVER> {
    pub fn new(
        encoder: &'a InferenceProblemEncoder<SOLVER>,
        solver: SOLVER,
        blocking_strategy: BlockingStrategy,
    ) -> Self {
        // For some blocking strategies involving functions, we precompute all
        // unique function occurances in the original solver assertions.
        let unique_fn_calls: BTreeMap<String, Vec<Dynamic>> = match blocking_strategy {
            BlockingStrategy::StateValuations(..) => BTreeMap::new(),
            BlockingStrategy::FunctionPoints(..) => collect_asserted_fn_calls(&solver, encoder),
        };

        InferenceSolverIterator {
            encoder,
            solver,
            blocking_strategy,
            unique_fn_calls,
        }
    }

    /// Iterate over satisfying solutions using the provided blocking strategy.
    /// If a limit `max_solutions` is provided, only the given number of solutions will
    /// be enumerated (note that at least one solution is always checked).
    ///
    /// This method builds a solver, checks for satisfiability, and uses the provided strategy
    /// to generate blocking clauses to exclude each found solution from subsequent checks.
    /// The `strategy` determines how to block each found model, see [`BlockingStrategy`].
    ///
    /// For now, we use a `callback` function to process each solution as we go. This can
    /// be used for custom on-the-fly logging or to stop computation when some external condition
    /// is met. We allow the callback to return error and finish the computation from the outside
    /// for convenience. It is recommended to use `max_solutions` for simple solution limit though.
    ///
    /// This expects that the blocking strategy was validated by [BlockingStrategy::validate]
    pub fn get_n_solutions<F>(
        &mut self,
        max_solutions: Option<usize>,
        print_fixed_points: bool,
        print_functions: bool,
        mut callback: F,
    ) -> Vec<z3::Model>
    where
        F: FnMut(&z3::Model) -> Result<(), anyhow::Error>,
    {
        let mut collected_models = Vec::new();

        loop {
            // Check for satisfiability and stop if not sat
            if self.solver.check() != z3::SatResult::Sat {
                break;
            }

            // The model will be pushed to `collected_models` at the end of the
            // iteration to avoid passing the reference there and back
            let model = self
                .solver
                .get_model()
                .expect("Failed to get model from solver");
            println!("==== Found model n. {} ====", collected_models.len() + 1);

            if print_fixed_points {
                println!("= Fixed point states =");
                for obs in self.encoder.problem.states() {
                    let state = self.encoder.decode_state(&obs, &model);
                    println!("> {obs}: {:?}", state);
                }
                println!();
            }
            if print_functions {
                println!("= Function interpretations =");
                for var in self.encoder.problem.variables() {
                    if let Some(update_expr) = self.encoder.update_function(var).as_fn_update() {
                        println!(
                            "> Function expression {} (fully spec)",
                            self.encoder.problem.get_variable(var).unwrap().name
                        );
                        println!("{}\n", update_expr);
                    } else {
                        let function = self
                            .encoder
                            .decode_update_function(var, &self.solver, &model)
                            .unwrap();
                        println!(
                            "> Function table {} (inferred)",
                            self.encoder.problem.get_variable(var).unwrap().name
                        );
                        println!("{}", function);
                    }
                }
            }
            if callback(&model).is_err() {
                collected_models.push(model);
                break;
            }

            // If a solution limit is specified and reached, we immediately
            // break before generating the blocking clause (since that can be
            // resource demanding)
            if let Some(max) = max_solutions
                && collected_models.len() + 1 >= max
            {
                collected_models.push(model);
                break;
            }

            let blocker = match &self.blocking_strategy {
                BlockingStrategy::StateValuations(bn_var_name) => {
                    let bn_var = bn_var_name
                        .as_ref()
                        .map(|v_name| self.encoder.problem.find_variable(v_name).unwrap());
                    self.encoder
                        .generate_state_valuation_blocker(&model, None, bn_var)
                }
                BlockingStrategy::FunctionPoints(bn_var_name) => {
                    let fn_name = bn_var_name
                        .as_ref()
                        .map(|v_name| self.encoder.problem.find_variable(v_name).unwrap())
                        .map(|v_id| {
                            // We can safely unwrap here, as this had to be checked by [BlockingStrategy::validate]
                            self.encoder
                                .update_function(v_id)
                                .as_func_decl()
                                .unwrap()
                                .name()
                        });

                    self.encoder.generate_function_points_blocker(
                        &model,
                        fn_name,
                        &self.unique_fn_calls,
                    )
                }
            };

            // Generate and assert a blocking clause
            match blocker {
                Ok(blocker) => {
                    info!(
                        "Generating blocking formula using {:?} strategy",
                        &self.blocking_strategy
                    );
                    self.solver.assert(&blocker);
                }
                Err(e) => {
                    // If we can't generate a blocker, there is something really wrong
                    panic!("Failed to generate blocker: {}", e);
                }
            }

            collected_models.push(model);
        }

        collected_models
    }
}
