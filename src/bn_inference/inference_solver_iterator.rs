use std::collections::BTreeMap;

use z3::ast::Dynamic;

use crate::bn_inference::InferenceProblemEncoder;
use crate::smt_solver::{AbstractMonotoneSolver, collect_asserted_fn_calls};

pub enum BlockingStrategy {
    FixedPoints,
    FunctionPoints,
    Combined,
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
            BlockingStrategy::FixedPoints => BTreeMap::new(),
            BlockingStrategy::FunctionPoints | BlockingStrategy::Combined => {
                collect_asserted_fn_calls(&solver)
            }
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
                    let function = self
                        .encoder
                        .decode_update_function(var, &self.solver, &model)
                        .unwrap();
                    println!(
                        "> Function table {}",
                        self.encoder.problem.get_variable(var).unwrap().name
                    );
                    println!("{}", function);
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

            let blocker =
                match self.blocking_strategy {
                    BlockingStrategy::FixedPoints => {
                        self.encoder.generate_fixed_point_blocker(&model, None)
                    }
                    BlockingStrategy::FunctionPoints => self
                        .encoder
                        .generate_function_points_blocker(&model, None, &self.unique_fn_calls),
                    BlockingStrategy::Combined => todo!(),
                };

            // Generate and assert a blocking clause
            match blocker {
                Ok(blocker) => {
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
