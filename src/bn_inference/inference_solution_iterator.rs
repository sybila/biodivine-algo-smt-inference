use std::collections::{BTreeMap, HashSet};

use z3::ast::{Ast, Dynamic};

use crate::bn_inference::InferenceProblemEncoder;
use crate::smt_solver::{AbstractMonotoneSolver, extract_function_applications};

pub enum BlockingStrategy {
    FixedPoints,
    FunctionPoints,
    Combined,
}

pub struct InferenceSolutionIterator<'a, SOLVER> {
    /// Referencing the associated inference encoder.
    pub encoder: &'a InferenceProblemEncoder<SOLVER>,
}

impl<'a, SOLVER: AbstractMonotoneSolver + 'static> InferenceSolutionIterator<'a, SOLVER> {
    pub fn new(encoder: &'a InferenceProblemEncoder<SOLVER>) -> Self {
        InferenceSolutionIterator { encoder }
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
    /// be used for on-the-fly logging or to stop computation when some condition is met.
    /// We allow the callback to return error and finish the computation from the outside for
    /// convenience. It is recommended to use `max_solutions` for simple solution limit though.
    pub fn get_n_solutions<F>(
        &self,
        solver: &mut SOLVER,
        blocking_strategy: &BlockingStrategy,
        max_solutions: Option<usize>,
        print_fixed_points: bool,
        print_functions: bool,
        mut callback: F,
    ) -> Vec<z3::Model>
    where
        F: FnMut(&z3::Model) -> Result<(), anyhow::Error>,
    {
        let mut collected_models = Vec::new();

        // For some blocking strategies involving functions, we should pre-compute
        // all unique function occurances in the original formula.
        let unique_fn_calls: BTreeMap<String, Vec<Dynamic>> = match blocking_strategy {
            BlockingStrategy::FixedPoints => BTreeMap::new(),
            BlockingStrategy::FunctionPoints | BlockingStrategy::Combined => {
                // Collect fn calls into HashSet to only get unique ones
                let mut func_calls_hash: BTreeMap<String, HashSet<Dynamic>> = BTreeMap::new();
                for assertion in solver.get_assertions() {
                    for func_call in extract_function_applications(&assertion) {
                        func_calls_hash
                            .entry(func_call.decl().name())
                            .or_default()
                            .insert(func_call);
                    }
                }
                // Convert the set to a sorted vector for determinism
                func_calls_hash
                    .into_iter()
                    .map(|(name, set)| {
                        let mut v: Vec<Dynamic> = set.into_iter().collect();
                        v.sort_by_key(|call| call.to_string());
                        (name, v)
                    })
                    .collect()
            }
        };

        loop {
            // Check for satisfiability and stop if not sat
            if solver.check() != z3::SatResult::Sat {
                break;
            }

            // The model will be pushed to `collected_models` at the end of the
            // iteration to avoid passing the reference there and back
            let model = solver.get_model().expect("Failed to get model from solver");
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
                        .decode_update_function(var, solver, &model)
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

            let blocker = match blocking_strategy {
                BlockingStrategy::FixedPoints => self.encoder.generate_fixed_point_blocker(&model),
                BlockingStrategy::FunctionPoints => self
                    .encoder
                    .generate_function_points_blocker(&model, &unique_fn_calls),
                BlockingStrategy::Combined => todo!(),
            };

            // Generate and assert a blocking clause
            match blocker {
                Ok(blocker) => {
                    solver.assert(&blocker);
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
