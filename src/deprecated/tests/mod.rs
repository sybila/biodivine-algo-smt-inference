use crate::deprecated::{EncodingMode, InferenceProblem};
use crate::smt_solver::DynOptimizeSolver;

/// Tests the SMT inference method on a few toy models.
mod inference_toy_models;

/// Very simple tests for naive inference method using toy models.
mod inference_naive;

fn get_instantiation_solver(problem: &InferenceProblem) -> DynOptimizeSolver {
    problem.build_solver(EncodingMode::Instantiation)
}
