// Hopefully, we'll be able to add more tests later on. For now, this is just a few simple
// test cases to make sure the latest features work as expected.

/// Simple tests that verify exact, fully specified networks have the claimed properties.
mod exact_networks;

/// Simple example tests of partially specified networks.
mod partially_specified;

/// Test that fully specified expressions inside partially specified networks work as intended.
mod fully_specified;

/// Test basic properties of enumeration / iteration.
mod iteration;

use crate::smt_solver::{
    BoundedIntSolver, DynMonotoneBoundedIntOptimizeSolver, DynMonotoneBoundedIntSolver,
    QuantifiedMonotoneSolver,
};

/// Default solver to use in integration tests.
fn build_test_solver() -> DynMonotoneBoundedIntSolver {
    Box::new(QuantifiedMonotoneSolver::new(
        BoundedIntSolver::new_strict(z3::Solver::new()),
        true,
    ))
}

/// Default solver to use in integration tests with optimization.
fn build_test_optimization_solver() -> DynMonotoneBoundedIntOptimizeSolver {
    Box::new(QuantifiedMonotoneSolver::new(
        BoundedIntSolver::new_strict(z3::Optimize::new()),
        true,
    ))
}
