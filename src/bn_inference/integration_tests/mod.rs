// Hopefully, we'll be able to add more tests later on. For now, this is just a few simple
// test cases to make sure the latest features work as expected.

mod fully_specified;

use crate::smt_solver::{BoundedIntSolver, DynMonotoneBoundedIntSolver, QuantifiedMonotoneSolver};

/// Default solver to use in integration tests.
fn build_test_solver() -> DynMonotoneBoundedIntSolver {
    Box::new(QuantifiedMonotoneSolver::new(
        BoundedIntSolver::new_strict(z3::Solver::new()),
        true,
    ))
}
