// Due to how trait objects work in Rust, it is really inconvenient to use intersection
// types with `dyn`. As such, we have to define combinations of solver traits as separate traits.
// All combinations are:
// - monotone + optimize
// - monotone + bounded int
// - bounded int + optimize
// - monotone + bounded int + optimize
// Implementation "specificity" should be `monotone < bounded int < optimize`.

use crate::smt_solver::{AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver};

/// Trait that can be used as a placeholder for `AbstractOptimizeSolver + AbstractMonotoneSolver`.
pub trait AbstractMonotoneOptimizeSolver: AbstractOptimizeSolver + AbstractMonotoneSolver {}
impl<T: AbstractOptimizeSolver + AbstractMonotoneSolver> AbstractMonotoneOptimizeSolver for T {}

/// Trait that can be used as a placeholder for `AbstractBoundedIntSolver + AbstractMonotoneSolver`.
pub trait AbstractMonotoneBoundedIntSolver:
    AbstractMonotoneSolver + AbstractBoundedIntSolver
{
}
impl<T: AbstractMonotoneSolver + AbstractBoundedIntSolver> AbstractMonotoneBoundedIntSolver for T {}

/// Trait that can be used as a placeholder for `AbstractBoundedIntSolver + AbstractOptimizeSolver`.
pub trait AbstractBoundedIntOptimizeSolver:
    AbstractOptimizeSolver + AbstractBoundedIntSolver
{
}
impl<T: AbstractOptimizeSolver + AbstractBoundedIntSolver> AbstractBoundedIntOptimizeSolver for T {}

/// Trait that can be used as a placeholder for `AbstractMonotoneSolver + AbstractBoundedIntSolver + AbstractOptimizeSolver`.
pub trait AbstractMonotoneBoundedIntOptimizeSolver:
    AbstractMonotoneOptimizeSolver + AbstractMonotoneBoundedIntSolver + AbstractBoundedIntOptimizeSolver
{
}
impl<T: AbstractOptimizeSolver + AbstractBoundedIntSolver + AbstractMonotoneSolver>
    AbstractMonotoneBoundedIntOptimizeSolver for T
{
}
