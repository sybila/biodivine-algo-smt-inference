use crate::smt_solver::abstract_solver_combinations::{
    AbstractBoundedIntOptimizeSolver, AbstractMonotoneBoundedIntOptimizeSolver,
    AbstractMonotoneBoundedIntSolver, AbstractMonotoneOptimizeSolver,
};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver,
};

/// Box-dyn variant of the base [`AbstractSolver`].
pub type DynAbstractSolver = Box<dyn AbstractSolver>;

// Variants that inherit directly from the abstract solver:

/// Box-dyn variant of the [`AbstractOptimizeSolver`].
pub type DynOptimizeSolver = Box<dyn AbstractOptimizeSolver>;

/// Box-dyn variant of the [`AbstractMonotoneSolver`].
pub type DynMonotoneSolver = Box<dyn AbstractMonotoneSolver>;

/// Box-dyn variant of the [`AbstractBoundedIntSolver`].
pub type DynBoundedIntSolver = Box<dyn AbstractBoundedIntSolver>;

// Variants that implement trait combinations:

/// Box-dyn variant of the [`AbstractMonotoneOptimizeSolver`].
pub type DynMonotoneOptimizeSolver = Box<dyn AbstractMonotoneOptimizeSolver>;

/// Box-dyn variant of the [`AbstractBoundedIntOptimizeSolver`].
pub type DynBoundedIntOptimizeSolver = Box<dyn AbstractBoundedIntOptimizeSolver>;

/// Box-dyn variant of the [`AbstractMonotoneBoundedIntSolver`].
pub type DynMonotoneBoundedIntSolver = Box<dyn AbstractMonotoneBoundedIntSolver>;

/// Box-dyn variant of the [`AbstractMonotoneBoundedIntOptimizeSolver`].
pub type DynMonotoneBoundedIntOptimizeSolver = Box<dyn AbstractMonotoneBoundedIntOptimizeSolver>;
