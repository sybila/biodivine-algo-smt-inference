mod abstract_solver;
pub use abstract_solver::AbstractSolver;
pub use abstract_solver::DynAbstractSolver;

mod abstract_optimize_solver;
pub use abstract_optimize_solver::AbstractOptimizeSolver;
pub use abstract_optimize_solver::DynOptimizeSolver;

mod abstract_monotone_solver;
pub use abstract_monotone_solver::AbstractMonotoneOptimizeSolver;
pub use abstract_monotone_solver::AbstractMonotoneSolver;
pub use abstract_monotone_solver::DynMonotoneOptimizeSolver;
pub use abstract_monotone_solver::DynMonotoneSolver;
pub use abstract_monotone_solver::Monotonicity;

mod quantified_monotone_solver;
pub use quantified_monotone_solver::QuantifiedMonotoneSolver;

mod instantiated_monotone_solver;
pub use instantiated_monotone_solver::InstantiatedMonotoneSolver;

/// Wrappers that allow us to work with Z3 ASTs restricted to `Bool` and `Int`
/// types in a slightly more convenient way.
pub mod typed_ast;

mod utils;
pub(crate) use utils::*;
