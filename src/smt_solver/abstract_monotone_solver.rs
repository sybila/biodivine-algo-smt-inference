use crate::smt_solver::{AbstractSolver, IntFunction};
use auto_impl::auto_impl;
use z3::{FuncDecl, Model};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Monotonicity {
    Positive,
    Negative,
}

/// Trait implemented by solvers that can explicitly reason about functions with monotone inputs.
///
/// **All monotonicity properties of a function must be declared before the function is first
/// used in an assert.**
#[auto_impl(Box)]
pub trait AbstractMonotoneSolver: AbstractSolver {
    /// Declare the i-th argument of a function as *positively monotone*.
    ///
    /// What type of function can be declared as monotone is solver-dependent, but typically,
    /// the solver should support functions with domain/range using `Int` and `Bool` values.
    /// Returns an error result if the function-argument combination is not supported.
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error>;
    
    /// Declare the i-th argument of a function as *negatively monotone*.
    ///
    /// What type of function can be declared as monotone is solver-dependent, but typically,
    /// the solver should support functions with domain/range using `Int` and `Bool` values.
    /// /// Returns an error result if the function-argument combination is not supported.
    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error>;

    /// Return `Some(true)` or `Some(false)` if the given function is declared as positively
    /// or negatively monotone, `None` otherwise.
    fn is_monotone(&self, f: &FuncDecl, i: usize) -> Option<Monotonicity>;

    /// Extract an [`IntFunction`] which describes all input points that are uniquely determined
    /// by the current Z3 model and query and all points that are transitively enforced by current
    /// monotonicity constraints.
    fn extract_monotone_function_points(
        &self,
        f: &FuncDecl,
        model: &Model,
    ) -> Result<IntFunction, anyhow::Error> {
        let mut point_function = self.extract_function_points(f, model)?;
        for arg_index in 0..f.arity() {
            if let Some(monotone) = self.is_monotone(f, arg_index) {
                point_function.relax_monotone_argument(arg_index, monotone);
            }
        }
        Ok(point_function)
    }
}
