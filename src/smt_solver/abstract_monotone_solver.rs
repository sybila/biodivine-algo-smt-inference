use crate::smt_solver::AbstractSolver;
use auto_impl::auto_impl;
use z3::FuncDecl;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Monotonicity {
    Positive,
    Negative,
}

/// Trait implemented by solvers that can explicitly reason about functions with monotone inputs.
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

}
