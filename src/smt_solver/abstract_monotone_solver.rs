use crate::smt_solver::{AbstractOptimizeSolver, AbstractSolver};
use num_rational::BigRational;
use z3::ast::{Bool, Dynamic};
use z3::{FuncDecl, Model, SatResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Monotonicity {
    Positive,
    Negative,
}

pub type DynMonotoneSolver = Box<dyn AbstractMonotoneSolver>;
pub type DynMonotoneOptimizeSolver = Box<dyn AbstractMonotoneOptimizeSolver>;

/// Trait implemented by solvers that can explicitly reason about functions with monotone inputs.
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
}

/// Trait that can be used as a placeholder for `AbstractOptimizeSolver + AbstractMonotoneSolver`.
pub trait AbstractMonotoneOptimizeSolver: AbstractOptimizeSolver + AbstractMonotoneSolver {}

// Any type that implements both traits also implements the intersection type.
impl<T: AbstractOptimizeSolver + AbstractMonotoneSolver> AbstractMonotoneOptimizeSolver for T {}

impl AbstractMonotoneSolver for DynMonotoneSolver {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.as_mut().set_monotone(f, i)
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.as_mut().set_antimonotone(f, i)
    }
}

impl AbstractSolver for DynMonotoneSolver {
    fn assert(&mut self, formula: &Bool) {
        self.as_mut().assert(formula);
    }

    fn check(&self) -> SatResult {
        self.as_ref().check()
    }

    fn get_model(&self) -> Option<Model> {
        self.as_ref().get_model()
    }
}

impl AbstractSolver for DynMonotoneOptimizeSolver {
    fn assert(&mut self, formula: &Bool) {
        self.as_mut().assert(formula);
    }

    fn check(&self) -> SatResult {
        self.as_ref().check()
    }

    fn get_model(&self) -> Option<Model> {
        self.as_ref().get_model()
    }
}

impl AbstractOptimizeSolver for DynMonotoneOptimizeSolver {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.as_mut().assert_soft(formula, weight);
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.as_ref().get_lower(objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        self.as_ref().get_upper(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.as_ref().register_model_handler(callback);
    }
}

impl AbstractMonotoneSolver for DynMonotoneOptimizeSolver {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.as_mut().set_monotone(f, i)
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.as_mut().set_antimonotone(f, i)
    }
}
