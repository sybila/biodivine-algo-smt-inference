use crate::smt_solver::AbstractSolver;
use log::trace;
use num_rational::BigRational;
use z3::ast::{Bool, Dynamic};
use z3::{Model, SatResult};

pub type DynOptimizeSolver = Box<dyn AbstractOptimizeSolver>;

/// Trait implemented by solvers that can perform basic optimization over assertions with weight.
pub trait AbstractOptimizeSolver: AbstractSolver {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational);
    fn get_lower(&self, objective_id: u32) -> Option<Dynamic>;
    fn get_upper(&self, objective_id: u32) -> Option<Dynamic>;
    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>);
}

impl AbstractOptimizeSolver for z3::Optimize {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        trace!("[assert-soft][{}] {}", weight, formula);
        z3::Optimize::assert_soft(self, formula, weight, None)
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        z3::Optimize::get_lower(self, objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        z3::Optimize::get_upper(self, objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        z3::Optimize::register_model_handler(self, callback)
    }
}

impl AbstractSolver for DynOptimizeSolver {
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

impl AbstractOptimizeSolver for DynOptimizeSolver {
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
        self.as_ref().register_model_handler(callback)
    }
}
