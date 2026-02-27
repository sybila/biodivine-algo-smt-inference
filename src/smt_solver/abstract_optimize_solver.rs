use crate::smt_solver::AbstractSolver;
use auto_impl::auto_impl;
use log::trace;
use num_rational::BigRational;
use z3::Model;
use z3::ast::{Bool, Dynamic};

/// Trait implemented by solvers that can perform basic optimization over assertions with weight.
#[auto_impl(Box)]
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
