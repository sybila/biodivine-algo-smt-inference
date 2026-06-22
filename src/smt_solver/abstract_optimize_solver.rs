use crate::smt_solver::AbstractSolver;
use auto_impl::auto_impl;
use log::trace;
use num_rational::BigRational;
use z3::ast::{Bool, Dynamic};
use z3::{Model, Symbol};

/// Trait implemented by solvers that can perform basic optimization over assertions with weight.
#[auto_impl(Box)]
pub trait AbstractOptimizeSolver: AbstractSolver {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        Self::assert_soft_with_class(self, formula, weight, None);
    }

    fn assert_soft_with_class(
        &mut self,
        formula: &Bool,
        weight: BigRational,
        class: Option<Symbol>,
    );
    fn get_lower(&self, objective_id: u32) -> Option<Dynamic>;
    fn get_upper(&self, objective_id: u32) -> Option<Dynamic>;
    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>);
}

impl AbstractOptimizeSolver for z3::Optimize {
    fn assert_soft_with_class(
        &mut self,
        formula: &Bool,
        weight: BigRational,
        class: Option<Symbol>,
    ) {
        trace!(
            "[assert-soft][weight:{};class:{:?}] {}",
            weight, class, formula
        );
        z3::Optimize::assert_soft(self, formula, weight, class)
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        z3::Optimize::get_lower(self, objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        z3::Optimize::get_upper(self, objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        z3::Optimize::set_model_handler(self, callback)
    }
}
