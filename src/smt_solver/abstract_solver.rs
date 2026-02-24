use auto_impl::auto_impl;
use log::trace;
use z3::ast::Bool;
use z3::{Model, SatResult};

/// The most basic trait implemented by all solvers.
#[auto_impl(Box)]
pub trait AbstractSolver {
    fn assert(&mut self, formula: &Bool);
    fn check(&self) -> SatResult;
    fn get_model(&self) -> Option<Model>;
}

impl AbstractSolver for z3::Solver {
    fn assert(&mut self, formula: &Bool) {
        trace!("[assert] {}", formula);
        z3::Solver::assert(self, formula);
    }

    fn check(&self) -> SatResult {
        z3::Solver::check(self)
    }

    fn get_model(&self) -> Option<Model> {
        z3::Solver::get_model(self)
    }
}

impl AbstractSolver for z3::Optimize {
    fn assert(&mut self, formula: &Bool) {
        trace!("[assert-optimize] {}", formula);
        z3::Optimize::assert(self, formula);
    }

    fn check(&self) -> SatResult {
        z3::Optimize::check(self, &[])
    }

    fn get_model(&self) -> Option<Model> {
        z3::Optimize::get_model(self)
    }
}
