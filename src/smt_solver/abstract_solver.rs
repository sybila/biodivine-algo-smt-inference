use log::trace;
use z3::ast::Bool;
use z3::{Model, SatResult};

pub type DynAbstractSolver = Box<dyn AbstractSolver>;

/// The most basic trait implemented by all solvers.
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

impl AbstractSolver for DynAbstractSolver {
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
