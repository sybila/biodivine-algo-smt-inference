use crate::smt_solver::{
    IntAtom, IntFunction, extract_function_applications, extract_function_type_signature,
    model_eval_int_function,
};
use auto_impl::auto_impl;
use log::trace;
use std::collections::BTreeMap;
use z3::ast::{Ast, Bool};
use z3::{FuncDecl, Model, SatResult};

/// The most basic trait implemented by all solvers.
#[auto_impl(Box)]
pub trait AbstractSolver {
    fn assert(&mut self, formula: &Bool);
    fn check(&mut self) -> SatResult;
    fn get_model(&self) -> Option<Model>;
    fn get_assertions(&self) -> Vec<Bool>;
    fn reinitialize(&mut self);

    /// Identify all points (input combinations) that are exactly determined by the current
    /// solver query in the provided model and place them into an [`IntFunction`].
    fn extract_function_points(
        &self,
        f: &FuncDecl,
        model: &Model,
    ) -> Result<IntFunction, anyhow::Error> {
        let signature = extract_function_type_signature(f)?;
        let mut terms: BTreeMap<u32, Vec<Vec<IntAtom>>> = BTreeMap::new();

        for assertion in self.get_assertions() {
            for func_call in extract_function_applications(&assertion) {
                if func_call.decl().name() != f.name() {
                    continue;
                }
                let (args, output) = model_eval_int_function(&func_call, model);
                let args = args
                    .into_iter()
                    .enumerate()
                    .map(|(i, val)| IntAtom::eq(i, val))
                    .collect::<Vec<_>>();

                terms.entry(output).or_default().push(args);
            }
        }

        let mut function = IntFunction { signature, terms };
        function.remove_duplicates();
        Ok(function)
    }
}

impl AbstractSolver for z3::Solver {
    fn assert(&mut self, formula: &Bool) {
        trace!("[assert] {}", formula);
        z3::Solver::assert(self, formula);
    }

    fn check(&mut self) -> SatResult {
        z3::Solver::check(self)
    }

    fn get_model(&self) -> Option<Model> {
        z3::Solver::get_model(self)
    }

    fn get_assertions(&self) -> Vec<Bool> {
        z3::Solver::get_assertions(self)
    }
    fn reinitialize(&mut self) {
        let new_solver = z3::Solver::new();
        for assertion in self.get_assertions() {
            new_solver.assert(&assertion);
        }
        *self = new_solver;
    }
}

impl AbstractSolver for z3::Optimize {
    fn assert(&mut self, formula: &Bool) {
        trace!("[assert-optimize] {}", formula);
        z3::Optimize::assert(self, formula);
    }

    fn check(&mut self) -> SatResult {
        z3::Optimize::check(self, &[])
    }

    fn get_model(&self) -> Option<Model> {
        z3::Optimize::get_model(self)
    }

    fn get_assertions(&self) -> Vec<Bool> {
        z3::Optimize::get_assertions(self)
    }

    fn reinitialize(&mut self) {
        // Right now, optimize solver cannot be reinitialized because we don't
        // have a method to get weights of soft assertions.
        // Technically, we might be able to do this by migrating optimization objectives
        // to the new solver, but I'm not sure that's correct.
        // Another alternative would be to make a wrapper around Optimize
        // that will track the weights manually and re-initialize itself based on that.
        unimplemented!();
    }
}
