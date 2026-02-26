use crate::smt_solver::{
    IntAtom, IntFunction, extract_function_applications, extract_function_type_signature,
    model_eval_int,
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
                let args = func_call
                    .children()
                    .iter()
                    .enumerate()
                    .map(|(i, child)| IntAtom::eq(i, model_eval_int(child, model)))
                    .collect::<Vec<_>>();

                let output = model_eval_int(&func_call, model);
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
}
