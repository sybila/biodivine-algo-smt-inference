use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractOptimizeSolver, AbstractSolver, extract_int_functions,
};
use anyhow::anyhow;
use num_rational::BigRational;
use std::collections::BTreeMap;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{FuncDecl, Model, SatResult};

/// Initial implementation of [`AbstractBoundedIntSolver`] which actually uses `Int` values
/// and additional assertions. Eventually, we may want to extend the bounded domains to
/// bit-vectors or other types as well.
pub struct BoundedIntSolver<SOLVER: AbstractSolver> {
    inner: SOLVER,
    /// Indicates whether it is allowed to use undeclared functions. If `false`, every `Int`
    /// uninterpreted function has to be declared before first use.
    allow_undeclared: bool,
    declarations: BTreeMap<String, Option<(u32, u32)>>,
}

impl<SOLVER: AbstractSolver> BoundedIntSolver<SOLVER> {
    pub fn new(inner: SOLVER, allow_undeclared: bool) -> Self {
        Self {
            inner,
            allow_undeclared,
            declarations: Default::default(),
        }
    }

    pub fn new_strict(inner: SOLVER) -> Self {
        Self {
            inner,
            allow_undeclared: false,
            declarations: Default::default(),
        }
    }

    fn handle_assertion(&mut self, formula: &Bool) {
        // First, assert that every usage of an `Int` function that appears in the assertion
        // is within the expected domain.
        for int_function in extract_int_functions(formula) {
            let name = int_function.decl().name();
            let domain = self.declarations.get(&name);
            if domain.is_none() && !self.allow_undeclared {
                // Undeclared and user requested this to be an error.
                panic!("Cannot use undeclared `Int` function `{}`.", name);
            } else if let Some(domain) = domain
                && let Some((min, max)) = domain
            {
                self.inner
                    .assert(&int_function.le(Int::from_u64(u64::from(*max))));
                self.inner
                    .assert(&int_function.ge(Int::from_u64(u64::from(*min))));
            } // else: The function is declared but unbounded.
            // Undeclared functions are otherwise skipped.
        }
    }
}

impl<SOLVER: AbstractSolver> AbstractBoundedIntSolver for BoundedIntSolver<SOLVER> {
    fn declare_int(
        &mut self,
        f: &FuncDecl,
        domain: Option<(u32, u32)>,
    ) -> Result<(), anyhow::Error> {
        // Check that this is not a duplicate declaration:
        if let Some(existing) = self.declarations.get(&f.name()) {
            return if *existing != domain {
                Err(anyhow!(
                    "Cannot redefine existing `Int` named `{}`",
                    f.name()
                ))
            } else {
                Ok(())
            };
        };

        // Add the declaration:
        self.declarations.insert(f.name(), domain);

        Ok(())
    }
}

impl<SOLVER: AbstractSolver> AbstractSolver for BoundedIntSolver<SOLVER> {
    fn assert(&mut self, formula: &Bool) {
        self.handle_assertion(formula);
        self.inner.assert(formula);
    }

    fn check(&mut self) -> SatResult {
        self.inner.check()
    }

    fn get_model(&self) -> Option<Model> {
        self.inner.get_model()
    }

    fn get_assertions(&self) -> Vec<Bool> {
        self.inner.get_assertions()
    }
}

impl<SOLVER: AbstractOptimizeSolver> AbstractOptimizeSolver for BoundedIntSolver<SOLVER> {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.handle_assertion(formula);
        self.inner.assert_soft(formula, weight);
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_lower(objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_upper(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.inner.register_model_handler(callback);
    }
}
