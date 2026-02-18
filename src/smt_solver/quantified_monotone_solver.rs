use crate::smt_solver::{
    AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver, make_dyn_vec,
};
use num_rational::BigRational;
use z3::ast::{Bool, Dynamic, forall_const};
use z3::{FuncDecl, Model, SatResult};

pub struct QuantifiedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
}

impl<INNER: AbstractSolver> QuantifiedMonotoneSolver<INNER> {
    pub fn new(inner: INNER) -> Self {
        // Gets rid of the "WARNING: optimization with quantified constraints is not supported"
        z3::set_global_param("warning", "false");
        Self { inner }
    }

    pub fn as_inner(&self) -> &INNER {
        &self.inner
    }

    pub fn into_inner(self) -> INNER {
        self.inner
    }

    fn mk_monotonicity_constraint(f: &FuncDecl, i: usize, is_positive: bool) -> Bool {
        let vars: Vec<_> = (0..f.arity())
            .map(|i| Bool::new_const(format!("arg_{}", i)))
            .collect();
        let mut args = vars.clone();

        args[i] = Bool::from_bool(true);
        let f_with_true = f.apply(&make_dyn_vec(&args)).as_bool().unwrap();

        args[i] = Bool::from_bool(false);
        let f_with_false = f.apply(&make_dyn_vec(&args)).as_bool().unwrap();

        let body = if is_positive {
            f_with_false.implies(f_with_true)
        } else {
            f_with_true.implies(f_with_false)
        };

        forall_const(&make_dyn_vec(&vars), &[], &body)
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for QuantifiedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) {
        self.assert(&Self::mk_monotonicity_constraint(f, i, true))
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) {
        self.assert(&Self::mk_monotonicity_constraint(f, i, false))
    }
}

impl Default for QuantifiedMonotoneSolver<z3::Solver> {
    fn default() -> Self {
        QuantifiedMonotoneSolver {
            inner: z3::Solver::new(),
        }
    }
}

impl<INNER: AbstractSolver> AbstractSolver for QuantifiedMonotoneSolver<INNER> {
    fn assert(&mut self, formula: &Bool) {
        self.inner.assert(formula);
    }

    fn check(&self) -> SatResult {
        self.inner.check()
    }

    fn get_model(&self) -> Option<Model> {
        self.inner.get_model()
    }
}

impl<INNER: AbstractOptimizeSolver> AbstractOptimizeSolver for QuantifiedMonotoneSolver<INNER> {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
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
