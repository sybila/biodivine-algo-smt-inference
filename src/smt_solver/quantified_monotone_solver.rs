use crate::smt_solver::typed_ast::{AstType, MapDynAst, TypedAst};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver,
    extract_function_type_signature,
};
use anyhow::anyhow;
use num_rational::BigRational;
use z3::ast::{Bool, Dynamic, forall_const};
use z3::{FuncDecl, Model, SatResult};

pub struct QuantifiedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
    optimize_boolean_quantifiers: bool,
}

impl<INNER: AbstractSolver> QuantifiedMonotoneSolver<INNER> {
    pub fn new(inner: INNER, optimize_boolean_quantifiers: bool) -> Self {
        // Gets rid of the "WARNING: optimization with quantified constraints is not supported"
        z3::set_global_param("warning", "false");
        Self {
            inner,
            optimize_boolean_quantifiers,
        }
    }

    pub fn as_inner(&self) -> &INNER {
        &self.inner
    }

    pub fn into_inner(self) -> INNER {
        self.inner
    }

    fn mk_monotonicity_constraint(
        f: &FuncDecl,
        i: usize,
        is_positive: bool,
        optimize_boolean_quantifiers: bool,
    ) -> Result<Bool, anyhow::Error> {
        let (domain, range) = extract_function_type_signature(f)?;

        if i >= domain.len() {
            return Err(anyhow!(
                "Argument `{}` not valid for function with arity `{}`.",
                i,
                f.arity()
            ));
        }

        // Quantified variables representing function arguments:
        let mut args: Vec<TypedAst> = domain
            .iter()
            .enumerate()
            .map(|(i, it)| it.new_const(format!("arg_{}", i)))
            .collect();

        if domain[i] == AstType::Bool && optimize_boolean_quantifiers {
            // If the argument is a Bool, we can build a slightly more optimized encoding:
            // Positive: `forall args: f(args[i=0]) <= f(args[i=1])`
            // Negative: `forall args: f(args[i=0]) >= f(args[i=1])`

            args[i] = TypedAst::Bool(Bool::from_bool(false));
            let f_args_0 = TypedAst::cast_dynamic(range, f.apply(&args.iter().dyn_vec()));
            args[i] = TypedAst::Bool(Bool::from_bool(true));
            let f_args_1 = TypedAst::cast_dynamic(range, f.apply(&args.iter().dyn_vec()));

            let f_args_0_le_f_args_1 = if is_positive {
                f_args_0.le(&f_args_1)?
            } else {
                f_args_1.le(&f_args_0)?
            };

            args.remove(i); // The constant value does not need to be quantified.
            return Ok(forall_const(
                &args.iter().dyn_vec(),
                &[],
                &f_args_0_le_f_args_1,
            ));
        }

        // Otherwise, for `Int` values we are building this generic formula:
        // Positive: `forall args,y: (args[i] <= y) -> (f(args) <= f(args[i=y]))`
        // Negative: `forall args,y: (args[i] <= y) -> (f(args) >= f(args[i=y]))`

        let y = domain[i].new_const("y");

        // A copy of `args` that will be used for quantification:
        let mut quantified_vars = Vec::new();
        quantified_vars.push(y.clone());
        quantified_vars.extend(args.clone());

        // args[i] <= y
        let args_i_le_y = args[i].le(&y)?;

        let f_args = TypedAst::cast_dynamic(range, f.apply(&args.iter().dyn_vec()));
        args[i] = y;
        let f_args_y = TypedAst::cast_dynamic(range, f.apply(&args.iter().dyn_vec()));

        // f(args) <= f(args[i=y]) (or swapped if not positive)
        let f_args_le_f_args_y = if is_positive {
            f_args.le(&f_args_y)?
        } else {
            f_args_y.le(&f_args)?
        };

        Ok(forall_const(
            &quantified_vars.iter().dyn_vec(),
            &[],
            &args_i_le_y.implies(&f_args_le_f_args_y),
        ))
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for QuantifiedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.assert(&Self::mk_monotonicity_constraint(
            f,
            i,
            true,
            self.optimize_boolean_quantifiers,
        )?);
        Ok(())
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.assert(&Self::mk_monotonicity_constraint(
            f,
            i,
            false,
            self.optimize_boolean_quantifiers,
        )?);
        Ok(())
    }
}

impl Default for QuantifiedMonotoneSolver<z3::Solver> {
    fn default() -> Self {
        QuantifiedMonotoneSolver {
            inner: z3::Solver::new(),
            optimize_boolean_quantifiers: true,
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

impl<INNER: AbstractBoundedIntSolver> AbstractBoundedIntSolver for QuantifiedMonotoneSolver<INNER> {
    fn declare_int(
        &mut self,
        f: &FuncDecl,
        domain: Option<(u32, u32)>,
    ) -> Result<(), anyhow::Error> {
        self.inner.declare_int(f, domain)
    }
}
