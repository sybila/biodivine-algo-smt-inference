use crate::smt_solver::typed_ast::{AstType, MapDynAst, TypedAst};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver,
    Monotonicity, extract_function_applications, extract_function_type_signature,
};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};
use z3::ast::{Ast, Bool, Dynamic, forall_const};
use z3::{FuncDecl, Model, SatResult, Symbol};

pub struct QuantifiedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
    /// When quantification over Boolean input is detected, one quantified variable is eliminated
    /// by explicitly instantiating the two possible values.
    optimize_boolean_quantifiers: bool,
    /// When not `None`, the solver will emit a single quantified assertion for each function
    /// instead of emitting a separate assertion for individual monotonicity constraints.
    /// The solver uses this set to identify functions that already have their monotonicity
    /// asserted and thus do not need new assertions.
    merged_monotonicity_constraints: Option<BTreeSet<String>>,
    /// Indicates which functions appeared in existing assertions (monotonicity must be declared
    /// before the function is first used). We are saving the whole declaration, not just the name,
    /// because we have to take the declaration from somewhere before creating the
    /// merged constraint.
    has_asserted: BTreeMap<String, FuncDecl>,
    function_info: BTreeMap<String, BTreeMap<usize, Monotonicity>>,
}

impl<INNER: AbstractSolver> QuantifiedMonotoneSolver<INNER> {
    pub fn new(inner: INNER, optimize_boolean_quantifiers: bool) -> Self {
        // Gets rid of the "WARNING: optimization with quantified constraints is not supported"
        z3::set_global_param("warning", "false");
        Self {
            inner,
            optimize_boolean_quantifiers,
            merged_monotonicity_constraints: None,
            has_asserted: BTreeMap::new(),
            function_info: BTreeMap::new(),
        }
    }

    pub fn new_merge(inner: INNER, optimize_boolean_quantifiers: bool) -> Self {
        // Gets rid of the "WARNING: optimization with quantified constraints is not supported"
        z3::set_global_param("warning", "false");
        Self {
            inner,
            optimize_boolean_quantifiers,
            merged_monotonicity_constraints: Some(BTreeSet::new()),
            has_asserted: BTreeMap::new(),
            function_info: BTreeMap::new(),
        }
    }

    pub fn should_merge_monotonicity_constraints(&self) -> bool {
        self.merged_monotonicity_constraints.is_some()
    }

    pub fn as_inner(&self) -> &INNER {
        &self.inner
    }

    pub fn into_inner(self) -> INNER {
        self.inner
    }

    /// Create a quantified monotonicity constraint for a single specific argument of
    /// an uninterpreted function (as opposed to creating one constraint that aggregates
    /// all monotonicity info).
    fn mk_single_monotonicity_constraint(
        &self,
        f: &FuncDecl,
        i: usize,
        is_positive: bool,
    ) -> Result<Bool, anyhow::Error> {
        let (domain, range) = extract_function_type_signature(f)?;

        if i >= domain.len() {
            anyhow::bail!(
                "Argument `{i}` not valid for function with arity `{}`.",
                f.arity()
            );
        }

        // Quantified variables representing function arguments:
        let mut args: Vec<TypedAst> = domain
            .iter()
            .enumerate()
            .map(|(i, it)| it.new_const(format!("arg_{}", i)))
            .collect();

        if domain[i] == AstType::Bool && self.optimize_boolean_quantifiers {
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

    fn mk_unified_monotonicity_constraint(
        &self,
        f: &FuncDecl,
        monotonicity: &BTreeMap<usize, Monotonicity>,
    ) -> Result<Bool, anyhow::Error> {
        let (domain, range) = extract_function_type_signature(f)?;

        // Two sets of quantified variables representing function arguments:
        let args: Vec<(TypedAst, TypedAst)> = domain
            .iter()
            .enumerate()
            .map(|(i, it)| {
                (
                    it.new_const(format!("arg_x_{}", i)),
                    it.new_const(format!("arg_y_{}", i)),
                )
            })
            .collect();

        // Require that x <= y (for positively monotone), x >= y (for negatively monotone),
        // and x == y (for unrestricted).
        let assumptions = args
            .iter()
            .enumerate()
            .map(|(i, (x, y))| match monotonicity.get(&i) {
                None => x.eq(y),
                Some(Monotonicity::Positive) => x.le(y),
                Some(Monotonicity::Negative) => y.le(x),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let assumption = Bool::and(&assumptions);

        let x_args = args.iter().map(|(x, _)| x.as_dyn_ref()).collect::<Vec<_>>();
        let f_x = TypedAst::cast_dynamic(range, f.apply(&x_args));

        let y_args = args.iter().map(|(_, y)| y.as_dyn_ref()).collect::<Vec<_>>();
        let f_y = TypedAst::cast_dynamic(range, f.apply(&y_args));

        let mut quantified_vars = Vec::new();
        quantified_vars.extend(x_args);
        quantified_vars.extend(y_args);

        Ok(forall_const(
            &quantified_vars,
            &[],
            &assumption.implies(&f_x.le(&f_y)?),
        ))
    }

    fn set_monotonicity(
        &mut self,
        f: &FuncDecl,
        i: usize,
        monotonicity: Monotonicity,
    ) -> Result<(), anyhow::Error> {
        let name = f.name();
        if self.has_asserted.contains_key(name.as_str()) {
            anyhow::bail!(
                "Monotonicity of `{name}` must be declared before all assertions using `{name}`."
            );
        }

        if i >= f.arity() {
            anyhow::bail!(
                "Argument `{i}` not valid for function with arity `{}`.",
                f.arity()
            );
        }

        self.function_info
            .entry(f.name())
            .or_default()
            .insert(i, monotonicity);

        if !self.should_merge_monotonicity_constraints() {
            // If constraint merging is turned off, immediately assert the monotonicity
            // for this specific function input:
            let is_positive = monotonicity == Monotonicity::Positive;
            self.assert(&self.mk_single_monotonicity_constraint(f, i, is_positive)?);
        }

        Ok(())
    }

    /// Create unified monotonicity assertions for functions that have some declared monotonicity
    /// but do not have a corresponding assertion yet.
    fn add_merged_monotonicity_assertions(&mut self) {
        let Some(already_asserted) = self.merged_monotonicity_constraints.as_ref() else {
            // If constraint merging is turned off, the method silently returns.
            return;
        };

        // Functions that don't appear in any assertions are ignored.

        let mut handled = Vec::new();
        for (fn_name, declaration) in &self.has_asserted {
            if already_asserted.contains(fn_name) {
                // This function was already handled in previous checks.
                continue;
            }

            // After this iteration, the function will be considered as asserted and will not be
            // considered again.
            handled.push(fn_name.clone());

            let Some(monotonicity) = self.function_info.get(fn_name) else {
                // If the function has no monotonicity constraints, skip it and never test it again.
                continue;
            };

            self.inner.assert(
                &self
                    .mk_unified_monotonicity_constraint(declaration, monotonicity)
                    .expect("Correctness violation: Cannot create monotonicity constraint."),
            );
        }

        // Save all handled functions to prevent repeated asserts.
        if let Some(asserted) = self.merged_monotonicity_constraints.as_mut() {
            asserted.extend(handled);
        }
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for QuantifiedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Positive)
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Negative)
    }

    fn is_monotone(&self, f: &FuncDecl, i: usize) -> Option<Monotonicity> {
        self.function_info
            .get(&f.name())
            .and_then(|info| info.get(&i).copied())
    }
}

impl Default for QuantifiedMonotoneSolver<z3::Solver> {
    fn default() -> Self {
        QuantifiedMonotoneSolver {
            inner: z3::Solver::new(),
            optimize_boolean_quantifiers: true,
            merged_monotonicity_constraints: None,
            function_info: BTreeMap::new(),
            has_asserted: BTreeMap::new(),
        }
    }
}

impl<INNER: AbstractSolver> AbstractSolver for QuantifiedMonotoneSolver<INNER> {
    fn assert(&mut self, formula: &Bool) {
        self.inner.assert(formula);

        // Remember functions that already appeared in an assertion:
        for app in extract_function_applications(formula) {
            let decl = app.decl();
            self.has_asserted.insert(decl.name(), decl);
        }
    }

    fn check(&mut self) -> SatResult {
        self.add_merged_monotonicity_assertions();
        self.inner.check()
    }

    fn get_model(&self) -> Option<Model> {
        self.inner.get_model()
    }

    fn get_assertions(&self) -> Vec<Bool> {
        self.inner.get_assertions()
    }

    fn reinitialize(&mut self) {
        self.inner.reinitialize();
    }
}

impl<INNER: AbstractOptimizeSolver> AbstractOptimizeSolver for QuantifiedMonotoneSolver<INNER> {
    fn assert_soft_with_class(
        &mut self,
        formula: &Bool,
        weight: BigRational,
        class: Option<Symbol>,
    ) {
        self.inner.assert_soft_with_class(formula, weight, class);

        // Remember functions that already appeared in an assertion:
        for app in extract_function_applications(formula) {
            let decl = app.decl();
            self.has_asserted.insert(decl.name(), decl);
        }
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
