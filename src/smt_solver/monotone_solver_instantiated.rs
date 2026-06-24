use crate::smt_solver::typed_ast::{AstType, TypedAst};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver,
    Monotonicity, extract_function_applications, extract_function_type_signature,
    model_eval_int_function,
};
use anyhow::anyhow;
use linked_hash_set::LinkedHashSet;
use log::{debug, info};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};
use z3::ast::{Ast, Bool, Dynamic};
use z3::{FuncDecl, Model, SatResult, Symbol};

type FunctionName = String;

pub struct InstantiatedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
    /// Indicates that the solver should add monotonicity lemmas lazily during solving.
    lazy_lemma_creation: bool,
    /// Indicate that when doing lazy lemma creation, the solver should re-initialize itself
    /// after each iteration to clean up the stale solver state.
    ///
    /// Note that in most instances, this should not be necessary and should not improve
    /// performance, but there can be edge cases where reinitialization does help.
    force_lazy_reinitialization: bool,
    /// Indicates which functions appeared in existing assertions (monotonicity must be declared
    /// before the function is first used).
    has_asserted: BTreeSet<FunctionName>,
    function_info: BTreeMap<FunctionName, FunctionMonotonicityData>,
}

/// Stores internal info about monotonicity properties related to one of the uninterpreted
/// functions.
///
/// Currently, this object is only created for functions with at least one monotonic argument,
/// meaning you can generally assume that `arguments` is not empty.
#[derive(Clone)]
struct FunctionMonotonicityData {
    name: FunctionName,
    // Type signature of the function.
    signature: (Vec<AstType>, AstType),
    // Stores function arguments that are declared as monotone.
    arguments: BTreeMap<usize, Monotonicity>,
    // Stores all unique usages of every function (should all be the same type).
    occurrences: LinkedHashSet<TypedAst>,
    // Remembers all monotonicity lemmas already asserted for a given function.
    lemmas: Vec<Bool>,
}

impl FunctionMonotonicityData {
    /// Make a lemma which states that for the two applications of this function,
    /// the argument monotonicity properties stored in this [`FunctionMonotonicityData`] must hold.
    pub fn mk_monotonicity_lemma(&self, app1: &TypedAst, app2: &TypedAst) -> Option<Bool> {
        assert!(app1.as_dyn_ref().is_app());
        assert!(app2.as_dyn_ref().is_app());
        assert_eq!(
            app1.as_dyn_ref().decl().name(),
            app2.as_dyn_ref().decl().name()
        );
        assert_eq!(app1.as_dyn_ref().decl().name(), self.name);

        let app1_args = app1.as_dyn_ref().children();
        let app2_args = app2.as_dyn_ref().children();

        let assumptions = app1_args
            .into_iter()
            .zip(app2_args)
            .zip(self.signature.0.iter())
            .enumerate()
            .filter(|(_, ((arg1, arg2), _))| *arg1 != *arg2)
            .map(|(i, ((arg1, arg2), tt))| {
                let arg1 = TypedAst::cast_dynamic(*tt, arg1);
                let arg2 = TypedAst::cast_dynamic(*tt, arg2);
                match self.arguments.get(&i) {
                    Some(Monotonicity::Positive) => arg1.le(&arg2), // arg1 <= arg2
                    Some(Monotonicity::Negative) => arg2.le(&arg1), // arg1 >= arg2
                    None => arg1.eq(&arg2),                         // arg1 == arg2
                }
                .unwrap_or_else(|_| unreachable!("`arg1` and `arg2` always have the same type"))
            })
            .collect::<Vec<_>>();

        if !assumptions.is_empty() {
            let comparison = app1.le(app2).unwrap_or_else(|_e| {
                unreachable!("`app1` and `app2` always have the same type.");
            });

            Some(Bool::and(&assumptions).implies(&comparison))
        } else {
            None
        }
    }

    /// Returns true if `left` is a "greater" input vector than `right` with respect to
    /// input monotonicity. The method also returns false if the vectors are incomparable.
    ///
    /// The method uses information about argument monotonicity stored
    /// in this [`FunctionMonotonicityData`].
    pub fn is_greater_input_vector(&self, left: &[u32], right: &[u32]) -> bool {
        for i in 0..self.signature.0.len() {
            let left_arg = left[i];
            let right_arg = right[i];
            if left_arg == right_arg {
                // Left can only be lesser based on arguments that have different values.
                continue;
            }

            match self.arguments.get(&i) {
                None => {
                    // If the input vectors differ in a non-monotonic input, they are
                    // incomparable, therefore, left is not "greater".
                    return false;
                }
                Some(Monotonicity::Positive) => {
                    // The left input needs to be higher or equal for the left
                    // input vector to be considered "greater".
                    if left_arg < right_arg {
                        return false;
                    }
                }
                Some(Monotonicity::Negative) => {
                    // Reversed: Left needs to be lower or equal for the left
                    // input vector to be considered "greater".
                    if left_arg > right_arg {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Immediately generate and assert all lemmas that are required to ensure the `new_app`
    /// function application is monotonic in terms of the existing function applications.
    pub fn eagerly_assert_lemmas(&mut self, solver: &mut impl AbstractSolver, new_app: &TypedAst) {
        // Assuming we are not in lazy mode, immediately add all monotonicity lemmas
        // for this function application.
        for other_app in self.occurrences.iter() {
            debug!(
                "Asserting: Monotonicity lemma for {} and {}.",
                new_app, other_app
            );
            if let Some(lemma) = self.mk_monotonicity_lemma(new_app, other_app) {
                solver.assert(&lemma);
                self.lemmas.push(lemma);
            }
            if let Some(lemma) = self.mk_monotonicity_lemma(other_app, new_app) {
                solver.assert(&lemma);
                self.lemmas.push(lemma);
            }
        }
    }

    /// Check usages of this function in the given `model`. If the usages are not monotonic,
    /// lazily generate the monotonicity lemmas necessary to prevent these breaking cases
    /// in future models.
    pub fn lazily_assert_lemmas(
        &mut self,
        solver: &mut impl AbstractSolver,
        model: &Model,
    ) -> usize {
        // First, build a table which holds the evaluated arguments and their output for each
        // known function application.
        let mut table: BTreeMap<u32, BTreeMap<Vec<u32>, Vec<TypedAst>>> = BTreeMap::new();

        for app in self.occurrences.iter() {
            let (args, output) = model_eval_int_function(app, model);
            let output_grouped_rows = table.entry(output).or_default();
            let row_applications = output_grouped_rows.entry(args).or_default();
            row_applications.push(app.clone());
        }

        // Second, for all inputs that generate value `H`, check all inputs that generate value
        // `L` s.t. `L < H`. Some of these input pairs could be breaking monotonicity, assuming
        // we can show that `L` is a "greater" input vector than `H`.

        let mut created_lemmas = 0;
        for (high_output, high_occurrences) in table.iter() {
            for (low_output, low_occurrences) in table.iter() {
                if low_output >= high_output {
                    // Only compare occurrences that produce `high_output` with all occurrences
                    // that produce a smaller `low_output` value.
                    continue;
                }

                for (high_row, high_applications) in high_occurrences.iter() {
                    for (low_row, low_applications) in low_occurrences.iter() {
                        // If the low input vector is greater than the high input vector,
                        // we have monotonicity violation, because input(low) >= input(high),
                        // but output(low) < output(high). We need to assert that all
                        // occurrences that resulted in these contradictory observations
                        // are handled properly.
                        if self.is_greater_input_vector(low_row, high_row) {
                            for low_app in low_applications {
                                for high_app in high_applications {
                                    let lemma =
                                        self.mk_monotonicity_lemma(high_app, low_app).expect(
                                            "Unreachable: The lemma must exist if it is violated.",
                                        );
                                    solver.assert(&lemma);
                                    self.lemmas.push(lemma);
                                    created_lemmas += 1;
                                }
                            }
                        }
                    }
                }
            }
        }

        created_lemmas
    }
}

impl<INNER: AbstractSolver> InstantiatedMonotoneSolver<INNER> {
    pub fn new(inner: INNER) -> InstantiatedMonotoneSolver<INNER> {
        InstantiatedMonotoneSolver {
            inner,
            has_asserted: BTreeSet::new(),
            lazy_lemma_creation: false,
            function_info: BTreeMap::new(),
            force_lazy_reinitialization: false,
        }
    }

    pub fn new_lazy(
        inner: INNER,
        force_reinitialization: bool,
    ) -> InstantiatedMonotoneSolver<INNER> {
        InstantiatedMonotoneSolver {
            inner,
            has_asserted: BTreeSet::new(),
            lazy_lemma_creation: true,
            function_info: BTreeMap::new(),
            force_lazy_reinitialization: force_reinitialization,
        }
    }

    pub fn count_used_lemmas(&self) -> usize {
        let mut total = 0;
        for v in self.function_info.values() {
            total += v.lemmas.len();
        }
        total
    }

    fn set_monotonicity(
        &mut self,
        f: &FuncDecl,
        i: usize,
        monotonicity: Monotonicity,
    ) -> Result<(), anyhow::Error> {
        let name = f.name();
        if self.has_asserted.contains(&name) {
            return Err(anyhow!(
                "Monotonicity constraints for `{name}` must be declared before all assertions using `{name}`."
            ));
        }

        if i >= f.arity() {
            return Err(anyhow!(
                "Argument `{i}` not valid for function with arity `{}`.",
                f.arity()
            ));
        }

        self.ensure_function_info(f)?
            .arguments
            .insert(i, monotonicity);
        Ok(())
    }

    fn ensure_function_info(
        &mut self,
        f: &FuncDecl,
    ) -> Result<&mut FunctionMonotonicityData, anyhow::Error> {
        let (domain, range) = extract_function_type_signature(f)?;

        Ok(self
            .function_info
            .entry(f.name())
            .or_insert_with_key(|name| FunctionMonotonicityData {
                name: name.clone(),
                signature: (domain, range),
                arguments: BTreeMap::new(),
                occurrences: LinkedHashSet::new(),
                lemmas: Vec::new(),
            }))
    }

    /// This method:
    ///  - In eager mode: Adds all monotonicity lemmas relevant to the given function application,
    ///    assuming these lemmas have not been already added before.
    ///  - Saves the function application for later lemma creation.
    fn handle_application_monotonicity(&mut self, app: Dynamic) {
        assert!(app.is_app());

        if let Some(info) = self.function_info.get_mut(&app.decl().name()) {
            let app = TypedAst::try_from(app).expect(
                "Correctness violation: `function_info` admits function with invalid type.",
            );

            if info.occurrences.contains(&app) {
                // Don't add new lemmas if this is a known function application.
                return;
            }

            if !self.lazy_lemma_creation {
                info.eagerly_assert_lemmas(&mut self.inner, &app);
            }

            // Save a function application for later lemma creation.
            info.occurrences.insert(app);
        }
    }

    fn handle_assert(&mut self, formula: &Bool) {
        for app in extract_function_applications(formula) {
            self.has_asserted.insert(app.decl().name());
            self.handle_application_monotonicity(app);
        }
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for InstantiatedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Positive)
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Negative)
    }

    fn is_monotone(&self, f: &FuncDecl, i: usize) -> Option<Monotonicity> {
        self.function_info
            .get(&f.name())
            .and_then(|info| info.arguments.get(&i).copied())
    }
}

impl<INNER: AbstractSolver> AbstractSolver for InstantiatedMonotoneSolver<INNER> {
    fn assert(&mut self, formula: &Bool) {
        self.inner.assert(formula);
        self.handle_assert(formula);
    }

    fn check(&mut self) -> SatResult {
        loop {
            // We need a loop because in lazy mode, the first result may not be final.

            let result = self.inner.check();
            if !self.lazy_lemma_creation || result != SatResult::Sat {
                // If the result is not SAT, the result is always final.
                // If the lazy lemma creation is turned off, the result is also always final.
                info!(
                    "Found exact solution using {} lemmas.",
                    self.count_used_lemmas()
                );
                return result;
            }

            // If the lazy lemma creation is turned on, we have to check that the resulting
            // model does not violate monotonicity, and if it does, add new lemmas to prevent it.

            let model = self
                .inner
                .get_model()
                .expect("Unreachable: Result is SAT but model does not exist.");

            let mut created_lemmas = 0usize;
            for fun_data in self.function_info.values_mut() {
                created_lemmas += fun_data.lazily_assert_lemmas(&mut self.inner, &model);
            }

            if created_lemmas == 0 {
                // All monotonicity lemmas are satisfied. We can actually report the SAT result.
                info!(
                    "Lazy monotonicity lemma creation converged with {} lemmas.",
                    self.count_used_lemmas()
                );
                return result;
            } else {
                info!(
                    "Result is spurious. Generated {created_lemmas} additional monotonicity lemmas. Total lemmas: {}.",
                    self.count_used_lemmas()
                );

                if self.force_lazy_reinitialization {
                    self.reinitialize();
                }
            }
        }
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

impl<INNER: AbstractOptimizeSolver> AbstractOptimizeSolver for InstantiatedMonotoneSolver<INNER> {
    fn assert_soft_with_class(
        &mut self,
        formula: &Bool,
        weight: BigRational,
        class: Option<Symbol>,
    ) {
        self.inner.assert_soft_with_class(formula, weight, class);
        self.handle_assert(formula);
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_lower(objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_upper(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.inner.register_model_handler(callback)
    }
}

impl<INNER: AbstractBoundedIntSolver> AbstractBoundedIntSolver
    for InstantiatedMonotoneSolver<INNER>
{
    fn declare_int(
        &mut self,
        f: &FuncDecl,
        domain: Option<(u32, u32)>,
    ) -> Result<(), anyhow::Error> {
        self.inner.declare_int(f, domain)
    }
}
