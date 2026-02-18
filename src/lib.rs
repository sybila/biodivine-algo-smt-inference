use crate::expression_generators::fn_update_to_smt;
use biodivine_lib_bdd::{Bdd, BddVariableSet, ValuationsOfClauseIterator};
use biodivine_lib_param_bn::Monotonicity::Activation;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ParameterId, VariableId};
use std::collections::{BTreeMap, BTreeSet};
use z3::ast::{Ast, Bool};
use z3::{FuncDecl, Model, Sort};

/// A data structure which defines one state that is supposed to exist in a BN.
mod smt_state;
pub use smt_state::SmtState;

mod monotone_smt;
pub use monotone_smt::{
    InstantiationMonotoneSMTSolver, LazyInstantiationMonotoneSMTSolver, MonotoneSMTSolver,
    QuantifiedMonotoneSMTSolver,
};

/// Utility methods for generating logical expressions for the SMT solver.
mod expression_generators;

/// A data structure which defines the observed properties of a single BN state.
mod state_specification;
pub use state_specification::StateSpecification;

/// Data structures to load and process datasets of observations.
mod observations;
pub use observations::{Dataset, Observation};

/// Method for naive inference with imprecise fixed-point specification.
mod naive_inference;
pub use naive_inference::{loosen_specification, run_naive_inference};

/// Blocking clause strategies for iterating over multiple unique solutions.
pub mod blocking;
pub use blocking::BlockingStrategy;

/// Data structures for simplified DNF clause representation and DNF generating.
mod dnf;
pub use dnf::{DNF, DNFClause, LiteralValue};

/// A module for collectively storing non-trivial tests, because we will probably need
/// quite a few of them (simpler unit tests can still go into the modules of the tested code)
#[cfg(test)]
mod tests;

/// Inference problem defines constraints on Boolean network behavior that can be converted
/// into an SMT query and addressed by a solver (the result being an assignment of the
/// uninterpreted functions for which the network satisfies all requirements).
pub struct InferenceProblem {
    network: BooleanNetwork, // Includes essentiality and monotonicity requirements.
    uninterpreted_symbols: BTreeMap<ParameterId, FuncDecl>,
    state_declarations: BTreeMap<String, SmtState>,
    state_specification: BTreeMap<String, StateSpecification>,
    fixed_points: BTreeSet<String>,
}

pub enum EncodingMode {
    Quantified,
    Instantiation,
    LazyInstantiation,
}

impl InferenceProblem {
    /// Create a new inference problem for a partially specified [`BooleanNetwork`].
    ///
    /// # Panics
    ///
    /// The network can only contain explicit uninterpreted functions.
    /// Use [`BooleanNetwork::name_implicit_parameters`] to assign default names to
    /// any "anonymous" update functions.
    pub fn new(network: BooleanNetwork) -> Self {
        // Network can't have "anonymous" uninterpreted functions. You can use
        // [`BooleanNetwork::name_implicit_parameters`] to assign default names
        // to all "anonymous" functions.
        assert_eq!(network.num_implicit_parameters(), 0);

        let bool_sort = Sort::bool();

        let uninterpreted_symbols = network
            .parameters()
            .map(|p| {
                let param = &network[p];
                let arity = usize::try_from(param.get_arity()).unwrap();
                let name = param.get_name().to_string();
                let args = vec![&bool_sort; arity];
                (p, FuncDecl::new(name, &args, &bool_sort))
            })
            .collect::<BTreeMap<_, _>>();

        Self {
            network,
            uninterpreted_symbols,
            state_declarations: BTreeMap::default(),
            state_specification: BTreeMap::default(),
            fixed_points: BTreeSet::default(),
        }
    }

    /// Make a new named [`SmtState`] valid within this [`InferenceProblem`].
    ///
    /// # Panics
    ///
    /// Method fails if a state with the same name already exists in this problem.
    pub fn make_state<S: Into<String>>(&mut self, name: S) -> SmtState {
        let name: String = name.into();
        assert!(!self.state_declarations.contains_key(&name));
        let state = SmtState::new(name.as_str(), &self.network);
        self.state_declarations.insert(name.clone(), state.clone());
        state
    }

    /// Retrieve a reference to one of the name [`SmtState`] instances currently tracked
    /// by this [`InferenceProblem`].
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    ///
    pub fn get_state<S: Into<String>>(&self, name: S) -> &SmtState {
        self.state_declarations.get(&name.into()).unwrap()
    }

    /// Get a reference to the underlying Boolean network.
    pub fn get_network(&self) -> &BooleanNetwork {
        &self.network
    }

    /// Get a reference to the map of state declarations (SMT states).
    pub fn get_state_declarations(&self) -> &BTreeMap<String, SmtState> {
        &self.state_declarations
    }

    /// Get a reference to the map of state specifications (required and optional
    /// constraints from observations).
    pub fn get_state_specification(&self) -> &BTreeMap<String, StateSpecification> {
        &self.state_specification
    }

    /// Get a reference to the map of function symbols.
    pub fn get_uninterpreted_symbols(&self) -> &BTreeMap<ParameterId, z3::FuncDecl> {
        &self.uninterpreted_symbols
    }

    /// Retrieve the internally stored [`FnUpdate`] for the given [`VariableId`], using
    /// the assumption that the network has no anonymous parameters, meaning the update function
    /// cannot be `None`.
    fn get_update_function(&self, bn_var: VariableId) -> &FnUpdate {
        self.network.get_update_function(bn_var).as_ref().unwrap()
    }

    /// Assert that the state referenced by the given `name` is a network fixed-point.
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    pub fn assert_fixed_point<S: Into<String>>(&mut self, name: S) {
        let name: String = name.into();
        assert!(self.state_declarations.contains_key(&name));
        self.fixed_points.insert(name);
    }

    /// Extract a BDD representation of the uninterpreted function symbol from a model.
    ///
    /// Currently, this requires the full enumeration of the function table. In the future,
    /// we probably want to provide an option to extract an expression string, but also to
    /// extract a BDD while avoiding the full enumeration. However, Z3 API makes it quite
    /// hard to extract an expression in a way that is useful to us. We can (mostly) only
    /// extract SMT-LIB expression strings that we would have to parse, and furthermore, they
    /// are generally not deterministic (i.e. we can get different strings representing the
    /// same function on different OS-es or Z3 versions).
    ///
    /// # Panics
    ///
    /// Method fails if the given `parameter` is not valid in the network of this inference problem,
    /// or if it is not present in the given `model`.
    pub fn extract_uninterpreted_symbol(
        &self,
        model: &Model,
        parameter_id: ParameterId,
    ) -> (BddVariableSet, Bdd) {
        let parameter = self.network.get_parameter(parameter_id);
        let declaration = self.uninterpreted_symbols.get(&parameter_id).unwrap();

        // Build BDD context:
        let arity = u16::try_from(parameter.get_arity()).unwrap();
        let bdd_ctx = BddVariableSet::new_anonymous(arity);

        // Build an exhaustive DNF representation of the whole function:
        let mut dnf = Vec::new();
        for clause in ValuationsOfClauseIterator::new_unconstrained(arity) {
            let smt_clause: Vec<Bool> = clause
                .clone()
                .into_vector()
                .into_iter()
                .map(Bool::from_bool)
                .collect();
            let smt_refs: Vec<&dyn Ast> = smt_clause.iter().map(|it| it as &dyn Ast).collect();
            let application = declaration.apply(&smt_refs);
            let result = model.eval(&application, true).unwrap();
            let result = result.as_bool().unwrap().as_bool().unwrap();
            if result {
                dnf.push(clause.to_partial_valuation());
            }
        }

        // And convert it into a BDD:
        let bdd = bdd_ctx.mk_dnf(&dnf);
        (bdd_ctx, bdd)
    }

    /// Extract a BooleanNetwork instance from a model by collecting interpretations of
    /// all uninterpreted functions.
    ///
    /// WARNING: This simplified approach only works if each variable's update function
    /// consists of a single uninterpreted fn applied to the variable's regulators.
    ///
    /// See [Self::extract_uninterpreted_symbol] for details on how function symbols are
    /// extracted from the model. This wrapper only aggregates the functions and renames
    /// the arguments to match BN variables.
    ///
    /// # Panics
    ///
    /// Method fails if the original PSBN had update expressions that are not a single
    /// uninterpreted function applied to the variable's regulators.
    pub fn extract_bn_instance_simplified(&self, model: &Model) -> BooleanNetwork {
        let psbn = self.get_network();
        let mut bn_instance = psbn.clone();
        for variable in psbn.variables() {
            let update_fn = psbn.get_update_function(variable).clone().unwrap();
            if let FnUpdate::Param(param_id, args) = update_fn {
                let (bdd_ctx, fn_bdd) = self.extract_uninterpreted_symbol(model, param_id);
                let bdd_string = fn_bdd.to_boolean_expression(&bdd_ctx).to_string();

                // We need to substitute variable names in the BDD expression string (x_0, x_1,..)
                // with the actual function arguments
                let update = substitute_fn_args(&bdd_string, args, psbn);
                bn_instance
                    .set_update_function(variable, Some(update))
                    .unwrap();
            } else {
                panic!("Unexpected update fn format.");
            }
        }
        bn_instance
    }

    /// Assert that the state referenced by the given `name` must follow the specification
    /// of the given `observation`.
    ///
    /// Note that while the state *must* follow the `observation` specification, the specification
    /// can contain "may" requirements that do not need to be satisfied by every valid model.
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    pub fn assert_state_observation<S: Into<String>>(
        &mut self,
        name: S,
        observation: &StateSpecification,
    ) {
        let name: String = name.into();
        assert!(self.state_declarations.contains_key(&name));
        self.state_specification
            .insert(name.clone(), observation.clone());
    }

    /// Build a [`z3::Optimize`] solver instance that implements all prescribed constraints.
    pub fn build_solver(&self, encoding: EncodingMode) -> Box<dyn MonotoneSMTSolver> {
        let mut solver: Box<dyn MonotoneSMTSolver> = match encoding {
            EncodingMode::Quantified => Box::new(QuantifiedMonotoneSMTSolver::new()),
            EncodingMode::Instantiation => Box::new(InstantiationMonotoneSMTSolver::new()),
            EncodingMode::LazyInstantiation => Box::new(LazyInstantiationMonotoneSMTSolver::new()),
        };

        // let mut solver = QuantifiedMonotoneSMTSolver::new();

        // First, declare all monotonicity constraints
        for reg in self.network.as_graph().regulations() {
            if let Some(m) = reg.monotonicity {
                let update = self.get_update_function(reg.target);

                // Uncomment to ignore monotonicities for fully defined functions
                /*
                if update.collect_parameters().is_empty() {
                    continue;
                }
                */

                let (fun_id, index) = match update {
                    FnUpdate::Param(id, params) => (
                        id,
                        params
                            .iter()
                            .position(|p| match p {
                                FnUpdate::Var(v) => *v == reg.regulator,
                                _ => false,
                            })
                            .expect(
                                "Monotonicity constraints are allowed only for function arguments.",
                            ),
                    ),
                    _ => panic!("Only function monotonicity constraints are supported."),
                };
                let fun = &self
                    .uninterpreted_symbols
                    .get(fun_id)
                    .expect("Invalid parameter id.");
                if m == Activation {
                    solver.set_monotone(fun, index);
                } else {
                    solver.set_antimonotone(fun, index);
                }
            }
        }

        // Assert that all state specifications are satisfied:
        for (name, specification) in &self.state_specification {
            let state = self.get_state(name);
            for (bn_var, value) in specification.make_required_assertion_map() {
                let smt_var = state.get_smt_var(bn_var);
                let assertion = if value { smt_var } else { smt_var.not() };
                solver.assert(&assertion);
            }

            for (bn_var, (value, confidence)) in specification.make_optional_assertion_map() {
                let smt_var = state.get_smt_var(bn_var);
                let assertion = if value { smt_var } else { smt_var.not() };
                solver.assert_soft(&assertion, confidence);
            }
        }

        // Assert that essential regulations have their respective properties:
        for reg in self.network.as_graph().regulations() {
            let update = self.get_update_function(reg.target);

            // Technically, both of these declare one extra SMT variable that is not used/needed,
            // but that should not be a big performance issue.

            if reg.observable {
                // Declare a new state `O` for which it holds `update(O[r=0]) != update(O[r=1])`.
                let essential_name =
                    format!("o_{}_{}", reg.regulator.to_index(), reg.target.to_index());
                let smt_state = SmtState::new(essential_name.as_str(), &self.network);
                let mut map = smt_state.make_smt_var_map();
                map.insert(reg.regulator, Bool::from_bool(true));
                let fn_update_reg_true =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);
                map.insert(reg.regulator, Bool::from_bool(false));
                let fn_update_reg_false =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);
                solver.assert(&fn_update_reg_true.iff(fn_update_reg_false).not());
            }
        }

        // Finally, assert that every state that should be a fixed-point is a fixed-point:
        for name in &self.fixed_points {
            let state = self.get_state(name);
            let state_var_map = state.make_smt_var_map();
            for (bn_var, smt_var) in &state_var_map {
                let update = self.get_update_function(*bn_var);
                let smt_update =
                    fn_update_to_smt(update, &state_var_map, &self.uninterpreted_symbols);
                solver.assert(&smt_var.iff(smt_update));
            }
        }

        solver
    }

    /// Iterate over satisfying solutions using the provided blocking strategy.
    /// If a limit `max_solutions` is provided, only the given number of solutions will
    /// be enumerated (note that at least one solution is always checked).
    ///
    /// This method builds a solver, checks for satisfiability, and uses the provided strategy
    /// to generate blocking clauses to exclude each found solution from subsequent checks.
    /// The `strategy` determines how to block each found model, see [`BlockingStrategy`].
    ///
    /// For now, we use a `callback` function to process each solution as we go. This can
    /// be used for on-the-fly logging or to stop computation when some condition is met.
    /// We allow the callback to return error and finish the computation from the outside
    /// for convenience. It is recommended to use `max_solutions` for solution limit though.
    pub fn get_solutions<F>(
        &self,
        encoding: EncodingMode,
        strategy: &BlockingStrategy,
        max_solutions: Option<usize>,
        mut callback: F,
    ) -> Result<Vec<z3::Model>, String>
    where
        F: FnMut(&z3::Model) -> Result<(), String>,
    {
        let mut solver = self.build_solver(encoding);
        let mut collected_models = Vec::new();

        loop {
            // Check for satisfiability and stop if not sat
            if solver.check() != z3::SatResult::Sat {
                break;
            }

            // The model will be pushed to `collected_models` at the end of the
            // iteration to avoid passing the reference there and back
            let model = solver
                .get_model()
                .ok_or("Failed to get model from solver")?;
            callback(&model)?;

            // If a solution limit is specified and reached, we immediately
            // break before generating the blocking clause (since that can be
            // resource demanding)
            if let Some(max) = max_solutions
                && collected_models.len() + 1 >= max
            {
                break;
            }

            // Generate and assert a blocking clause
            match strategy.generate_blocker(&model, self) {
                Ok(blocker) => {
                    solver.assert(&blocker);
                }
                Err(e) => {
                    // If we can't generate a blocker, stop with an err message
                    return Err(format!("Failed to generate blocker: {}", e));
                }
            }

            collected_models.push(model);
        }

        Ok(collected_models)
    }
}

/// Given a general expression of a previously unintepreted function, substitute all formal
/// args (x_0, x_1, ..) with the actual arguments that the function is applied to (in the
/// BN's update).
///
/// Return a new FnUpdate instance for the expression, with substituted variable names.
pub fn substitute_fn_args(
    expression: &str,
    applied_args: Vec<FnUpdate>,
    psbn: &BooleanNetwork,
) -> FnUpdate {
    // Compute rename mapping between formal and actual arguments
    let mut renaming = BTreeMap::new();
    for (i, arg) in applied_args.iter().enumerate() {
        assert!(matches!(arg, FnUpdate::Var(_)));
        renaming.insert(format!("x_{}", i), format!("({})", arg.to_string(psbn)));
    }

    // Sort by len, since this is just string pattern matching substitution
    let mut keys: Vec<_> = renaming.keys().cloned().collect();
    keys.sort_by_key(|k| std::cmp::Reverse(k.len()));
    let mut modified_expression = expression.to_string();
    for key in keys {
        modified_expression = modified_expression.replace(&key, &renaming[&key]);
    }

    FnUpdate::try_from_str(&modified_expression, psbn).unwrap()
}
