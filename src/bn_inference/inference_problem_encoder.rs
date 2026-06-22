use crate::bn_inference::InferenceProblem;
use crate::bn_inference::UpdateFunctionDefinition;
use crate::bn_inference::constraints::ValueComparison;
use crate::smt_solver::typed_ast::{MapDynAst, TypedAst};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractSolver, IntFunction, model_eval_int,
};
use anyhow::anyhow;
use biodivine_lib_param_bn::{BooleanNetwork, Regulation, RegulatoryGraph, VariableId};
use log::info;
use std::collections::{BTreeMap, HashMap};
use z3::ast::{Bool, Dynamic, Int};
use z3::{AstKind, Model};

/// A static collection of SMT formulas and declarations that are collectively used to
/// actually encode an [`InferenceProblem`] into a solver query. Subsequently, this object
/// is also used to translate the elements of the resulting model back into an interpretable
/// result.
pub struct InferenceProblemEncoder<SOLVER> {
    /// Referencing the associated inference problem.
    pub problem: InferenceProblem<SOLVER>,
    /// Update function definitions of model variables.
    update_functions: BTreeMap<VariableId, UpdateFunctionDefinition>,
    /// Assigns each declared state the literals necessary to construct the state.
    state_atoms: BTreeMap<String, BTreeMap<VariableId, TypedAst>>,
}

impl<SOLVER: AbstractBoundedIntSolver + 'static> InferenceProblemEncoder<SOLVER> {
    /// Build a new encoder for a given [`InferenceProblem`] while also adding all
    /// required assertions to the given solver.
    ///
    /// Once created, the encoder (and the underlying problem) should effectively remain immutable
    /// to guarantee that the problem and its encoding stay in sync.
    ///
    /// If `propagate_observations` is set to `true`, the encoder will try to inline known
    /// values of atoms that are fully determined by observations.
    pub fn new(
        problem: InferenceProblem<SOLVER>,
        solver: &mut SOLVER,
        propagate_observations: bool,
    ) -> Result<Self, anyhow::Error> {
        let mut encoder = InferenceProblemEncoder {
            update_functions: problem
                .variables()
                .map(|var| {
                    let def = UpdateFunctionDefinition::from_variable_data(&problem, var);
                    (var, def)
                })
                .collect(),
            state_atoms: problem
                .states()
                .map(|state| {
                    let atoms = Self::mk_state_atoms(&problem, state.as_str());
                    (state, atoms)
                })
                .collect(),
            problem,
        };

        if propagate_observations {
            // For each state, find observations that reason about this state. In these observations,
            // detect exact observations and use those to replace current free atoms with known
            // state values.
            for constraint in encoder.problem.constraints() {
                let Some(constraint) = constraint.downcast_ref::<ValueComparison>() else {
                    continue;
                };
                let Some((state, var, value)) = constraint.as_assignment() else {
                    continue;
                };

                let atoms = encoder
                    .state_atoms
                    .get_mut(&state)
                    .expect("Unreachable: State must exist.");
                let val_const = encoder.problem[var].ast_type().new_value(value);
                atoms.insert(var, val_const);
                info!("Propagated value of `{var:?}` in state `{state}` to `{value}.");
            }
        }

        // Declare domains for `Int` update functions as long as they are uninterpreted:
        for (var, func) in &encoder.update_functions {
            let var_data = &encoder.problem[*var];
            if var_data.is_int()
                && let Some(declaration) = func.as_uninterpreted()
            {
                solver.declare_int(declaration, Some(var_data.domain))?;
            }
        }

        // Declare domains for known `Int` atoms:
        for atoms in encoder.state_atoms.values() {
            for (var, atom) in atoms {
                let var_data = &encoder.problem[*var];
                if var_data.is_int() {
                    if atom.as_dyn_ref().kind() == AstKind::Numeral {
                        // If observation propagation is enabled, some of these atoms could
                        // be constants, in which case we don't want to assert their bounds.
                        continue;
                    }

                    let func = atom.as_dyn_ref().decl();
                    solver.declare_int(&func, Some(var_data.domain))?;
                }
            }
        }

        for constraint in encoder.problem.constraints() {
            constraint.assert_self(&encoder, solver)?;
        }

        Ok(encoder)
    }
}

impl<SOLVER: AbstractSolver + 'static> InferenceProblemEncoder<SOLVER> {
    /// A static helper which creates one free atom for each variable value in a specific state.
    ///
    /// Note that the naming is deterministic, i.e., calling this method multiple times
    /// with the same `problem` and `variable` produces the same set of atoms.
    fn mk_state_atoms(
        problem: &InferenceProblem<SOLVER>,
        state: &str,
    ) -> BTreeMap<VariableId, TypedAst> {
        problem
            .variables()
            .map(|var| {
                let name = format!("state_{}_{}", state, var.to_index());
                (var, problem[var].new_const(name.as_str()))
            })
            .collect()
    }

    /// Retrieve the update function definition of the given variable.
    ///
    /// # Panics
    ///
    /// Fails if the variable is not valid in this [`InferenceProblemEncoder`].
    pub fn update_function(&self, variable: VariableId) -> &UpdateFunctionDefinition {
        self.update_functions
            .get(&variable)
            .unwrap_or_else(|| panic!("Variable `{variable:?}` not found."))
    }

    /// Retrieve the atom encoding the value of a particular variable in the given `state`.
    pub fn state_atom(&self, state: &str, variable: VariableId) -> &TypedAst {
        let atoms = self
            .state_atoms
            .get(state)
            .unwrap_or_else(|| panic!("Unknown state `{state}`."));
        atoms
            .get(&variable)
            .unwrap_or_else(|| panic!("Unknown variable `{variable:?}`."))
    }

    /// Create a function application that calls the update function of the given variable
    /// on the provided arguments. The result can be either a function application if the
    /// function is uninterpreted, or an explicit expression if the function is fully defined.
    ///
    /// # Panics
    ///
    /// If the number of arguments or argument types do not match what is expected for
    /// the update function, or if the given variable does not exist at all.
    pub fn mk_update_function_call(&self, variable: VariableId, args: &[&TypedAst]) -> TypedAst {
        // Check that the variable exists and has a function.
        let function = self.update_function(variable);

        // Check that the type is correct.
        let variable = &self.problem[variable];
        assert_eq!(
            variable.regulators.len(),
            args.len(),
            "Expected {} arguments, but got {}.",
            args.len(),
            variable.regulators.len()
        );
        for (arg, var) in args.iter().zip(variable.regulators.iter()) {
            assert_eq!(
                arg.sort_kind(),
                self.problem[*var].sort_kind(),
                "Expected variable {var:?} to have type `{:?}`.",
                arg.sort_kind()
            );
        }

        // Make the function call and wrap it into `TypedAst`.
        match function {
            UpdateFunctionDefinition::Uninterpreted(declaration) => TypedAst::cast_dynamic(
                variable.ast_type(),
                declaration.apply(&args.iter().dyn_vec()),
            ),
            UpdateFunctionDefinition::FullySpecified(expression) => {
                let substitutions = Iterator::zip(variable.regulators.iter(), args.iter())
                    .map(|(var, ast)| {
                        let ast: Bool = match ast {
                            // For `Int` variables, require them to be non-zero:
                            TypedAst::Int(value) => value.ge(Int::from_u64(1)),
                            // For `Bool` variables, just use them directly:
                            TypedAst::Bool(value) => value.clone(),
                        };
                        (*var, ast)
                    })
                    .collect::<HashMap<_, _>>();
                TypedAst::from_fn_update(expression, &substitutions)
            }
        }
    }

    /// Extract the valuation of variables in the given state according to the provided Z3 model.
    ///
    /// # Panics
    ///
    /// The state must exist in this [`InferenceProblemEncoder`].
    pub fn decode_state(&self, state: &str, model: &Model) -> BTreeMap<VariableId, u32> {
        let atoms = self
            .state_atoms
            .get(state)
            .unwrap_or_else(|| panic!("Unknown state `{state}`."));
        atoms
            .iter()
            .map(|(var, ast)| {
                let eval = model_eval_int(&Dynamic::from_ast(ast.as_dyn_ref()), model);
                (*var, eval)
            })
            .collect()
    }
}

impl<SOLVER: AbstractMonotoneSolver + 'static> InferenceProblemEncoder<SOLVER> {
    /// Extract the update function inferred for the given [`VariableId`]. This is similar
    /// to using [`AbstractMonotoneSolver::extract_monotone_function_points`],
    /// but it also clamps the arguments of the function to their respective intervals,
    /// eliminating unnecessary atoms. Furthermore, it should also support fully specified
    /// update functions.
    pub fn decode_update_function(
        &self,
        variable: VariableId,
        solver: &SOLVER,
        model: &Model,
    ) -> Result<IntFunction, anyhow::Error> {
        let mut function = match self.update_function(variable) {
            UpdateFunctionDefinition::Uninterpreted(declaration) => {
                solver.extract_monotone_function_points(declaration, model)?
            }
            UpdateFunctionDefinition::FullySpecified(expression) => {
                let var_data = &self.problem[variable];
                let arg_signatures = var_data
                    .regulators_iter()
                    .map(|var| (var, self.problem[var].ast_type()))
                    .collect::<Vec<_>>();
                IntFunction::from_update_function(expression, &arg_signatures)
            }
        };

        for (i, reg) in self.problem[variable].regulators.iter().enumerate() {
            function.clamp_argument(i, self.problem[*reg].domain);
        }
        function.drop_default_output_level();
        function.remove_duplicates();
        Ok(function)
    }

    pub fn decode_boolean_network(
        &self,
        solver: &SOLVER,
        model: &Model,
        infer_graph: bool,
    ) -> Result<BooleanNetwork, anyhow::Error> {
        let mut names = Vec::new();
        for var in self.problem.variables() {
            names.push(self.problem[var].name.clone());
        }

        let mut rg = RegulatoryGraph::new(names);
        for var in self.problem.variables() {
            let var_data = &self.problem[var];
            for reg in var_data.regulators.iter() {
                // Don't include essential/monotonic constraints,
                // we'll infer the graph automatically.
                rg.add_raw_regulation(Regulation {
                    regulator: *reg,
                    target: var,
                    observable: false,
                    monotonicity: None,
                })
                .map_err(|e| anyhow!(e))?;
            }
        }

        let mut bn = BooleanNetwork::new(rg);
        for var in self.problem.variables() {
            let var_data = &self.problem[var];
            let function = self.decode_update_function(var, solver, model)?;
            let regulators = Vec::from_iter(var_data.regulators.iter().cloned());
            let function = function.as_update_function(&regulators)?;
            bn.set_update_function(var, Some(function))
                .map_err(|e| anyhow!(e))?;
        }

        if infer_graph {
            bn = bn.infer_valid_graph().map_err(|e| anyhow!(e))?;
        }
        Ok(bn)
    }
}
