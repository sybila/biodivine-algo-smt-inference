use crate::bn_inference::constraints::{
    ConstraintStrings, RegulatorIsEssential, RegulatorIsMonotone, SoftConstraint, StateComparison,
    StateIsFixedPoint, ValueComparison,
};
use crate::bn_inference::{DynInferenceConstraint, InferenceConstraint};
use crate::smt_solver::typed_ast::{AstType, TypedAst};
use crate::smt_solver::{
    AbstractMonotoneBoundedIntOptimizeSolver, AbstractMonotoneBoundedIntSolver,
};
use anyhow::anyhow;
use biodivine_lib_param_bn::{
    BooleanNetwork, FnUpdate, ModelAnnotation, RegulatoryGraph, VariableId,
};
use std::collections::BTreeSet;
use std::ops::{Index, IndexMut};
use z3::{Sort, SortKind};

/// Stores input data for a model inference problem without interacting with a solver.
pub struct InferenceProblem<SOLVER> {
    /// Collection describing the properties of variables that must appear in the inferred model.
    declared_variables: Vec<VariableData>,
    /// Collection of "named states" that can be referenced by inference constraints
    /// to assert model properties.
    declared_abstract_states: BTreeSet<String>,
    /// List of constraints that must be satisfied by the inferred model.
    inference_constraints: Vec<DynInferenceConstraint<SOLVER>>,
}

/// A data struct managing known information about one model variable within [`InferenceProblem`].
pub struct VariableData {
    /// Human-readable name of the variable. The uniqueness of variable names is not enforced.
    pub name: String,
    /// An inclusive interval of admissible values for this variable.
    pub domain: (u32, u32),
    /// Regulators of this variable.
    pub regulators: BTreeSet<VariableId>,
    /// Optional concrete update function expression for this variable.
    /// Currently, we only support either no expression (completely uninterpreted function) or a
    /// fully specified expression (no parameters).
    pub update_expr: Option<FnUpdate>,
    /// A hidden private field to make sure this struct can only be instantiated by this module.
    _hidden: (),
}

impl VariableData {
    pub fn is_boolean(&self) -> bool {
        self.ast_type() == AstType::Bool
    }

    pub fn is_int(&self) -> bool {
        self.ast_type() == AstType::Int
    }

    pub fn has_update_expr(&self) -> bool {
        self.update_expr.is_some()
    }

    pub fn update_expr(&self) -> &Option<FnUpdate> {
        &self.update_expr
    }

    pub fn ast_type(&self) -> AstType {
        if self.domain.0 == 0 && self.domain.1 == 1 {
            AstType::Bool
        } else {
            AstType::Int
        }
    }

    pub fn sort(&self) -> Sort {
        match self.ast_type() {
            AstType::Int => Sort::int(),
            AstType::Bool => Sort::bool(),
        }
    }

    pub fn sort_kind(&self) -> SortKind {
        self.ast_type().into()
    }

    pub fn regulators_iter(&self) -> impl Iterator<Item = VariableId> {
        self.regulators.iter().copied()
    }

    pub fn regulator_index(&self, regulator: VariableId) -> Option<usize> {
        self.regulators_iter().position(|r| r == regulator)
    }

    pub fn new_const(&self, name: &str) -> TypedAst {
        self.ast_type().new_const(name)
    }
}

impl<SOLVER: 'static> Index<VariableId> for InferenceProblem<SOLVER> {
    type Output = VariableData;

    fn index(&self, index: VariableId) -> &Self::Output {
        self.get_variable(index)
            .unwrap_or_else(|| panic!("Variable `{index:?}` not found."))
    }
}

impl<SOLVER: 'static> IndexMut<VariableId> for InferenceProblem<SOLVER> {
    fn index_mut(&mut self, index: VariableId) -> &mut Self::Output {
        self.get_variable_mut(index)
            .unwrap_or_else(|| panic!("Variable `{index:?}` not found."))
    }
}

impl<SOLVER: 'static> Default for InferenceProblem<SOLVER> {
    fn default() -> Self {
        InferenceProblem::new()
    }
}

impl<SOLVER: 'static> InferenceProblem<SOLVER> {
    pub fn new() -> InferenceProblem<SOLVER> {
        InferenceProblem {
            declared_variables: vec![],
            declared_abstract_states: Default::default(),
            inference_constraints: vec![],
        }
    }

    pub fn get_variable(&self, variable: VariableId) -> Option<&VariableData> {
        self.declared_variables.get(variable.to_index())
    }

    pub fn find_variable(&self, name: &str) -> Option<VariableId> {
        self.declared_variables
            .iter()
            .position(|it| it.name == name)
            .map(VariableId::from_index)
    }

    pub fn get_variable_mut(&mut self, variable: VariableId) -> Option<&mut VariableData> {
        if !self.inference_constraints.is_empty() {
            panic!("Cannot update variable data once inference constraint has been added.");
        }
        self.declared_variables.get_mut(variable.to_index())
    }

    pub fn has_state(&self, state: &str) -> bool {
        self.declared_abstract_states.contains(state)
    }

    pub fn variables(&self) -> impl Iterator<Item = VariableId> {
        (0..self.declared_variables.len()).map(VariableId::from_index)
    }

    pub fn states(&self) -> impl Iterator<Item = String> {
        self.declared_abstract_states.iter().cloned()
    }

    pub fn constraints(&self) -> impl Iterator<Item = &dyn InferenceConstraint<SOLVER>> {
        self.inference_constraints.iter().map(|it| it.as_ref())
    }

    /// Declare a new system variable of the inference problem, returning the variable's ID.
    ///
    /// # Panics
    ///
    /// Variables cannot be created or modified once any inference constraint has been added
    /// to this [`InferenceProblem`] instance.
    pub fn declare_variable(&mut self, name: &str, domain: (u32, u32)) -> VariableId {
        if !self.inference_constraints.is_empty() {
            panic!("Cannot update variable data once inference constraint has been added.");
        }

        let data = VariableData {
            name: name.to_string(),
            domain,
            regulators: BTreeSet::default(),
            update_expr: None,
            _hidden: (),
        };
        self.declared_variables.push(data);
        VariableId::from_index(self.declared_variables.len() - 1)
    }

    /// Declare a new abstract state, returning true if the state was created
    /// successfully (false if it already exists).
    pub fn declare_state(&mut self, name: &str) -> bool {
        if self.declared_abstract_states.contains(name) {
            return false;
        }
        self.declared_abstract_states.insert(name.to_string());
        true
    }

    /// Assert new inference constraint.
    ///
    /// Note that variables cannot be created or modified once any inference constraint
    /// has been added to this [`InferenceProblem`] instance.
    pub fn assert_constraint<C: InferenceConstraint<SOLVER>>(
        &mut self,
        constraint: C,
    ) -> Result<(), anyhow::Error> {
        constraint.validate(self)?;
        self.inference_constraints.push(Box::new(constraint));
        Ok(())
    }

    /// Assert new dynamic inference constraint.
    ///
    /// Note that variables cannot be created or modified once any inference constraint
    /// has been added to this [`InferenceProblem`] instance.
    pub fn assert_dyn_constraint(
        &mut self,
        constraint: DynInferenceConstraint<SOLVER>,
    ) -> Result<(), anyhow::Error> {
        constraint.validate(self)?;
        self.inference_constraints.push(constraint);
        Ok(())
    }
}

impl<SOLVER: AbstractMonotoneBoundedIntSolver + 'static> InferenceProblem<SOLVER> {
    /// Completely initialize the [`InferenceProblem`] from the given [`RegulatoryGraph`],
    /// declaring all variables as Boolean and using their declared regulations. All update
    /// function expressions remain completely unspecified.
    pub fn from_influence_graph(
        rg: &RegulatoryGraph,
    ) -> Result<InferenceProblem<SOLVER>, anyhow::Error> {
        let mut inference_problem = InferenceProblem::new();

        // Declare all variables:
        for var in rg.variables() {
            let var_p = inference_problem.declare_variable(rg.get_variable_name(var), (0, 1));
            assert_eq!(var_p, var);
        }

        inference_problem.initialize_regulations(rg)?;
        Ok(inference_problem)
    }

    /// Initialize regulations between variables based on the provided [`RegulatoryGraph`],
    /// assuming all variables are already declared.
    ///
    /// This can be used as a helper function when you want to use a specific graph, but want
    /// to override variable domains.
    pub fn initialize_regulations(&mut self, rg: &RegulatoryGraph) -> Result<(), anyhow::Error> {
        // Declare all regulations:
        for reg in rg.regulations() {
            self[reg.target].regulators.insert(reg.regulator);
        }

        // Declare all monotonic inputs (these need to go first):
        for c in RegulatorIsMonotone::read_from(rg) {
            self.assert_constraint(c)?;
        }

        // Declare all essential inputs:
        for c in RegulatorIsEssential::read_from(rg) {
            self.assert_constraint(c)?;
        }

        Ok(())
    }

    /// Initialize (optional) update function expressions for Boolean variables based on the
    /// provided [`BooleanNetwork`], assuming all variables are already declared.
    ///
    /// This assumes that [`Self::initialize_regulations`] (or [`Self::from_influence_graph`])
    /// was already called on to populate the inference problem with variables and regulations.
    ///
    /// Expressions can only be provided for Boolean variables, and these can only reference the
    /// variable's regulators. We currently do not support partially specified update functions,
    /// fully uninterpreted or fully specified (no nested parameters are allowed yet).
    pub fn initialize_update_expressions(
        &mut self,
        bn: &BooleanNetwork,
    ) -> Result<(), anyhow::Error> {
        // Declare all update expressions specified in the BN:
        for variable in bn.variables() {
            let update_expr = bn.get_update_function(variable);
            if let Some(expression) = update_expr {
                // Single explicit uninterpreted function as update fn is okay, this will be
                // solved by the standard inference as if the function would be empty
                if expression.as_param().is_some() {
                    continue;
                }

                if !self[variable].domain.1 <= 1 {
                    panic!("Specifying update functions is only available for Boolean variables.");
                }
                if !expression.collect_parameters().is_empty() {
                    panic!("Partially specified update functions are not supported yet.");
                }
                for arg in expression.collect_arguments() {
                    if !self[variable].regulators.contains(&arg) {
                        panic!(
                            "Variable {arg} does not regulate {variable} and cant appear in its update fn."
                        );
                    }
                }

                // This bypasses the `get_variable_mut` check that no constraints were added yet,
                // since we need regulation constraints to already be placed at this point.
                self.declared_variables
                    .get_mut(variable.to_index())
                    .unwrap()
                    .update_expr = update_expr.clone();
            }
        }

        Ok(())
    }

    /// Read all constraints from an annotated `.aeon` file, **ignoring** any weights
    /// and priority classes, and assert them into the provided inference problem.
    ///
    /// This assumes that [`Self::initialize_regulations`] (or [`Self::from_influence_graph`])
    /// was already called on to populate the inference problem with variables and regulations.
    pub fn initialize_constraints(
        &mut self,
        psbn: &BooleanNetwork,
        annotation: &ModelAnnotation,
    ) -> Result<(), anyhow::Error> {
        // First, go through all state declarations:
        self.initialize_state_declarations(annotation)?;

        // Then go through different types of constraints, parse them, and assert them.

        for (c, _meta) in StateComparison::read_from::<SOLVER>(annotation)? {
            self.assert_constraint(c)?;
        }

        for (c, _meta) in StateIsFixedPoint::read_from::<SOLVER>(annotation)? {
            self.assert_constraint(c)?;
        }

        for (c, _meta) in ValueComparison::read_from::<SOLVER>(psbn, annotation)? {
            self.assert_constraint(c)?;
        }

        Ok(())
    }

    fn initialize_state_declarations(
        &mut self,
        annotation: &ModelAnnotation,
    ) -> Result<(), anyhow::Error> {
        if let Some(declarations) =
            annotation.get_value(&[ConstraintStrings::STATE, ConstraintStrings::DECLARE])
        {
            for name in declarations.lines() {
                if !self.declare_state(name) {
                    return Err(anyhow!("State `{name}` is declared more than once."));
                }
            }
        }
        Ok(())
    }
}

impl<SOLVER: AbstractMonotoneBoundedIntOptimizeSolver + 'static> InferenceProblem<SOLVER> {
    /// Read all constraints from an annotated `.aeon` file, including any weights
    /// and priority classes, and assert them into the provided inference problem.
    ///
    /// This assumes that [`Self::initialize_regulations`] (or [`Self::from_influence_graph`])
    /// was already called on this inference problem.
    pub fn initialize_constraints_and_weights(
        &mut self,
        psbn: &BooleanNetwork,
        annotation: &ModelAnnotation,
    ) -> Result<(), anyhow::Error> {
        // First, go through all state declarations:
        // First, go through all state declarations:
        self.initialize_state_declarations(annotation)?;

        // Then go through different types of constraints, parse them, and assert them.

        for (c, meta) in StateComparison::read_from::<SOLVER>(annotation)? {
            self.assert_dyn_constraint(SoftConstraint::wrap_if_soft(c, meta)?)?;
        }

        for (c, meta) in StateIsFixedPoint::read_from::<SOLVER>(annotation)? {
            self.assert_dyn_constraint(SoftConstraint::wrap_if_soft(c, meta)?)?;
        }

        for (c, meta) in ValueComparison::read_from::<SOLVER>(psbn, annotation)? {
            self.assert_dyn_constraint(SoftConstraint::wrap_if_soft(c, meta)?)?;
        }

        Ok(())
    }
}
