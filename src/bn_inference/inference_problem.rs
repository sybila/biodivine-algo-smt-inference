use crate::bn_inference::constraints::{RegulatorIsEssential, RegulatorIsMonotone};
use crate::bn_inference::{InferenceConstraint, InferenceProblemEncoder};
use crate::smt_solver::AbstractMonotoneSolver;
use crate::smt_solver::typed_ast::{AstType, TypedAst};
use biodivine_lib_param_bn::{Monotonicity, RegulatoryGraph, VariableId};
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
    inference_constraints: Vec<Box<dyn InferenceConstraint<SOLVER>>>,
}

/// A data struct managing known information about one model variable within [`InferenceProblem`].
pub struct VariableData {
    /// Human-readable name of the variable. The uniqueness of variable names is not enforced.
    pub name: String,
    /// An inclusive interval of admissible values for this variable.
    pub domain: (u32, u32),
    /// Regulators of this variable.
    pub regulators: BTreeSet<VariableId>,
    /// A hidden private field to make sure this struct can only be instantiated by this module.
    _hidden: (),
}

impl VariableData {
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

    pub fn build_solver(&self, solver: &mut SOLVER) -> Result<(), anyhow::Error> {
        let encoder = InferenceProblemEncoder::new(self);
        for constraint in self.constraints() {
            constraint.assert_self(&encoder, solver)?;
        }
        Ok(())
    }
}

impl<SOLVER: AbstractMonotoneSolver + 'static> InferenceProblem<SOLVER> {
    pub fn from_influence_graph(
        rg: &RegulatoryGraph,
    ) -> Result<InferenceProblem<SOLVER>, anyhow::Error> {
        let mut inference_problem = InferenceProblem::new();
        // Declare all variables:
        for var in rg.variables() {
            let var_p = inference_problem.declare_variable(rg.get_variable_name(var), (0, 1));
            assert_eq!(var_p, var);
        }

        // Declare all regulations:
        for reg in rg.regulations() {
            inference_problem[reg.target]
                .regulators
                .insert(reg.regulator);
        }

        // Declare all monotonic inputs (these need to go first):
        for reg in rg.regulations() {
            if let Some(monotonicity) = reg.monotonicity {
                let constraint = RegulatorIsMonotone::new(
                    reg.target,
                    reg.regulator,
                    monotonicity == Monotonicity::Activation,
                );
                inference_problem.assert_constraint(constraint)?;
            }
        }

        // Declare all essential inputs:
        for reg in rg.regulations() {
            if reg.observable {
                let constraint = RegulatorIsEssential::new(reg.target, reg.regulator);
                inference_problem.assert_constraint(constraint)?;
            }
        }

        Ok(inference_problem)
    }
}
