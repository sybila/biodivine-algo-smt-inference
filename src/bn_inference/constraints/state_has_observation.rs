use crate::bn_inference::constraints::{check_state_exists, check_state_observation};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::{AbstractOptimizeSolver, AbstractSolver};
use anyhow::Error;
use biodivine_lib_param_bn::VariableId;
use num_rational::BigRational;
use std::collections::BTreeMap;

/// Values that were observed within a single system state. Each value can have an optional
/// [`BigRational`] "weight", expressing the penalty for violating this constraint.
///
/// When an optimizing solver is used, the result should minimize the sum of such penalties.
/// However, if using a non-optimizing solver, the weight can be ignored. If no weight
/// is provided, we consider the observation to be a "hard constraint" that cannot be violated.
pub struct StateObservation {
    values: BTreeMap<VariableId, (u32, Option<BigRational>)>,
}

impl StateObservation {
    pub fn from_exact(values: impl IntoIterator<Item = (VariableId, u32)>) -> Self {
        StateObservation {
            values: values.into_iter().map(|(k, v)| (k, (v, None))).collect(),
        }
    }

    pub fn from_weighted(
        values: impl IntoIterator<Item = (VariableId, (u32, Option<BigRational>))>,
    ) -> Self {
        StateObservation {
            values: values.into_iter().collect(),
        }
    }

    /// Iterator over all observed values.
    pub fn observations(&self) -> impl Iterator<Item = (VariableId, u32)> {
        self.values.iter().map(|(a, (b, _))| (*a, *b))
    }

    /// Iterator over all observed values and their weights.
    pub fn weighted_observations(
        &self,
    ) -> impl Iterator<Item = (VariableId, u32, Option<BigRational>)> {
        self.values.iter().map(|(a, (b, c))| (*a, *b, c.clone()))
    }
}

/// Asserts that a state must exactly follow the given observation, ignoring any potential
/// confidence coefficients (every value is treated as a "hard constraint").
pub struct StateHasExactObservation {
    state: String,
    observation: StateObservation,
}

/// Asserts that a state must follow the given observation, using soft constraints to model
/// observations that have some confidence coefficient. Consequently, this constraint can only
/// be used with instances of [`AbstractOptimizeSolver`].
pub struct StateHasWeightedObservation {
    state: String,
    observation: StateObservation,
}

impl StateHasExactObservation {
    pub fn new(state: &str, observation: StateObservation) -> Self {
        Self {
            state: state.to_string(),
            observation,
        }
    }
}

impl StateHasWeightedObservation {
    pub fn new(state: &str, observation: StateObservation) -> Self {
        Self {
            state: state.to_string(),
            observation,
        }
    }
}

impl<SOLVER: AbstractSolver + 'static> InferenceConstraint<SOLVER> for StateHasExactObservation {
    /// Ensure that the state exists and all variable values are valid within their domain.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_state_exists(problem, self.state.as_str())?;
        check_state_observation(problem, &self.observation)?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), Error> {
        // Assert that all state atoms have the values they are expected to have.
        for (variable, observation) in self.observation.observations() {
            let atom = encoder.state_atom(&self.state, variable);
            let value = encoder.problem[variable].ast_type().new_value(observation);
            solver.assert(&atom.eq(&value)?);
        }
        Ok(())
    }
}

impl<SOLVER: AbstractOptimizeSolver + 'static> InferenceConstraint<SOLVER>
    for StateHasWeightedObservation
{
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_state_exists(problem, self.state.as_str())?;
        check_state_observation(problem, &self.observation)?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), Error> {
        // Assert that all state atoms have the values they are expected to have. Treat observations
        // without coefficients as hard constraints.
        for (variable, observation, weight) in self.observation.weighted_observations() {
            let atom = encoder.state_atom(&self.state, variable);
            let value = encoder.problem[variable].ast_type().new_value(observation);
            if let Some(weight) = weight {
                solver.assert_soft(&atom.eq(&value)?, weight);
            } else {
                solver.assert(&atom.eq(&value)?);
            }
        }
        Ok(())
    }
}
