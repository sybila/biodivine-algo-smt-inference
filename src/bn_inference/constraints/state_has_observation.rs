use crate::bn_inference::constraints::{check_state_exists, check_state_observation};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::{AbstractOptimizeSolver, AbstractSolver};
use anyhow::Error;
use biodivine_lib_param_bn::VariableId;
use log::{debug, info};
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

    pub fn from_uniformly_weighted(
        values: impl IntoIterator<Item = (VariableId, u32)>,
        weight: BigRational,
    ) -> Self {
        StateObservation {
            values: values
                .into_iter()
                .map(|(k, v)| (k, (v, Some(weight.clone()))))
                .collect(),
        }
    }

    pub fn from_weighted(
        values: impl IntoIterator<Item = (VariableId, (u32, Option<BigRational>))>,
    ) -> Self {
        StateObservation {
            values: values.into_iter().collect(),
        }
    }

    pub fn size(&self) -> usize {
        self.values.len()
    }

    /// Iterator over all observed values, regardless of weight.
    pub fn all_observations(&self) -> impl Iterator<Item = (VariableId, u32)> {
        self.values.iter().map(|(a, (b, _))| (*a, *b))
    }

    /// Iterator over all observed values and their weights.
    pub fn all_observations_weighted(
        &self,
    ) -> impl Iterator<Item = (VariableId, u32, Option<BigRational>)> {
        self.values.iter().map(|(a, (b, c))| (*a, *b, c.clone()))
    }

    /// Iterator over all exact observations, i.e., those without a weight.
    pub fn only_exact_observations(&self) -> impl Iterator<Item = (VariableId, u32)> {
        self.values.iter().filter_map(
            |(a, (b, c))| {
                if c.is_none() { Some((*a, *b)) } else { None }
            },
        )
    }

    /// Iterator over all weighted observations, i.e., those with a weight.
    pub fn only_weighted_observations(
        &self,
    ) -> impl Iterator<Item = (VariableId, (u32, BigRational))> {
        self.values
            .iter()
            .filter_map(|(a, (b, c))| c.clone().map(|weight| (*a, (*b, weight))))
    }
}

/// Asserts that a state must exactly follow the given observation.
pub struct StateHasExactObservation {
    state: String,
    observation: BTreeMap<VariableId, u32>,
}

/// Asserts that a state must follow the given observation, using soft constraints to model
/// observation weight. Consequently, this constraint can only be used with instances
/// of [`AbstractOptimizeSolver`].
pub struct StateHasWeightedObservation {
    state: String,
    observation: BTreeMap<VariableId, (u32, BigRational)>,
}

impl StateHasExactObservation {
    pub fn new(state: &str, values: impl Iterator<Item = (VariableId, u32)>) -> Self {
        Self {
            state: state.to_string(),
            observation: BTreeMap::from_iter(values),
        }
    }

    pub fn len(&self) -> usize {
        self.observation.len()
    }

    pub fn is_empty(&self) -> bool {
        self.observation.is_empty()
    }

    pub fn state(&self) -> &str {
        &self.state
    }

    pub fn observations(&self) -> impl Iterator<Item = (VariableId, u32)> {
        self.observation.clone().into_iter()
    }
}

impl StateHasWeightedObservation {
    pub fn new(
        state: &str,
        values: impl Iterator<Item = (VariableId, (u32, BigRational))>,
    ) -> Self {
        Self {
            state: state.to_string(),
            observation: BTreeMap::from_iter(values),
        }
    }

    pub fn state(&self) -> &str {
        &self.state
    }
}

impl<SOLVER: AbstractSolver + 'static> InferenceConstraint<SOLVER> for StateHasExactObservation {
    /// Ensure that the state exists and all variable values are valid within their domain.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_state_exists(problem, self.state.as_str())?;
        check_state_observation(problem, self.observation.clone().into_iter())?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), Error> {
        // Assert that all state atoms have the values they are expected to have.
        info!("Asserting: state `{}` has exact observation.", self.state);
        for (variable, observation) in self.observation.iter() {
            let atom = encoder.state_atom(&self.state, *variable);
            let value = encoder.problem[*variable]
                .ast_type()
                .new_value(*observation);
            debug!(
                "Asserting: `{variable:?}` is fixed to `{value}` by observation in state `{}`.",
                self.state
            );
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
        check_state_observation(
            problem,
            self.observation.iter().map(|(var, (val, _))| (*var, *val)),
        )?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), Error> {
        // Assert that all state atoms have the values they are expected to have. Treat observations
        // without coefficients as hard constraints.
        info!(
            "Asserting: state `{}` has weighted observation.",
            self.state
        );
        for (variable, (observation, weight)) in self.observation.iter() {
            let atom = encoder.state_atom(&self.state, *variable);
            let value = encoder.problem[*variable]
                .ast_type()
                .new_value(*observation);
            debug!(
                "Asserting: `{variable:?}` is fixed to `{value}` with weight {weight} by observation in state `{}`.",
                self.state
            );
            solver.assert_soft(&atom.eq(&value)?, weight.clone());
        }
        Ok(())
    }
}
