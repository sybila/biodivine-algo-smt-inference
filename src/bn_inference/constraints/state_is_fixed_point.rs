use crate::bn_inference::constraints::check_state_exists;
use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder, SimpleInferenceConstraint};
use crate::smt_solver::AbstractSolver;
use anyhow::Error;
use log::{debug, info};
use macros::InferenceConstraint;
use z3::ast::Bool;

#[derive(InferenceConstraint, Clone, Debug, PartialEq, Eq, Hash)]
pub struct StateIsFixedPoint {
    state: String,
}

impl StateIsFixedPoint {
    pub fn new(state: &str) -> Self {
        Self {
            state: state.to_string(),
        }
    }
}

impl<SOLVER: AbstractSolver + 'static> SimpleInferenceConstraint<SOLVER> for StateIsFixedPoint {
    /// Checks that the `state` exists.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_state_exists(problem, self.state.as_str())
    }

    fn mk_assertion(&self, encoder: &InferenceProblemEncoder<SOLVER>) -> Result<Bool, Error> {
        info!("Building assertion: state `{}` is fixed-point.", self.state);
        let mut conjunction = Vec::new();
        for var in encoder.problem.variables() {
            let var_atom = encoder.state_atom(&self.state, var);
            let args = encoder.problem[var]
                .regulators_iter()
                .map(|regulator| encoder.state_atom(&self.state, regulator))
                .collect::<Vec<_>>();
            let var_function_call = encoder.mk_update_function_call(var, &args);
            debug!(
                "Asserting: `{var:?}` is fixed to `{var_atom}` in fixed-point state `{}`.",
                self.state
            );
            conjunction.push(var_atom.eq(&var_function_call)?);
        }
        Ok(Bool::and(&conjunction))
    }
}
