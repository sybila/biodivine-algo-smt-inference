use crate::bn_inference::constraints::check_state_exists;
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractSolver;
use log::{debug, info};

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

impl<SOLVER: AbstractSolver + 'static> InferenceConstraint<SOLVER> for StateIsFixedPoint {
    /// Checks that the `state` exists.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error> {
        check_state_exists(problem, self.state.as_str())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), anyhow::Error> {
        info!("Asserting: state `{}` is fixed-point.", self.state);
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
            solver.assert(&var_atom.eq(&var_function_call)?);
        }
        Ok(())
    }
}
