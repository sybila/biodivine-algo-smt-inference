use crate::bn_inference::constraints::{ConstraintStrings, check_state_exists, sorted_map};
use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder, SimpleInferenceConstraint};
use crate::smt_solver::AbstractSolver;
use anyhow::Error;
use biodivine_lib_param_bn::ModelAnnotation;
use log::trace;
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

    /// Read all fixed-point states from the given model annotations.
    ///
    /// The method returns each constraint together with its metadata (again represented as
    /// an annotation).
    pub fn read_from<SOLVER: AbstractSolver + 'static>(
        model_annotation: &ModelAnnotation,
    ) -> Result<Vec<(Self, &ModelAnnotation)>, Error> {
        let mut result = Vec::new();
        let constraints =
            model_annotation.get_child(&[ConstraintStrings::STATE, ConstraintStrings::FIXED_POINT]);
        if let Some(constraints) = constraints {
            for (state, inner) in sorted_map(constraints.children()) {
                result.push((Self::new(state), inner));
            }
        }
        Ok(result)
    }
}

impl<SOLVER: AbstractSolver + 'static> SimpleInferenceConstraint<SOLVER> for StateIsFixedPoint {
    /// Checks that the `state` exists.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_state_exists(problem, self.state.as_str())
    }

    fn mk_assertion(&self, encoder: &InferenceProblemEncoder<SOLVER>) -> Result<Bool, Error> {
        trace!("Building assertion: state `{}` is fixed-point.", self.state);
        let mut conjunction = Vec::new();
        for var in encoder.problem.variables() {
            let var_atom = encoder.state_atom(&self.state, var);
            let args = encoder.problem[var]
                .regulators_iter()
                .map(|regulator| encoder.state_atom(&self.state, regulator))
                .collect::<Vec<_>>();
            let var_function_call = encoder.mk_update_function_call(var, &args);
            trace!(
                "Asserting: `{var:?}` is fixed to `{var_atom}` in fixed-point state `{}`.",
                self.state
            );
            conjunction.push(var_atom.eq(&var_function_call)?);
        }
        Ok(Bool::and(&conjunction))
    }
}
