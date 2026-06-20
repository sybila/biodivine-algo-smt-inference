use crate::bn_inference::SimpleInferenceConstraint;
use crate::smt_solver::AbstractSolver;
use anyhow::Error;
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use macros::InferenceConstraint;
use z3::ast::Bool;

/// Raw constraint is a way to assert a generic Z3 formula. This is mostly intended for
/// "internal use" in situations where the formula is already available but for some reason
/// needs to be used as a separate constraint.
#[derive(InferenceConstraint, Debug, PartialEq, Eq, Clone, Hash)]
pub struct RawConstraint(Bool);

impl<SOLVER: AbstractSolver + 'static> SimpleInferenceConstraint<SOLVER> for RawConstraint {
    fn validate(&self, _problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        Ok(())
    }

    fn mk_assertion(&self, _encoder: &InferenceProblemEncoder<SOLVER>) -> Result<Bool, Error> {
        Ok(self.0.clone())
    }
}

impl From<Bool> for RawConstraint {
    fn from(value: Bool) -> Self {
        RawConstraint(value)
    }
}

impl From<RawConstraint> for Bool {
    fn from(value: RawConstraint) -> Self {
        value.0
    }
}
