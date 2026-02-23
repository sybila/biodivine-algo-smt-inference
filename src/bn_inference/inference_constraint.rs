use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use downcast_rs::{Downcast, impl_downcast};

/// Implemented by objects that can be used to assert constraints in an [`InferenceProblem`].
/// It has access to an [`InferenceProblemEncoder`] which maps the elements of the inference
/// problem to SMT formulas, plus provides access to the underlying [`InferenceProblem`].
pub trait InferenceConstraint<SOLVER>: Downcast {
    /// Validate that this constraint can be safely asserted in the given inference problem.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error>;

    /// Assert this constraint into the given `SOLVER`, relying on data from the given
    /// [`InferenceProblem`] and [`InferenceProblemEncoder`].
    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), anyhow::Error>;
}

impl_downcast!(InferenceConstraint<SOLVER>);
