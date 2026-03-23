use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use downcast_rs::{Downcast, impl_downcast};
use z3::ast::Bool;

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

/// A boxed, dynamic variant of [`InferenceConstraint`].
pub type DynInferenceConstraint<SOLVER> = Box<dyn InferenceConstraint<SOLVER>>;

/// A simplified variant of [`InferenceConstraint`] that is used in situations where
/// the whole constraint can be expressed as a single formula, without requiring addition
/// interaction with the solver or other special treatment.
///
/// Simple constraints can either directly derive [`InferenceConstraint`], or they can be
/// wrapped into [`crate::bn_inference::constraints::SoftConstraint`] to allow optimization as
/// soft constraints. Note that the `#[derive(InferenceConstraint)]` currently only works
/// if `SimpleInferenceConstraint` is implemented for [`crate::smt_solver::AbstractSolver`].
pub trait SimpleInferenceConstraint<SOLVER>: Downcast {
    /// Equivalent to [`InferenceConstraint::validate`].
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error>;

    /// Produce a formula that can be given to the `SOLVER` when
    /// [`InferenceConstraint::assert_self`] is called.
    fn mk_assertion(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
    ) -> Result<Bool, anyhow::Error>;
}

impl_downcast!(SimpleInferenceConstraint<SOLVER>);
