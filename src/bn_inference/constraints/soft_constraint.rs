use crate::bn_inference::SimpleInferenceConstraint;
use crate::smt_solver::AbstractOptimizeSolver;
use anyhow::Error;
use biodivine_algo_smt_inference::bn_inference::{
    InferenceConstraint, InferenceProblem, InferenceProblemEncoder,
};
use num_rational::BigRational;
use std::marker::PhantomData;
use z3::Symbol;

/// A wrapper for [`SimpleInferenceConstraint`] allowing to designate a constraint as "soft".
/// Soft constraints do not have to be satisfied, but violation incurs a penalty that the solver
/// will attempt to minimize.
///
/// Soft constraints can optionally belong to numbered priority classes, in which case the solver
/// will treat these as independent optimization criteria subject to ascending priority.
/// Ordering class `0` is the default (maximal) optimization priority.
///
/// *Note that you can also create dedicated soft constraints directly by implementing
/// [`InferenceConstraint`]. However, [`SoftConstraint`] makes it possible to interpret instances
/// of [`SimpleInferenceConstraint`] as soft constraints directly without any code duplication.*
pub struct SoftConstraint<SOLVER: AbstractOptimizeSolver, C: SimpleInferenceConstraint<SOLVER>> {
    constraint: C,
    priority_class: Symbol,
    weight: BigRational,
    _phantom: PhantomData<SOLVER>,
}

impl<SOLVER: AbstractOptimizeSolver, C: SimpleInferenceConstraint<SOLVER>>
    SoftConstraint<SOLVER, C>
{
    pub fn with_weight(constraint: C, weight: BigRational) -> Self {
        SoftConstraint {
            constraint,
            priority_class: Symbol::Int(0u32),
            weight,
            _phantom: Default::default(),
        }
    }

    pub fn with_weight_and_class(constraint: C, weight: BigRational, priority_class: u32) -> Self {
        SoftConstraint {
            constraint,
            priority_class: Symbol::Int(priority_class),
            weight,
            _phantom: Default::default(),
        }
    }
}

impl<SOLVER: AbstractOptimizeSolver + 'static, C: SimpleInferenceConstraint<SOLVER> + 'static>
    InferenceConstraint<SOLVER> for SoftConstraint<SOLVER, C>
{
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        self.constraint.validate(problem)
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), Error> {
        let assertion = self.constraint.mk_assertion(encoder)?;
        solver.assert_soft_with_class(
            &assertion,
            self.weight.clone(),
            Some(self.priority_class.clone()),
        );
        Ok(())
    }
}
