use crate::bn_inference::SimpleInferenceConstraint;
use crate::bn_inference::constraints::ConstraintStrings;
use crate::smt_solver::AbstractOptimizeSolver;
use anyhow::Error;
use biodivine_algo_smt_inference::bn_inference::{
    InferenceConstraint, InferenceProblem, InferenceProblemEncoder,
};
use biodivine_lib_param_bn::ModelAnnotation;
use log::info;
use num_rational::BigRational;
use num_traits::One;
use std::fmt::{Debug, Formatter};
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
pub struct SoftConstraint<SOLVER: AbstractOptimizeSolver> {
    pub constraint: Box<dyn SimpleInferenceConstraint<SOLVER>>,
    pub priority_class: u32,
    pub weight: BigRational,
    _phantom: PhantomData<SOLVER>,
}

impl<SOLVER: AbstractOptimizeSolver> SoftConstraint<SOLVER> {
    pub fn with_weight<C: SimpleInferenceConstraint<SOLVER>>(
        constraint: C,
        weight: BigRational,
    ) -> Self {
        SoftConstraint {
            constraint: Box::new(constraint),
            priority_class: 0,
            weight,
            _phantom: Default::default(),
        }
    }

    pub fn with_weight_and_class<C: SimpleInferenceConstraint<SOLVER>>(
        constraint: C,
        weight: BigRational,
        priority_class: u32,
    ) -> Self {
        SoftConstraint {
            constraint: Box::new(constraint),
            priority_class,
            weight,
            _phantom: Default::default(),
        }
    }
}

impl<SOLVER: AbstractOptimizeSolver + 'static> SoftConstraint<SOLVER> {
    /// Wraps a given constraint into a soft constraint if applicable
    /// based on the provided model annotation.
    ///
    /// The soft constraint is created if the annotation contains either a valid `weight` or
    /// `priority-class` key. If neither is provided, it remains a hard constraint.
    pub fn wrap_if_soft<
        INNER: SimpleInferenceConstraint<SOLVER> + InferenceConstraint<SOLVER> + 'static,
    >(
        inner: INNER,
        metadata: &ModelAnnotation,
    ) -> Result<Box<dyn InferenceConstraint<SOLVER>>, Error> {
        let mut priority_class: Option<u32> = None;
        if let Some(class) = metadata.get_value(&[ConstraintStrings::PRIORITY_CLASS]) {
            priority_class = Some(class.parse::<u32>()?);
        };
        let mut weight: Option<BigRational> = None;
        if let Some(weight_str) = metadata.get_value(&[ConstraintStrings::WEIGHT]) {
            weight = Some(big_rational_str::str_to_big_rational(weight_str)?);
        };
        if priority_class.is_none() && weight.is_none() {
            return Ok(Box::new(inner));
        };
        let priority_class = priority_class.unwrap_or(0u32);
        let weight = weight.unwrap_or(BigRational::one());
        Ok(Box::new(Self::with_weight_and_class(
            inner,
            weight,
            priority_class,
        )))
    }
}

impl<SOLVER: AbstractOptimizeSolver + 'static> InferenceConstraint<SOLVER>
    for SoftConstraint<SOLVER>
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
        info!(
            "Asserting soft constraint `{:?}` with `weight={}` and `priority_class={:?}`",
            self.constraint, self.weight, self.priority_class
        );
        solver.assert_soft_with_class(
            &assertion,
            self.weight.clone(),
            Some(Symbol::Int(self.priority_class)),
        );
        Ok(())
    }
}

impl<SOLVER: AbstractOptimizeSolver> Debug for SoftConstraint<SOLVER> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SoftConstraint {{ constraint: {:?}, weight: {}, priority_class: {} }}",
            self.constraint, self.weight, self.priority_class
        )
    }
}
