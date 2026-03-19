use crate::bn_inference::constraints::{ConstraintStrings, check_state_exists, sorted_map};
use crate::bn_inference::{InferenceProblem, InferenceProblemEncoder, SimpleInferenceConstraint};
use crate::smt_solver::AbstractSolver;
use anyhow::anyhow;
use biodivine_lib_param_bn::ModelAnnotation;
use log::info;
use macros::InferenceConstraint;
use z3::ast::Bool;

/// A simple constraint which enforces that two given states must be either equivalent or different.
///
/// Naturally, both states must exist in the related [`InferenceProblem`].
#[derive(InferenceConstraint, Debug, PartialEq, Eq, Clone, Hash)]
pub struct StateComparison {
    is_equal: bool,
    left: String,
    right: String,
}

impl StateComparison {
    pub fn new_equal(left: &str, right: &str) -> Self {
        StateComparison {
            is_equal: true,
            left: left.to_string(),
            right: right.to_string(),
        }
    }

    pub fn new_not_equal(left: &str, right: &str) -> Self {
        StateComparison {
            is_equal: false,
            left: left.to_string(),
            right: right.to_string(),
        }
    }

    /// Read all state comparisons from the given model annotations.
    ///
    /// The method returns each constraint together with its metadata (again represented as
    /// an annotation).
    pub fn read_from<SOLVER: AbstractSolver + 'static>(
        model_annotation: &ModelAnnotation,
    ) -> Result<Vec<(Self, &ModelAnnotation)>, anyhow::Error> {
        let mut result = Vec::new();
        let equalities =
            model_annotation.get_child(&[ConstraintStrings::STATE, ConstraintStrings::EQUAL]);
        if let Some(equalities) = equalities {
            for (left_state, inner) in sorted_map(equalities.children()) {
                if inner.children().is_empty() {
                    return Err(anyhow!(
                        "Malformed equality constraint for state `{}`.",
                        left_state
                    ));
                }
                for (right_state, inner) in sorted_map(inner.children()) {
                    result.push((Self::new_equal(left_state, right_state), inner));
                }
            }
        }
        let inequalities =
            model_annotation.get_child(&[ConstraintStrings::STATE, ConstraintStrings::NOT_EQUAL]);
        if let Some(inequalities) = inequalities {
            for (left_state, inner) in sorted_map(inequalities.children()) {
                if inner.children().is_empty() {
                    return Err(anyhow!(
                        "Malformed inequality constraint for state `{}`.",
                        left_state
                    ));
                }
                for (right_state, inner) in sorted_map(inner.children()) {
                    result.push((Self::new_not_equal(left_state, right_state), inner));
                }
            }
        }
        Ok(result)
    }
}

impl<SOLVER: AbstractSolver + 'static> SimpleInferenceConstraint<SOLVER> for StateComparison {
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error> {
        check_state_exists(problem, self.left.as_str())?;
        check_state_exists(problem, self.right.as_str())?;
        Ok(())
    }

    fn mk_assertion(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
    ) -> Result<Bool, anyhow::Error> {
        if self.is_equal {
            info!(
                "Making state equality assertion `{} == {}`.",
                self.left, self.right
            );
        } else {
            info!(
                "Making state inequality assertion `{} != {}`.",
                self.left, self.right
            );
        }

        let equalities = encoder
            .problem
            .variables()
            .map(|var| {
                let left_atom = encoder.state_atom(self.left.as_str(), var);
                let right_atom = encoder.state_atom(self.right.as_str(), var);
                left_atom.eq(right_atom).expect(
                    "Correctness violation: Two atoms of a variable have incompatible types.",
                )
            })
            .collect::<Vec<_>>();

        let all_are_equal = Bool::and(&equalities);
        if self.is_equal {
            Ok(all_are_equal)
        } else {
            Ok(all_are_equal.not())
        }
    }
}
