use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractMonotoneSolver;
use biodivine_lib_param_bn::{Monotonicity, RegulatoryGraph, VariableId};
use log::info;

/// TODO: There cant be monotonicity constraints on fully specified functions
/// at this moment. Support for this will be added later.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct RegulatorIsMonotone {
    target: VariableId,
    regulator: VariableId,
    is_positive: bool,
}

impl RegulatorIsMonotone {
    pub fn new(target: VariableId, regulator: VariableId, is_positive: bool) -> Self {
        Self {
            target,
            regulator,
            is_positive,
        }
    }

    pub fn new_positive(target: VariableId, regulator: VariableId) -> Self {
        Self::new(target, regulator, true)
    }

    pub fn new_negative(target: VariableId, regulator: VariableId) -> Self {
        Self::new(target, regulator, false)
    }

    /// Read all monotonicity constraints from a given [`RegulatorIsMonotone`].
    pub fn read_from(psbn: &RegulatoryGraph) -> Vec<RegulatorIsMonotone> {
        psbn.regulations()
            .filter_map(|it| {
                it.get_monotonicity().map(|monotonicity| {
                    Self::new(
                        it.target,
                        it.regulator,
                        monotonicity == Monotonicity::Activation,
                    )
                })
            })
            .collect()
    }
}

impl<SOLVER: AbstractMonotoneSolver + 'static> InferenceConstraint<SOLVER> for RegulatorIsMonotone {
    /// Ensure that `target` exists and it has the given `regulator`.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error> {
        check_variable_exists(problem, self.target)?;
        check_regulator_exists(problem, self.target, self.regulator)?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), anyhow::Error> {
        // TODO: Monotonicity for fully specified functions needs to be checked directly via a
        //       different mechanism within the encoder in future. We just ignore it here for now.
        let update_fn = encoder.update_function(self.target);
        if !update_fn.is_uninterpreted() {
            info!(
                "Ignoring monotonicity of `{:?}` -> `{:?}` because {:?} has fully specified function.",
                self.regulator, self.target, self.target
            );
            return Ok(());
        }

        info!(
            "Asserting: regulator `{:?}` is monotone (is_positive={}) in target `{:?}`.",
            self.regulator, self.is_positive, self.target
        );
        let function = update_fn.as_func_decl().unwrap(); // Can safely unwrap now.
        let argument = encoder.problem[self.target]
            .regulator_index(self.regulator)
            .unwrap_or_else(|| unreachable!()); // Must fail during validation.

        if self.is_positive {
            solver.set_monotone(function, argument)
        } else {
            solver.set_antimonotone(function, argument)
        }
    }
}
