use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractMonotoneSolver;
use anyhow::Error;
use biodivine_lib_param_bn::VariableId;

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
}

impl<SOLVER: AbstractMonotoneSolver + 'static> InferenceConstraint<SOLVER> for RegulatorIsMonotone {
    /// Ensure that `target` exists and it has the given `regulator`.
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), Error> {
        check_variable_exists(problem, self.target)?;
        check_regulator_exists(problem, self.target, self.regulator)?;
        Ok(())
    }

    fn assert_self(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        solver: &mut SOLVER,
    ) -> Result<(), anyhow::Error> {
        let function = encoder.update_function(self.target);
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
