use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractMonotoneSolver;
use crate::smt_solver::typed_ast::TypedAst;
use anyhow::anyhow;
use biodivine_algo_smt_inference::bn_inference::UpdateFunctionDefinition;
use biodivine_lib_param_bn::{Monotonicity, RegulatoryGraph, VariableId};
use log::info;
use std::collections::HashMap;
use z3::SatResult;
use z3::ast::Bool;

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
        info!(
            "Asserting: regulator `{:?}` is monotone (is_positive={}) in target `{:?}`.",
            self.regulator, self.is_positive, self.target
        );
        let function = encoder.update_function(self.target);
        let argument_index = encoder.problem[self.target]
            .regulator_index(self.regulator)
            .unwrap_or_else(|| unreachable!()); // Must fail during validation.

        match function {
            UpdateFunctionDefinition::Uninterpreted(function) => {
                // If the function is uninterpreted, assert monotonicity as a solver property.
                if self.is_positive {
                    solver.set_monotone(function, argument_index)
                } else {
                    solver.set_antimonotone(function, argument_index)
                }
            }
            UpdateFunctionDefinition::FullySpecified(expression) => {
                // If the function is fully specified, execute a completely separate solver
                // query to verify that monotonicity holds. Under normal circumstances, this
                // query should be very simple to check and should not cause any
                // major performance issues.

                let target_data = &encoder.problem[self.target];
                let arg_prefix = "fully_specified_arg";

                let mut args = target_data
                    .regulators_iter()
                    .map(|reg| (reg, Bool::fresh_const(arg_prefix)))
                    .collect::<HashMap<_, _>>();

                args.insert(self.regulator, Bool::from_bool(false));
                let low = TypedAst::from_fn_update(expression, &args);

                args.insert(self.regulator, Bool::from_bool(true));
                let high = TypedAst::from_fn_update(expression, &args);

                let assertion = if self.is_positive {
                    // For positive monotonicity, we want to find a counter example
                    // where `f(high) < f(low)` (increasing input decreases output).
                    high.lt(&low)
                } else {
                    low.lt(&high)
                }?;

                // Make a new solver, add the assertion, and check that it is unsatisfiable,
                // i.e., no counter example exists and thus the expression is monotonic.
                let solver = z3::Solver::new();
                solver.assert(assertion);

                match solver.check() {
                    SatResult::Unsat => Ok(()),
                    SatResult::Unknown => {
                        unreachable!(
                            "Monotonicity of fully specified expression is always decidable."
                        )
                    }
                    SatResult::Sat => Err(anyhow!(
                        "Monotonicity mismatch for regulator `{}` in `{}`",
                        self.regulator,
                        expression
                    )),
                }
            }
        }
    }
}
