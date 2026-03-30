use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractBoundedIntSolver;
use crate::smt_solver::typed_ast::AstType;
use biodivine_lib_param_bn::{RegulatoryGraph, VariableId};
use log::info;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct RegulatorIsEssential {
    target: VariableId,
    regulator: VariableId,
}

impl RegulatorIsEssential {
    pub fn new(target: VariableId, regulator: VariableId) -> Self {
        Self { target, regulator }
    }

    /// Read all essentiality constraints from a given [`RegulatoryGraph`].
    pub fn read_from(psbn: &RegulatoryGraph) -> Vec<RegulatorIsEssential> {
        psbn.regulations()
            .filter(|it| it.is_observable())
            .map(|it| Self::new(it.target, it.regulator))
            .collect()
    }
}

impl<SOLVER: AbstractBoundedIntSolver + 'static> InferenceConstraint<SOLVER>
    for RegulatorIsEssential
{
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
            "Asserting: regulator `{:?}` is essential in target `{:?}`.",
            self.regulator, self.target
        );
        let target_data = &encoder.problem[self.target];
        let regulator_data = &encoder.problem[self.regulator];
        let argument_index = encoder.problem[self.target]
            .regulator_index(self.regulator)
            .unwrap_or_else(|| unreachable!()); // Must fail during validation.

        let essential_name = format!(
            "essential_{}_{}",
            self.target.to_index(),
            self.regulator.to_index()
        );

        // Create a fresh free atom for each argument.
        let mut args = target_data
            .regulators_iter()
            .map(|reg| {
                encoder.problem[reg]
                    .ast_type()
                    .new_fresh_const(essential_name.as_str())
            })
            .collect::<Vec<_>>();

        // Declare the domains of all newly created arguments:
        for (reg, arg) in target_data.regulators_iter().zip(args.iter()) {
            let reg_data = &encoder.problem[reg];
            if reg_data.is_int() {
                let func = arg.as_dyn_ref().decl();
                solver.declare_int(&func, Some(reg_data.domain))?;
            }
        }

        if regulator_data.ast_type() == AstType::Bool {
            // For Boolean arguments, we can simplify the constraint creation process because
            // we know the argument can only be 0/1. This avoids two free variables.

            // Assert that `update(args[i=0]) != update(args[i=1]])`.
            args[argument_index] = AstType::Bool.new_value(0);
            let call_args =
                encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
            args[argument_index] = AstType::Bool.new_value(1);
            let call_args_prime =
                encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
            solver.assert(&call_args.eq(&call_args_prime)?.not());

            return Ok(());
        }

        let arg_prime = regulator_data
            .ast_type()
            .new_fresh_const(essential_name.as_str());
        if regulator_data.is_int() {
            // If the regulator is `Int`, declare its domain.
            let func = arg_prime.as_dyn_ref().decl();
            solver.declare_int(&func, Some(regulator_data.domain))?;
        }

        // Assert that `update(args) != update(args[i=i_prime]])`.
        let call_args = encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
        args[argument_index] = arg_prime;
        let call_args_prime =
            encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
        solver.assert(&call_args.eq(&call_args_prime)?.not());

        Ok(())
    }
}
