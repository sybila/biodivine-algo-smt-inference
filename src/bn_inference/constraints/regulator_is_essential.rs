use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractMonotoneSolver;
use crate::smt_solver::typed_ast::AstType;
use biodivine_lib_param_bn::VariableId;

pub struct RegulatorIsEssential {
    target: VariableId,
    regulator: VariableId,
}

impl RegulatorIsEssential {
    pub fn new(target: VariableId, regulator: VariableId) -> Self {
        Self { target, regulator }
    }
}

impl<SOLVER: AbstractMonotoneSolver + 'static> InferenceConstraint<SOLVER>
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
        }

        // Assert that `update(args) != update(args[i=i_prime]])`.
        let call_args = encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
        let i_prime = regulator_data
            .ast_type()
            .new_fresh_const(essential_name.as_str());
        args[argument_index] = i_prime;
        let call_args_prime =
            encoder.mk_update_function_call(self.target, &Vec::from_iter(args.iter()));
        solver.assert(&call_args.eq(&call_args_prime)?.not());

        Ok(())
    }
}
