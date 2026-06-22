use crate::bn_inference::constraints::{check_regulator_exists, check_variable_exists};
use crate::bn_inference::{InferenceConstraint, InferenceProblem, InferenceProblemEncoder};
use crate::smt_solver::AbstractBoundedIntSolver;
use crate::smt_solver::typed_ast::AstType;
use anyhow::anyhow;
use biodivine_algo_smt_inference::bn_inference::UpdateFunctionDefinition;
use biodivine_algo_smt_inference::smt_solver::typed_ast::TypedAst;
use biodivine_lib_param_bn::{RegulatoryGraph, VariableId};
use log::info;
use std::collections::HashMap;
use z3::SatResult;
use z3::ast::Bool;

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

        if let UpdateFunctionDefinition::FullySpecified(expression) =
            encoder.update_function(self.target)
        {
            // If the function is fully specified, execute a completely separate solver
            // query to verify that essentiality holds. Under normal circumstances, this
            // query should be very simple to check and should not cause any
            // major performance issues. Subsequently, there is no need to add additional
            // assertions to the main query.

            // Note (1): If the regulators are ints, we consider them true iff they are non-zero.
            // Consequently, we can simply treat them as Boolean when performing this extra
            // solver check, because any non-zero value will produce the same truth value
            // in our fully specified expression.

            // Note (2): Technically, this check is not necessary. The property could be
            // embedded into the main solver query. However, this (a) simplifies the main query
            // when possible and (b) makes the error path consistent with monotonicity errors,
            // failing during encoding if the fully specified expression is inconsistent.

            let arg_prefix = "fully_specified_arg";

            let mut args = target_data
                .regulators_iter()
                .map(|reg| (reg, Bool::fresh_const(arg_prefix)))
                .collect::<HashMap<_, _>>();

            args.insert(self.regulator, Bool::from_bool(false));
            let low = TypedAst::from_fn_update(expression, &args);

            args.insert(self.regulator, Bool::from_bool(true));
            let high = TypedAst::from_fn_update(expression, &args);

            let assertion = low.eq(&high)?.not();

            // Make a new solver, add the assertion, and check that it is satisfiable,
            // i.e., there is an input where flipping the regulator causes a change in output.
            let solver = z3::Solver::new();
            solver.assert(assertion);

            return match solver.check() {
                SatResult::Sat => Ok(()),
                SatResult::Unknown => {
                    unreachable!("Essentiality of fully specified expression is always decidable.")
                }
                SatResult::Unsat => Err(anyhow!(
                    "Essentiality mismatch for regulator `{}` in `{}`",
                    self.regulator,
                    expression
                )),
            };
        }

        // If the function is uninterpreted, build a general query that will be added
        // to the inference constraints.

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
