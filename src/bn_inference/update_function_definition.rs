use crate::smt_solver::AbstractSolver;
use biodivine_algo_smt_inference::bn_inference::InferenceProblem;
use biodivine_lib_param_bn::{FnUpdate, VariableId};
use z3::FuncDecl;

/// In an [`InferenceProblem`], an update function can be either
/// uninterpreted (given by an unknown symbol), or fully specified (given by a fully known
/// expression).
#[derive(Debug)]
pub enum UpdateFunctionDefinition {
    Uninterpreted(FuncDecl),
    FullySpecified(FnUpdate),
}

impl UpdateFunctionDefinition {
    /// Build a new [`UpdateFunctionDefinition`] for the given `variable` using data stored
    /// in the provided [`InferenceProblem`].
    ///
    /// If [`VariableData::update_expression`] is set, create a fully specified function;
    /// otherwise create an uninterpreted function. Note that the naming of uninterpreted functions
    /// is deterministic, i.e., calling this method multiple times with the same `problem` and
    /// `variable` produces equivalent uninterpreted function declaration.
    pub fn from_variable_data<SOLVER: AbstractSolver + 'static>(
        problem: &InferenceProblem<SOLVER>,
        variable: VariableId,
    ) -> UpdateFunctionDefinition {
        let var_data = &problem[variable];
        if let Some(expression) = var_data.update_expression() {
            UpdateFunctionDefinition::FullySpecified(expression.clone())
        } else {
            let name = format!("update_{}", variable.to_index());
            let range = problem[variable].sort();

            let regulators = &problem[variable].regulators;
            let domain = regulators
                .iter()
                .map(|it| problem[*it].sort())
                .collect::<Vec<_>>();

            let fun = FuncDecl::new(name, &Vec::from_iter(domain.iter()), &range);
            UpdateFunctionDefinition::Uninterpreted(fun)
        }
    }

    pub fn as_uninterpreted(&self) -> Option<&FuncDecl> {
        if let UpdateFunctionDefinition::Uninterpreted(func) = self {
            Some(func)
        } else {
            None
        }
    }

    pub fn as_fully_specified(&self) -> Option<&FnUpdate> {
        if let UpdateFunctionDefinition::FullySpecified(fun) = self {
            Some(fun)
        } else {
            None
        }
    }
}
