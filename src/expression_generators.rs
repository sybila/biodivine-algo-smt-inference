use biodivine_lib_param_bn::{BinaryOp, FnUpdate, ParameterId, VariableId};
use std::collections::BTreeMap;
use z3::FuncDecl;
use z3::ast::{Ast, Bool};

/// Take a [`FnUpdate`] and turn it into an [`Bool`] SMT expression.
/// All network variable and uninterpreted function symbols must be provided.
pub fn fn_update_to_smt(
    update: &FnUpdate,
    variables: &BTreeMap<VariableId, Bool>,
    functions: &BTreeMap<ParameterId, FuncDecl>,
) -> Bool {
    match update {
        FnUpdate::Const(value) => Bool::from_bool(*value),
        FnUpdate::Var(id) => variables
            .get(id)
            .cloned()
            .expect("Encountered invalid variable id."),
        FnUpdate::Param(id, args) => {
            let args = args
                .iter()
                .map(|it| fn_update_to_smt(it, variables, functions))
                .collect::<Vec<_>>();
            let fun = functions
                .get(id)
                .expect("Encountered invalid parameter id.");
            let args_ref: Vec<&dyn Ast> = args.iter().map(|it| it as &dyn Ast).collect::<Vec<_>>();
            fun.apply(&args_ref)
                .as_bool()
                .expect("Parameter function has invalid type.")
        }
        FnUpdate::Not(inner) => fn_update_to_smt(inner, variables, functions).not(),
        FnUpdate::Binary(op, l, r) => {
            let l = fn_update_to_smt(l, variables, functions);
            let r = fn_update_to_smt(r, variables, functions);
            match op {
                BinaryOp::And => l & r,
                BinaryOp::Or => l | r,
                BinaryOp::Xor => l ^ r,
                BinaryOp::Iff => l.eq(r),
                BinaryOp::Imp => l.implies(r),
            }
        }
    }
}
