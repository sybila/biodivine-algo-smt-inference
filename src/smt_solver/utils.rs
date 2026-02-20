use crate::smt_solver::typed_ast::AstType;
use anyhow::anyhow;
use std::collections::HashSet;
use z3::ast::{Ast, Bool, Dynamic};
use z3::{DeclKind, FuncDecl};

/// Extract all uninterpreted function applications from the given expression. The expression is
/// only allowed to use `Int` and `Bool` functions.
pub fn extract_function_applications(fml: &Bool) -> HashSet<Dynamic> {
    let mut todo = vec![Dynamic::from_ast(fml)];
    let mut results: HashSet<Dynamic> = HashSet::new();
    let mut seen: HashSet<Dynamic> = HashSet::new();

    while let Some(expr) = todo.pop() {
        // Regardless of expression type, we want to explore all child expressions, assuming
        // we have not seen them before.
        for child in expr.children() {
            if !seen.contains(&child) {
                seen.insert(child.clone());
                todo.push(child);
            }
        }

        // Check if the expression is a non-trivial uninterpreted function application, and if so,
        // save it.
        if expr.num_children() > 0 && expr.is_app() && expr.decl().kind() == DeclKind::UNINTERPRETED
        {
            results.insert(expr.clone());
        }
    }

    results
}

/// Extract the type signature of the given `function`, assuming it only has [`AstType`] arguments
/// and output.
pub fn extract_function_type_signature(
    function: &FuncDecl,
) -> Result<(Vec<AstType>, AstType), anyhow::Error> {
    let args = (0..function.arity())
        .map(|i| AstType::try_from(function.domain(i).unwrap()))
        .collect::<Result<Vec<_>, anyhow::Error>>()
        .map_err(|err| {
            anyhow!(
                "Function {:?} has invalid argument type ({}).",
                function,
                err
            )
        })?;
    let out = AstType::try_from(function.range())
        .map_err(|err| anyhow!("Function {:?} has invalid return type ({}).", function, err))?;
    Ok((args, out))
}
