use crate::smt_solver::typed_ast::AstType;
use anyhow::anyhow;
use std::collections::HashSet;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{DeclKind, FuncDecl, Model};

/// Extract all uninterpreted function applications from the given expression. The expression is
/// only allowed to use `Int` and `Bool` functions.
///
/// TODO: For now, this is ignoring usages that appear inside quantifiers...
pub fn extract_function_applications(fml: &Bool) -> HashSet<Dynamic> {
    let mut todo = vec![Dynamic::from_ast(fml)];
    let mut results: HashSet<Dynamic> = HashSet::new();
    let mut seen: HashSet<Dynamic> = HashSet::new();

    while let Some(expr) = todo.pop() {
        // Regardless of expression type, we want to explore all child expressions, assuming
        // we have not seen them before.
        if expr.is_app() {
            for child in expr.children() {
                if !seen.contains(&child) {
                    seen.insert(child.clone());
                    todo.push(child);
                }
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

/// Extract all uninterpreted function usages (including zero-arity constants) of type `Int`.
///
/// TODO: For now, this is ignoring usages that appear inside quantifiers...
pub fn extract_int_functions(fml: &Bool) -> HashSet<Int> {
    let mut todo = vec![Dynamic::from_ast(fml)];
    let mut results: HashSet<Int> = HashSet::new();
    let mut seen: HashSet<Dynamic> = HashSet::new();

    while let Some(expr) = todo.pop() {
        // Same as `extract_function_applications`, we want to explore all child expressions.
        if expr.is_app() {
            for child in expr.children() {
                if !seen.contains(&child) {
                    seen.insert(child.clone());
                    todo.push(child);
                }
            }
        }

        // Check if the expression is an uninterpreted function application and has type `Int`:
        if expr.is_app()
            && expr.decl().kind() == DeclKind::UNINTERPRETED
            && let Some(expr) = expr.as_int()
        {
            results.insert(expr);
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

/// Evaluate a [`Dynamic`] expression in the given [`Model`], assuming the expression is
/// either an `Int` or a `Bool`. Subsequently cast the result to `u32`.
pub fn model_eval_int(expr: &Dynamic, model: &Model) -> u32 {
    let result = model.eval(expr, true).expect("Cannot evaluate.");
    if let Some(value) = result.as_bool() {
        u32::from(value.as_bool().unwrap())
    } else if let Some(value) = result.as_int() {
        u32::try_from(value.as_u64().unwrap()).unwrap()
    } else {
        panic!("Function did not evaluate to bool/number.")
    }
}

/// Assume the given expression is an Integer of Boolean uninterpreted function. Evaluate
/// its arguments and the function itself.
pub fn model_eval_int_function(expr: &Dynamic, model: &Model) -> (Vec<u32>, u32) {
    let args = expr
        .children()
        .iter()
        .map(|child| model_eval_int(child, model))
        .collect::<Vec<_>>();

    let output = model_eval_int(expr, model);
    (args, output)
}
