use crate::smt_solver::typed_ast::{AstType, TypedAst};
use anyhow::anyhow;
use linked_hash_set::LinkedHashSet;
use std::collections::HashSet;
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{DeclKind, FuncDecl, Model};

/// Extract all uninterpreted function applications within unquantified formulas (any
/// usage inside quantifiers is ignored). The expression
/// is only allowed to use `Int` and `Bool` functions.
///
/// Note that this also returns all occurring constants (including state constants),
/// not just update functions, as these are zero-arity function applications.
pub fn extract_function_applications(fml: &Bool) -> LinkedHashSet<Dynamic> {
    let mut todo = vec![Dynamic::from_ast(fml)];
    let mut results: LinkedHashSet<Dynamic> = LinkedHashSet::new();
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
        // save it. Note that constants are also valid function applications (with 0 arguments).
        if expr.is_app() && expr.decl().kind() == DeclKind::Uninterpreted {
            results.insert(expr);
        }
    }

    results
}

/// Extract all uninterpreted function usages (including zero-arity constants) of type `Int`
/// within unquantified formulas (any usage inside quantifiers is ignored).
///
/// Note that this also returns all state constants, not just update functions.
pub fn extract_int_functions(fml: &Bool) -> LinkedHashSet<Int> {
    extract_function_applications(fml)
        .iter()
        .filter_map(|it| it.as_int())
        .collect()
}

/// Extract all usages of a specific uninterpreted function.
///
/// Due to API limitations, the functions are considered equal if they share the same name.
pub fn extract_specific_function_applications(
    fml: &Bool,
    declaration: &FuncDecl,
) -> LinkedHashSet<Dynamic> {
    extract_function_applications(fml)
        .into_iter()
        // `FuncDecl` does not implement `Eq`, but this should be acceptable for now...
        .filter(|it| it.decl().name() == declaration.name())
        .collect()
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

/// Assume the given expression is a function application with `Int`/`Bool` arguments.
/// Evaluate the arguments of this function application and the function itself.
///
/// # Panics
///
/// Fails if the arguments of the expression are not correctly typed or if they do not
/// evaluate to constant values.
pub fn model_eval_int_function(expr: &TypedAst, model: &Model) -> (Vec<u32>, u32) {
    let args = expr
        .typed_children()
        .expect("Precondition violation: Invalid child expressions.")
        .iter()
        .map(|child| {
            child
                .eval_as_constant(model)
                .expect("Precondition violation: Argument AST does not evaluate to a constant.")
        })
        .collect::<Vec<_>>();

    let output = expr
        .eval_as_constant(model)
        .expect("Precondition violation: AST does not evaluate to a constant.");
    (args, output)
}
