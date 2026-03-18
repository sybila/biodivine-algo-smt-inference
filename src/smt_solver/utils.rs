use crate::smt_solver::AbstractSolver;
use crate::smt_solver::typed_ast::{AstType, TypedAst};
use anyhow::anyhow;
use linked_hash_set::LinkedHashSet;
use std::collections::{BTreeMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic, Int};
use z3::{DeclKind, FuncDecl, Model};

/// Extract all uninterpreted function applications from the given expression. The expression is
/// only allowed to use `Int` and `Bool` functions.
///
/// TODO: For now, this is ignoring usages that appear inside quantifiers...
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
        // save it.
        if expr.is_app() && expr.decl().kind() == DeclKind::UNINTERPRETED {
            results.insert(expr);
        }
    }

    results
}

/// Extract all uninterpreted function usages (including zero-arity constants) of type `Int`.
///
/// TODO: For now, this is ignoring usages that appear inside quantifiers...
pub fn extract_int_functions(fml: &Bool) -> LinkedHashSet<Int> {
    let mut todo = vec![Dynamic::from_ast(fml)];
    let mut results: LinkedHashSet<Int> = LinkedHashSet::new();
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

        // Check if the expression is an uninterpreted function application and has the type `Int`:
        if expr.is_app()
            && expr.decl().kind() == DeclKind::UNINTERPRETED
            && let Some(expr) = expr.as_int()
        {
            results.insert(expr);
        }
    }

    results
}

/// Extract all uninterpreted function usages from all asserted expressions. The expressions
/// are only allowed to use `Int` and `Bool` functions. Only unique expressions are returned,
/// and expressions of each function are sorted for determinism.
///
/// This uses [extract_function_applications] internally to process each assertion.
pub fn collect_asserted_fn_calls<SOLVER: AbstractSolver>(
    solver: &SOLVER,
) -> BTreeMap<String, Vec<Dynamic>> {
    // Collect the fn calls into `HashSet`s at first to only get unique ones
    let mut func_calls_hash: BTreeMap<String, HashSet<Dynamic>> = BTreeMap::new();
    for assertion in solver.get_assertions() {
        for func_call in extract_function_applications(&assertion) {
            func_calls_hash
                .entry(func_call.decl().name())
                .or_default()
                .insert(func_call);
        }
    }

    // Convert the `HashSet`s to sorted vectors for determinism
    func_calls_hash
        .into_iter()
        .map(|(name, set)| {
            let mut v: Vec<Dynamic> = set.into_iter().collect();
            v.sort_by_key(|call| call.to_string());
            (name, v)
        })
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

/// Assume the given expression is an Integer of Boolean uninterpreted function. Evaluate
/// its arguments in the model and substitute the constants into the function call.
///
/// For instance, for expr `f(x_1, x_2)` and model assigning `x_1` -> `1` and `x_2` -> `3`,
/// return substituted expr `f(1, 3)`.
pub fn model_substitute_args_int_function(expr: &Dynamic, model: &Model) -> Dynamic {
    let args = expr
        .children()
        .iter()
        .map(|child| {
            let model_value = model.eval(child, true).expect("Cannot evaluate.");
            TypedAst::try_from(model_value).unwrap()
        })
        .collect::<Vec<_>>();

    let input_refs: Vec<&dyn z3::ast::Ast> = args.iter().map(|b| b.as_dyn_ref()).collect();
    let func_decl = expr.decl();
    func_decl.apply(&input_refs)
}
