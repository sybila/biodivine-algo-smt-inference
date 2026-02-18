use std::collections::HashSet;
use z3::DeclKind;
use z3::ast::{Ast, Bool};

/// Convert `Bool` arguments into dynamic references (required by some Z3 APIs).
pub fn make_dyn_vec(asts: &[Bool]) -> Vec<&dyn Ast> {
    asts.iter().map(|it| it as &dyn Ast).collect()
}

/// Assume the given argument is a function application; extract and convert all its arguments
/// to `Bool`. Panics if any of these assumptions fails.
pub fn extract_bool_args<T: Ast>(e: &T) -> Vec<Bool> {
    assert!(e.is_app(), "Must be a function application.");
    e.children()
        .iter()
        .map(|it| it.as_bool().expect("Argument is not of type `Bool`."))
        .collect()
}

/// Extract all applications of *Boolean* functions from the given expression.
pub fn extract_function_applications(fml: &Bool) -> HashSet<Bool> {
    let mut todo = vec![fml.clone()];
    let mut res: HashSet<Bool> = HashSet::new();
    let mut seen: HashSet<Bool> = HashSet::new();

    while let Some(cur) = todo.pop() {
        if !cur.is_app() {
            continue;
        }

        match cur.decl().kind() {
            DeclKind::UNINTERPRETED => {
                if cur.num_children() > 0 {
                    res.insert(cur.clone());
                }
            }
            DeclKind::TRUE | DeclKind::FALSE => {}
            DeclKind::EQ
            | DeclKind::AND
            | DeclKind::OR
            | DeclKind::NOT
            | DeclKind::IFF
            | DeclKind::IMPLIES => {
                for child in cur.children() {
                    let bool_child = child.as_bool().unwrap();
                    if !seen.contains(&bool_child) {
                        seen.insert(bool_child.clone());
                        todo.push(bool_child);
                    }
                }
            }
            _ => panic!("Unsupported {}", cur),
        }
    }

    res
}
