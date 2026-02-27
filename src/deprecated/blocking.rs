use crate::deprecated::InferenceProblem;
use z3::Model;
use z3::ast::Bool;

/// Block based on fixed-point state variables.
///
/// Constructs a blocker that prevents the solver from returning the exact same
/// assignments to all Boolean variables in the fixed-point states.
fn generate_fixed_point_blocker(model: &Model, problem: &InferenceProblem) -> Result<Bool, String> {
    let mut eq_atoms: Vec<Bool> = Vec::new();

    // For each state, extract the SMT variable values and create equalities
    for state in problem.get_state_declarations().values() {
        for smt_var in state.make_smt_var_map().values() {
            let val = model
                .get_const_interp(smt_var)
                .ok_or("Failed to extract interpretation from model")?
                .as_bool()
                .ok_or("Failed to convert to bool")?;
            eq_atoms.push(smt_var.iff(Bool::from_bool(val)));
        }
    }

    if eq_atoms.is_empty() {
        return Err("No variables to block".to_string());
    }

    // Create conj of all equalities matching the current model
    // Negate the conjunction to block it
    let constraint = Bool::and(&eq_atoms.iter().collect::<Vec<_>>());
    Ok(constraint.not())
}

/// Block based on interpretation of function symbols.
///
/// Constructs a blocker that prevents the solver from returning the exact same
/// assignments to all uninterpreted function symbols in the model.
fn generate_interpretation_blocker(
    model: &Model,
    problem: &InferenceProblem,
) -> Result<Bool, String> {
    let uninterpreted_symbols = problem.get_uninterpreted_symbols();
    if uninterpreted_symbols.is_empty() {
        return Err("No uninterpreted symbols to block".to_string());
    }

    let mut model_constraint_atoms: Vec<Bool> = Vec::new();
    let bn = problem.get_network();

    // For each function, enumerate all input->output pairs and require they match the model
    for (param_id, func_decl) in uninterpreted_symbols {
        let arity = bn.get_parameter(*param_id).get_arity();

        // Enumerate all 2^arity input combinations
        let max_num = 2u32.pow(arity);
        for input_index in 0..max_num {
            let mut inputs: Vec<Bool> = Vec::new();
            for bit_pos in 0..arity {
                let bit_set = (input_index >> bit_pos) & 1 == 1;
                inputs.push(z3::ast::Bool::from_bool(bit_set));
            }

            let input_refs: Vec<&dyn z3::ast::Ast> =
                inputs.iter().map(|b| b as &dyn z3::ast::Ast).collect();
            let func_app = func_decl.apply(&input_refs);

            // Get the model's value and create an equality constraint
            let model_value = model
                .eval(&func_app, true)
                .ok_or("Failed to evaluate function")?
                .as_bool()
                .ok_or("Function value is not a Bool")?;

            let func_bool = func_app.as_bool().ok_or("Function return is not a Bool")?;

            // Add constraint: f(input) == model_value
            model_constraint_atoms.push(func_bool.iff(model_value));
        }
    }

    if model_constraint_atoms.is_empty() {
        return Err("Could not generate function model constraints".to_string());
    }

    // Create conj of all equalities matching the current model
    // Negate the conjunction to block it
    let constraint = Bool::and(&model_constraint_atoms.iter().collect::<Vec<_>>());
    Ok(constraint.not())
}

/// Block based on a combination of fixed-point states and function symbols.
///
/// Constructs a blocker that prevents the solver from returning the exact same
/// assignments to both state variables and uninterpreted function symbols.
fn generate_combined_blocker(model: &Model, problem: &InferenceProblem) -> Result<Bool, String> {
    let state_blocker = generate_fixed_point_blocker(model, problem)?;
    // TODO: if there are no functions, this would fail - do we want to allow this
    //       and return just the state blocker?
    let func_blocker = generate_interpretation_blocker(model, problem)?;

    Ok(Bool::and(&[&state_blocker, &func_blocker]))
}

pub enum BlockingStrategy {
    FixedPoints,
    Interpretation,
    Combined,
}

impl BlockingStrategy {
    pub fn generate_blocker(
        &self,
        model: &Model,
        problem: &InferenceProblem,
    ) -> Result<Bool, String> {
        match self {
            BlockingStrategy::FixedPoints => generate_fixed_point_blocker(model, problem),
            BlockingStrategy::Interpretation => generate_interpretation_blocker(model, problem),
            BlockingStrategy::Combined => generate_combined_blocker(model, problem),
        }
    }
}
