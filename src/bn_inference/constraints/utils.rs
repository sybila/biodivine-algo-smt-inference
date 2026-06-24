use crate::bn_inference::InferenceProblem;
use crate::bn_inference::inference_problem::VariableData;
use anyhow::anyhow;
use biodivine_lib_param_bn::{ModelAnnotation, VariableId};
use std::collections::{BTreeMap, HashMap};

pub struct ConstraintStrings();

impl ConstraintStrings {
    pub const PRIORITY_CLASS: &str = "priority_class";
    pub const WEIGHT: &str = "weight";
    pub const STATE: &str = "state";
    pub const FIXED_POINT: &str = "fixed_point";
    pub const COMPARISON: &str = "comparison";
    pub const DECLARE: &str = "declare";

    pub const EQUAL: &str = "equal";
    pub const NOT_EQUAL: &str = "not_equal";
    pub const LESS: &str = "less";
    pub const LESS_EQUAL: &str = "less_equal";
    pub const GREATER: &str = "greater";
    pub const GREATER_EQUAL: &str = "greater_equal";
}

/// A helper function which ensures we always go through the model annotations in a sorted order.
pub fn sorted_map(
    annotations: &HashMap<String, ModelAnnotation>,
) -> BTreeMap<&String, &ModelAnnotation> {
    BTreeMap::from_iter(annotations.iter())
}

pub fn check_state_exists<S: 'static>(
    problem: &InferenceProblem<S>,
    state: &str,
) -> Result<(), anyhow::Error> {
    if !problem.has_state(state) {
        anyhow::bail!("State `{state}` not found.");
    }
    Ok(())
}

pub fn check_variable_exists<S: 'static>(
    problem: &InferenceProblem<S>,
    variable: VariableId,
) -> Result<&VariableData, anyhow::Error> {
    problem
        .get_variable(variable)
        .ok_or_else(|| anyhow!("Variable `{:?}` not found.", variable))
}

pub fn check_variable_name_exists<'a, S: 'static>(
    problem: &'a InferenceProblem<S>,
    variable: &str,
) -> Result<&'a VariableData, anyhow::Error> {
    problem
        .find_variable(variable)
        .and_then(|var| problem.get_variable(var))
        .ok_or_else(|| anyhow!("Variable `{variable}` not found."))
}

pub fn check_regulator_exists<S: 'static>(
    problem: &InferenceProblem<S>,
    target: VariableId,
    regulator: VariableId,
) -> Result<(), anyhow::Error> {
    let target_data = check_variable_exists(problem, target)?;
    if target_data.regulator_index(regulator).is_none() {
        anyhow::bail!("Variable `{target:?}` not regulated by `{regulator:?}`");
    }
    Ok(())
}

pub fn check_variable_domain<S: 'static>(
    problem: &InferenceProblem<S>,
    variable: VariableId,
    value: u32,
) -> Result<(), anyhow::Error> {
    let data = check_variable_exists(problem, variable)?;
    if value < data.domain.0 || value > data.domain.1 {
        anyhow::bail!(
            "Value `{value}` not valid for domain `[{},{}]` of variable `{variable:?}`.",
            data.domain.0,
            data.domain.1
        );
    }
    Ok(())
}
