use crate::bn_inference::InferenceProblem;
use crate::bn_inference::inference_problem::VariableData;
use anyhow::anyhow;
use biodivine_lib_param_bn::VariableId;

pub fn check_state_exists<S: 'static>(
    problem: &InferenceProblem<S>,
    state: &str,
) -> Result<(), anyhow::Error> {
    if !problem.has_state(state) {
        return Err(anyhow!("State `{}` not found.", state));
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

pub fn check_regulator_exists<S: 'static>(
    problem: &InferenceProblem<S>,
    target: VariableId,
    regulator: VariableId,
) -> Result<(), anyhow::Error> {
    let target_data = check_variable_exists(problem, target)?;
    if target_data.regulator_index(regulator).is_none() {
        return Err(anyhow!(
            "Variable `{target:?}` not regulated by `{regulator:?}`"
        ));
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
        return Err(anyhow!(
            "Value `{value}` not valid for domain `[{},{}]` of variable `{variable:?}`.",
            data.domain.0,
            data.domain.1
        ));
    }
    Ok(())
}

pub fn check_state_observation<S: 'static>(
    problem: &InferenceProblem<S>,
    observation: impl Iterator<Item = (VariableId, u32)>,
) -> Result<(), anyhow::Error> {
    for (variable, observation) in observation {
        check_variable_domain(problem, variable, observation)?;
    }
    Ok(())
}
