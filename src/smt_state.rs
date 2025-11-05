use biodivine_lib_param_bn::{BooleanNetwork, VariableId};
use std::collections::BTreeMap;
use z3::ast::Bool;

/// Represents a declaration of "some state" that exists in a Boolean network.
///
/// Internally, this means new Boolean SMT variable is declared for every
/// variable in the network.
#[derive(Clone)]
pub struct SmtState {
    name: String,
    variables: Vec<Bool>,
}

impl SmtState {
    /// Build a new [`SmtState`] for a given [`BooleanNetwork`].
    ///
    /// By default, the names of the underlying SMT variables are built from both the
    /// state name and the variable name as `x_{state_name}_{network_variable_name}`.
    pub fn new(name: &str, network: &BooleanNetwork) -> Self {
        Self {
            name: name.to_string(),
            variables: network
                .variables()
                .map(|id| {
                    let var_name = network.get_variable_name(id);
                    Bool::new_const(format!("x_{}_{}", name, var_name))
                })
                .collect(),
        }
    }

    /// Get the name with which the state is declared in the SMT solver.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Make a copy of the underlying SMT variables used to represent this symbolic state.
    ///
    /// See also [`Self::make_smt_var_map`] and [`Self::iter_smt_vars`].
    pub fn make_smt_vars(&self) -> Vec<Bool> {
        self.variables.clone()
    }

    /// Iterate over the SMT variables of this [`SmtState`]. The positions of the
    /// variables should match the corresponding [`VariableId`] in the original [`BooleanNetwork`].
    ///
    /// See also [`Self::make_smt_vars`].
    pub fn iter_smt_vars(&self) -> impl Iterator<Item = Bool> {
        self.variables.iter().cloned()
    }

    /// Make a copy of the underlying SMT variables, indexed by the corresponding [`VariableId`].
    ///
    /// See also [`Self::make_smt_vars`].
    pub fn make_smt_var_map(&self) -> BTreeMap<VariableId, Bool> {
        self.iter_smt_var_map().collect()
    }

    /// Iterate over the pairs of corresponding network variables ([`VariableId`]) and SMT
    /// variables ([`Bool`]).
    ///
    /// See also [`Self::make_smt_var_map`].
    pub fn iter_smt_var_map(&self) -> impl Iterator<Item = (VariableId, Bool)> {
        self.variables
            .iter()
            .enumerate()
            .map(|(i, v)| (VariableId::from_index(i), v.clone()))
    }

    /// Get the SMT variable corresponding to the given BN variable.
    ///
    /// # Panics
    ///
    /// If the given [`VariableId`] is not valid in this state.
    pub fn get_smt_var(&self, var: VariableId) -> Bool {
        self.variables[var.to_index()].clone()
    }

    /// Read the value of this state from a [`z3::Model`].
    pub fn extract_state(&self, model: &z3::Model) -> Vec<bool> {
        self.variables
            .iter()
            .map(|var| {
                let interp = model.get_const_interp(var).unwrap();
                interp.as_bool().unwrap()
            })
            .collect()
    }

    /// Read the value of this state from a [`z3::Model`] and pair the values with the
    /// corresponding network [`VariableId`].
    pub fn extract_state_map(&self, model: &z3::Model) -> BTreeMap<VariableId, bool> {
        self.variables
            .iter()
            .enumerate()
            .map(|(i, var)| {
                let interp = model.get_const_interp(var).unwrap();
                (VariableId::from_index(i), interp.as_bool().unwrap())
            })
            .collect()
    }
}
