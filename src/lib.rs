use crate::expression_generators::fn_update_to_smt;
use biodivine_lib_param_bn::Monotonicity::Activation;
use biodivine_lib_param_bn::{BooleanNetwork, FnUpdate, ParameterId, VariableId};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Not;
use z3::ast::{Bool, forall_const};
use z3::{FuncDecl, Sort};

/// A data structure which defines one state that is supposed to exist in a BN.
mod smt_state;
pub use smt_state::SmtState;

/// Utility methods for generating logical expressions for the SMT solver.
mod expression_generators;

/// A data structure which defines the observed properties of a single BN state.
mod state_specification;
pub use state_specification::StateSpecification;

/// Inference problem defines constraints on Boolean network behavior that can be converted
/// into an SMT query and addressed by a solver (the result being an assignment of the
/// uninterpreted functions for which the network satisfies all requirements).
pub struct InferenceProblem {
    network: BooleanNetwork, // Includes essentiality and monotonicity requirements.
    uninterpreted_symbols: BTreeMap<ParameterId, FuncDecl>,
    state_declarations: BTreeMap<String, SmtState>,
    state_specification: BTreeMap<String, StateSpecification>,
    fixed_points: BTreeSet<String>,
}

impl InferenceProblem {
    /// Create a new inference problem for a partially specified [`BooleanNetwork`].
    ///
    /// # Panics
    ///
    /// The network can only contain explicit uninterpreted functions.
    /// Use [`BooleanNetwork::name_implicit_parameters`] to assign default names to
    /// any "anonymous" update functions.
    pub fn new(network: BooleanNetwork) -> Self {
        // Network can't have "anonymous" uninterpreted functions. You can use
        // [`BooleanNetwork::name_implicit_parameters`] to assign default names
        // to all "anonymous" functions.
        assert_eq!(network.num_implicit_parameters(), 0);

        let bool_sort = Sort::bool();

        let uninterpreted_symbols = network
            .parameters()
            .map(|p| {
                let param = &network[p];
                let arity = usize::try_from(param.get_arity()).unwrap();
                let name = param.get_name().to_string();
                let args = vec![&bool_sort; arity];
                (p, FuncDecl::new(name, &args, &bool_sort))
            })
            .collect::<BTreeMap<_, _>>();

        Self {
            network,
            uninterpreted_symbols,
            state_declarations: BTreeMap::default(),
            state_specification: BTreeMap::default(),
            fixed_points: BTreeSet::default(),
        }
    }

    /// Make a new named [`SmtState`] valid within this [`InferenceProblem`].
    ///
    /// # Panics
    ///
    /// Method fails if a state with the same name already exists in this problem.
    pub fn make_state<S: Into<String>>(&mut self, name: S) -> SmtState {
        let name: String = name.into();
        assert!(!self.state_declarations.contains_key(&name));
        let state = SmtState::new(name.as_str(), &self.network);
        self.state_declarations.insert(name.clone(), state.clone());
        state
    }

    /// Retrieve a reference to one of the name [`SmtState`] instances currently tracked
    /// by this [`InferenceProblem`].
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    ///
    pub fn get_state<S: Into<String>>(&self, name: S) -> &SmtState {
        self.state_declarations.get(&name.into()).unwrap()
    }

    /// Assert that the state referenced by the given `name` is a network fixed-point.
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    pub fn assert_fixed_point<S: Into<String>>(&mut self, name: S) {
        let name: String = name.into();
        assert!(self.state_declarations.contains_key(&name));
        self.fixed_points.insert(name);
    }

    /// Assert that the state referenced by the given `name` must follow the specification
    /// of the given `observation`.
    ///
    /// Note that while the state *must* follow the `observation` specification, the specification
    /// can contain "may" requirements that do not need to be satisfied by every valid model.
    ///
    /// # Panics
    ///
    /// Method fails if such state was not declared using [`Self::make_state`].
    pub fn assert_state_observation<S: Into<String>>(
        &mut self,
        name: S,
        observation: &StateSpecification,
    ) {
        let name: String = name.into();
        assert!(self.state_declarations.contains_key(&name));
        self.state_specification
            .insert(name.clone(), observation.clone());
    }

    /// Build a [`z3::Optimize`] solver instance that implements all prescribed constraints.
    pub fn build_solver(&self) -> z3::Optimize {
        let solver = z3::Optimize::new();

        // First, assert that all state specifications are satisfied:
        for (name, specification) in &self.state_specification {
            let state = self.get_state(name);
            for (bn_var, value) in specification.make_required_assertion_map() {
                let smt_var = state.get_smt_var(bn_var);
                let assertion = if value { smt_var } else { smt_var.not() };
                solver.assert(&assertion);
            }

            for (bn_var, (value, confidence)) in specification.make_optional_assertion_map() {
                let smt_var = state.get_smt_var(bn_var);
                let assertion = if value { smt_var } else { smt_var.not() };
                solver.assert_soft(&assertion, confidence, None);
            }
        }

        // Second, assert that every state that should be a fixed-point is a fixed-point:
        for name in &self.fixed_points {
            let state = self.get_state(name);
            let state_var_map = state.make_smt_var_map();
            for (bn_var, smt_var) in &state_var_map {
                let update = self.get_update_function(*bn_var);
                let smt_update =
                    fn_update_to_smt(update, &state_var_map, &self.uninterpreted_symbols);
                solver.assert(&smt_var.iff(smt_update));
            }
        }

        // Finally, assert that essential/monotonic regulations have their respective properties:
        for reg in self.network.as_graph().regulations() {
            let update = self.get_update_function(reg.target);

            // Technically, both of these declare one extra SMT variable that is not used/needed,
            // but that should not be a big performance issue.

            if reg.observable {
                // Declare a new state `O` for which it holds `update(O[r=0]) != update(O[r=1])`.
                let essential_name =
                    format!("o_{}_{}", reg.regulator.to_index(), reg.target.to_index());
                let smt_state = SmtState::new(essential_name.as_str(), &self.network);
                let mut map = smt_state.make_smt_var_map();
                map.insert(reg.regulator, Bool::from_bool(true));
                let fn_update_reg_true =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);
                map.insert(reg.regulator, Bool::from_bool(false));
                let fn_update_reg_false =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);
                solver.assert(&fn_update_reg_true.iff(fn_update_reg_false).not());
            }

            if let Some(m) = reg.monotonicity {
                // Declare a new state `ACT` or `INH` where for every such state holds that
                // `update(ACT[r=0]) <= update(ACT[r=1])` (symmetrically for `INH`).
                let key = if m == Activation { "act" } else { "inh" };
                let monotonicity_name = format!(
                    "{}_{}_{}",
                    key,
                    reg.regulator.to_index(),
                    reg.target.to_index()
                );
                let smt_state = SmtState::new(monotonicity_name.as_str(), &self.network);
                let mut map = smt_state.make_smt_var_map();
                map.insert(reg.regulator, Bool::from_bool(true));
                let fn_update_reg_true =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);
                map.insert(reg.regulator, Bool::from_bool(false));
                let fn_update_reg_false =
                    fn_update_to_smt(update, &map, &self.uninterpreted_symbols);

                let assertion = if m == Activation {
                    fn_update_reg_false.implies(fn_update_reg_true)
                } else {
                    fn_update_reg_true.implies(fn_update_reg_false)
                };

                solver.assert(&forall_const(
                    &smt_state.make_dyn_smt_vars(),
                    &[],
                    &assertion,
                ));
            }
        }

        solver
    }

    /// Retrieve the internally stored [`FnUpdate`] for the given [`VariableId`], using
    /// the assumption that the network has no anonymous parameters, meaning the update function
    /// cannot be `None`.
    fn get_update_function(&self, bn_var: VariableId) -> &FnUpdate {
        self.network.get_update_function(bn_var).as_ref().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use crate::InferenceProblem;
    use crate::state_specification::StateSpecification;
    use biodivine_lib_param_bn::{BooleanNetwork, VariableId};
    use num_rational::BigRational;
    use num_traits::FromPrimitive;
    use z3::SatResult;

    /// Create a simple fully specified network that has variables `a`, `b`, `c`
    /// and a single fixed-point `010`.
    fn make_one_fixed_point_network() -> (BooleanNetwork, VariableId, VariableId, VariableId) {
        let bn = BooleanNetwork::try_from_bnet(
            r#"
            a, false
            b, true
            c, a & b
        "#,
        )
        .unwrap();
        (
            bn,
            VariableId::from_index(0),
            VariableId::from_index(1),
            VariableId::from_index(2),
        )
    }

    /// Same as [`make_one_fixed_point_network`] but the network has
    /// two fixed-points, `010` and `111`
    fn make_two_fixed_points_network() -> (BooleanNetwork, VariableId, VariableId, VariableId) {
        let bn = BooleanNetwork::try_from_bnet(
            r#"
        a, a
        b, true
        c, a & b
        "#,
        )
        .unwrap();
        (
            bn,
            VariableId::from_index(0),
            VariableId::from_index(1),
            VariableId::from_index(2),
        )
    }

    /// Test that we can find a single fixed-point.
    #[test]
    fn fully_specified_one_fixed_point_must_positive() {
        let (bn, a, b, c) = make_one_fixed_point_network();

        let mut specification = StateSpecification::default();
        specification.assert_must(a, false);
        specification.assert_must(b, true);
        specification.assert_must(c, false);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix = problem.make_state("fix");
        problem.assert_fixed_point("fix");
        problem.assert_state_observation("fix", &specification);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert_eq!(fix.extract_state(&model), vec![false, true, false]);
    }

    /// Test that we can detect that a fixed-point does not exist.
    #[test]
    fn fully_specified_one_fixed_point_must_negative() {
        let (bn, a, b, c) = make_one_fixed_point_network();

        let mut specification = StateSpecification::default();
        specification.assert_must(a, true);
        specification.assert_must(b, true);
        specification.assert_must(c, false);

        let mut problem = InferenceProblem::new(bn.clone());
        let _fix = problem.make_state("fix");
        problem.assert_fixed_point("fix");
        problem.assert_state_observation("fix", &specification);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Unsat);
    }

    /// Test that we can detect a fixed-point (010) within distance one of specification (110).
    #[test]
    fn fully_specified_one_fixed_point_may() {
        let (bn, a, b, c) = make_one_fixed_point_network();

        let one_half = BigRational::from_f32(0.5).unwrap();
        let mut specification = StateSpecification::default();
        specification.assert_may(a, true, &one_half);
        specification.assert_may(b, true, &one_half);
        specification.assert_may(c, false, &one_half);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix = problem.make_state("fix");
        problem.assert_fixed_point("fix");
        problem.assert_state_observation("fix", &specification);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        // Note that a=0, even though specification requires a=1.
        assert_eq!(fix.extract_state(&model), vec![false, true, false]);
    }

    /// Test that we can find two distinct fixed-points.
    #[test]
    fn fully_specified_two_fixed_point_must_positive() {
        let (bn, a, b, c) = make_two_fixed_points_network();

        let mut spec_one = StateSpecification::default();
        spec_one.assert_must(a, false);
        spec_one.assert_must(b, true);
        spec_one.assert_must(c, false);

        let mut spec_two = StateSpecification::default();
        spec_two.assert_must(a, true);
        spec_two.assert_must(b, true);
        spec_two.assert_must(c, true);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix_one = problem.make_state("fix-1");
        let fix_two = problem.make_state("fix-2");
        problem.assert_fixed_point("fix-1");
        problem.assert_fixed_point("fix-2");
        problem.assert_state_observation("fix-1", &spec_one);
        problem.assert_state_observation("fix-2", &spec_two);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert_eq!(fix_one.extract_state(&model), vec![false, true, false]);
        assert_eq!(fix_two.extract_state(&model), vec![true, true, true]);
    }

    // Test that we can detect two fixed points (010 and 111) within distance one and two
    // of a specification (000 and 101).
    #[test]
    fn fully_specified_two_fixed_point_may() {
        let (bn, a, b, c) = make_two_fixed_points_network();

        let one_half = BigRational::from_f32(0.5).unwrap();
        let mut spec_one = StateSpecification::default();
        spec_one.assert_may(a, false, &one_half);
        spec_one.assert_may(b, false, &one_half);
        spec_one.assert_may(c, false, &one_half);

        let mut spec_two = StateSpecification::default();
        spec_two.assert_may(a, true, &one_half);
        spec_two.assert_may(b, false, &one_half);
        spec_two.assert_may(c, true, &one_half);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix_one = problem.make_state("fix-1");
        let fix_two = problem.make_state("fix-2");
        problem.assert_fixed_point("fix-1");
        problem.assert_fixed_point("fix-2");
        problem.assert_state_observation("fix-1", &spec_one);
        problem.assert_state_observation("fix-2", &spec_two);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert_eq!(fix_one.extract_state(&model), vec![false, true, false]);
        assert_eq!(fix_two.extract_state(&model), vec![true, true, true]);
    }

    /// Test that we can detect one fixed-point out of two (010 and 111) within distance
    /// two of specification (001) where the final fixed-point is determined by
    /// specification weights.
    #[test]
    fn fully_specified_one_in_two_fixed_point_optimize() {
        let (bn, a, b, c) = make_two_fixed_points_network();

        // 0.25 + 0.25 < 0.66 + 0.25
        let two_over_three = BigRational::from_f32(0.66).unwrap();
        let one_over_four = BigRational::from_f32(0.25).unwrap();

        // First, build the specification such that `010` is the optimal fixed-point.
        let mut specification = StateSpecification::default();
        specification.assert_may(a, false, &two_over_three);
        specification.assert_may(b, false, &one_over_four);
        specification.assert_may(c, true, &one_over_four);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix = problem.make_state("fix");
        problem.assert_fixed_point("fix");
        problem.assert_state_observation("fix", &specification);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert_eq!(fix.extract_state(&model), vec![false, true, false]);

        // Second, rebuild the specification to prefer `111`.
        let mut specification = StateSpecification::default();
        specification.assert_may(a, false, &one_over_four);
        specification.assert_may(b, false, &one_over_four);
        specification.assert_may(c, true, &two_over_three);

        let mut problem = InferenceProblem::new(bn.clone());
        let fix = problem.make_state("fix");
        problem.assert_fixed_point("fix");
        problem.assert_state_observation("fix", &specification);

        let solver = problem.build_solver();
        assert_eq!(solver.check(&[]), SatResult::Sat);
        let model = solver.get_model().unwrap();
        assert_eq!(fix.extract_state(&model), vec![true, true, true]);
    }
}
