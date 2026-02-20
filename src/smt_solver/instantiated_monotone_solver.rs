use crate::smt_solver::{
    AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver, Monotonicity,
    extract_bool_args, extract_function_applications,
};
use num_rational::BigRational;
use std::collections::{BTreeMap, HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic};
use z3::{FuncDecl, Model, SatResult};

type FunctionName = String;

pub struct InstantiatedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
    // Indicates whether assert was called (monotonicity has to be declared before all assertions).
    has_asserted: bool,
    function_info: HashMap<FunctionName, MonotoneFunctionInfo>,
}

/// Stores internal info about monotonicity properties related to one of the uninterpreted
/// functions.
///
/// Currently, this object is only created for functions with at least one monotonic argument.
#[derive(Clone, Default)]
struct MonotoneFunctionInfo {
    name: String,
    // Remembers which function arguments are declared as monotone.
    arguments: BTreeMap<usize, Monotonicity>,
    // Remembers all unique usages of every function.
    occurrences: HashSet<Bool>,
    // Remembers all monotonicity lemmas already asserted for a given function.
    lemmas: Vec<Bool>,
}

impl MonotoneFunctionInfo {
    /// Make a lemma which states that for the two applications of this function,
    /// the argument monotonicity properties stored in this [`MonotoneFunctionInfo`] must hold.
    pub fn mk_monotonicity_lemma(&self, app1: &Bool, app2: &Bool) -> Option<Bool> {
        assert!(app1.is_app());
        assert!(app2.is_app());
        assert_eq!(app1.decl().name(), app2.decl().name());
        assert_eq!(app1.decl().name(), self.name);

        let app1_args = extract_bool_args(app1);
        let app2_args = extract_bool_args(app2);

        let assumptions = app1_args
            .into_iter()
            .zip(app2_args)
            .enumerate()
            .filter(|(_, (arg1, arg2))| *arg1 != *arg2)
            .map(|(i, (arg1, arg2))| {
                match self.arguments.get(&i) {
                    Some(Monotonicity::Positive) => arg1.implies(arg2), // arg1 <= arg2
                    Some(Monotonicity::Negative) => arg2.implies(arg1), // arg2 <= arg1
                    None => arg1.iff(arg2),                             // arg1 == arg2
                }
            })
            .collect::<Vec<_>>();

        if !assumptions.is_empty() {
            Some(Bool::and(&assumptions).implies(app1.implies(app2)))
        } else {
            None
        }
    }
}

impl<INNER: AbstractSolver> InstantiatedMonotoneSolver<INNER> {
    pub fn new(inner: INNER) -> InstantiatedMonotoneSolver<INNER> {
        InstantiatedMonotoneSolver {
            inner,
            has_asserted: false,
            function_info: HashMap::new(),
        }
    }

    fn ensure_function_info(&mut self, f: &FuncDecl) -> &mut MonotoneFunctionInfo {
        self.function_info
            .entry(f.name())
            .or_insert_with_key(|name| MonotoneFunctionInfo {
                name: name.clone(),
                arguments: BTreeMap::new(),
                occurrences: HashSet::new(),
                lemmas: Vec::new(),
            })
    }

    /// This method:
    ///  - Adds all monotonicity lemmas relevant to the given function application, assuming
    ///    these lemmas have not been already added before.
    ///  - Saves the function application for later lemma creation.
    ///  - If the function does not have monotone arguments, nothing happens.
    fn ensure_monotonicity_lemmas_for_application(&mut self, app: &Bool) {
        if let Some(info) = self.function_info.get_mut(&app.decl().name()) {
            if info.occurrences.contains(app) {
                // Don't add new lemmas if this is a known function application.
                return;
            }

            for other_app in info.occurrences.iter() {
                if let Some(lemma) = info.mk_monotonicity_lemma(app, other_app) {
                    self.inner.assert(&lemma);
                    info.lemmas.push(lemma);
                }
                if let Some(lemma) = info.mk_monotonicity_lemma(other_app, app) {
                    self.inner.assert(&lemma);
                    info.lemmas.push(lemma);
                }
            }

            // Save a function application for later lemma creation.
            info.occurrences.insert(app.clone());
        }
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for InstantiatedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        assert!(
            !self.has_asserted,
            "Monotonicity constraint must be declared before all assertions."
        );
        self.ensure_function_info(f)
            .arguments
            .insert(i, Monotonicity::Positive);
        Ok(())
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        assert!(
            !self.has_asserted,
            "Monotonicity constraint must be declared before all assertions."
        );
        self.ensure_function_info(f)
            .arguments
            .insert(i, Monotonicity::Negative);
        Ok(())
    }
}

impl<INNER: AbstractSolver> AbstractSolver for InstantiatedMonotoneSolver<INNER> {
    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.inner.assert(formula);

        for app in extract_function_applications(formula) {
            self.ensure_monotonicity_lemmas_for_application(&app);
        }
    }

    fn check(&self) -> SatResult {
        self.inner.check()
    }

    fn get_model(&self) -> Option<Model> {
        self.inner.get_model()
    }
}

impl<INNER: AbstractOptimizeSolver> AbstractOptimizeSolver for InstantiatedMonotoneSolver<INNER> {
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.has_asserted = true;
        self.inner.assert_soft(formula, weight);

        for app in extract_function_applications(formula) {
            self.ensure_monotonicity_lemmas_for_application(&app);
        }
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_lower(objective_id)
    }

    fn get_upper(&self, objective_id: u32) -> Option<Dynamic> {
        self.inner.get_upper(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.inner.register_model_handler(callback)
    }
}
