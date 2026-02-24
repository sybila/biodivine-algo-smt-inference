use crate::smt_solver::typed_ast::{AstType, TypedAst};
use crate::smt_solver::{
    AbstractBoundedIntSolver, AbstractMonotoneSolver, AbstractOptimizeSolver, AbstractSolver,
    Monotonicity, extract_function_applications, extract_function_type_signature,
};
use anyhow::anyhow;
use num_rational::BigRational;
use std::collections::{BTreeMap, HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic};
use z3::{FuncDecl, Model, SatResult};

type FunctionName = String;

pub struct InstantiatedMonotoneSolver<INNER: AbstractSolver> {
    inner: INNER,
    // Indicates whether assert was called (monotonicity has to be declared before all assertions).
    has_asserted: bool,
    function_info: HashMap<FunctionName, FunctionMonotonicityData>,
}

/// Stores internal info about monotonicity properties related to one of the uninterpreted
/// functions.
///
/// Currently, this object is only created for functions with at least one monotonic argument,
/// meaning you can generally assume that `arguments` is not empty.
#[derive(Clone)]
struct FunctionMonotonicityData {
    name: FunctionName,
    // Type signature of the function.
    signature: (Vec<AstType>, AstType),
    // Stores function arguments that are declared as monotone.
    arguments: BTreeMap<usize, Monotonicity>,
    // Stores all unique usages of every function (should all be the same type).
    occurrences: HashSet<TypedAst>,
    // Remembers all monotonicity lemmas already asserted for a given function.
    lemmas: Vec<Bool>,
}

impl FunctionMonotonicityData {
    /// Make a lemma which states that for the two applications of this function,
    /// the argument monotonicity properties stored in this [`FunctionMonotonicityData`] must hold.
    pub fn mk_monotonicity_lemma(&self, app1: &TypedAst, app2: &TypedAst) -> Option<Bool> {
        assert!(app1.as_dyn_ref().is_app());
        assert!(app2.as_dyn_ref().is_app());
        assert_eq!(
            app1.as_dyn_ref().decl().name(),
            app2.as_dyn_ref().decl().name()
        );
        assert_eq!(app1.as_dyn_ref().decl().name(), self.name);

        let app1_args = app1.as_dyn_ref().children();
        let app2_args = app2.as_dyn_ref().children();

        let assumptions = app1_args
            .into_iter()
            .zip(app2_args)
            .zip(self.signature.0.iter())
            .enumerate()
            .filter(|(_, ((arg1, arg2), _))| *arg1 != *arg2)
            .map(|(i, ((arg1, arg2), tt))| {
                let arg1 = TypedAst::cast_dynamic(*tt, arg1);
                let arg2 = TypedAst::cast_dynamic(*tt, arg2);
                match self.arguments.get(&i) {
                    Some(Monotonicity::Positive) => arg1.le(&arg2), // arg1 <= arg2
                    Some(Monotonicity::Negative) => arg2.le(&arg1), // arg1 >= arg2
                    None => arg1.eq(&arg2),                         // arg1 == arg2
                }
                .unwrap_or_else(|_| unreachable!("`arg1` and `arg2` always have the same type"))
            })
            .collect::<Vec<_>>();

        if !assumptions.is_empty() {
            let comparison = app1.le(app2).unwrap_or_else(|_e| {
                unreachable!("`app1` and `app2` always have the same type.");
            });

            Some(Bool::and(&assumptions).implies(&comparison))
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

    pub fn count_used_lemmas(&self) -> usize {
        let mut total = 0;
        for v in self.function_info.values() {
            total += v.lemmas.len();
        }
        total
    }

    fn set_monotonicity(
        &mut self,
        f: &FuncDecl,
        i: usize,
        monotonicity: Monotonicity,
    ) -> Result<(), anyhow::Error> {
        if self.has_asserted {
            return Err(anyhow!(
                "Monotonicity constraint must be declared before all assertions."
            ));
        }

        if i >= f.arity() {
            return Err(anyhow!(
                "Argument `{}` not valid for function with arity `{}`.",
                i,
                f.arity()
            ));
        }

        self.ensure_function_info(f)?
            .arguments
            .insert(i, monotonicity);
        Ok(())
    }

    fn ensure_function_info(
        &mut self,
        f: &FuncDecl,
    ) -> Result<&mut FunctionMonotonicityData, anyhow::Error> {
        let (domain, range) = extract_function_type_signature(f)?;

        Ok(self
            .function_info
            .entry(f.name())
            .or_insert_with_key(|name| FunctionMonotonicityData {
                name: name.clone(),
                signature: (domain, range),
                arguments: BTreeMap::new(),
                occurrences: HashSet::new(),
                lemmas: Vec::new(),
            }))
    }

    /// This method:
    ///  - Adds all monotonicity lemmas relevant to the given function application, assuming
    ///    these lemmas have not been already added before.
    ///  - Saves the function application for later lemma creation.
    ///  - If the function does not have monotone arguments, nothing happens.
    fn ensure_monotonicity_lemmas_for_application(&mut self, app: Dynamic) {
        assert!(app.is_app());

        if let Some(info) = self.function_info.get_mut(&app.decl().name()) {
            let app = TypedAst::try_from(app).expect(
                "Correctness violation: `function_info` admits function with invalid type.",
            );

            if info.occurrences.contains(&app) {
                // Don't add new lemmas if this is a known function application.
                return;
            }

            for other_app in info.occurrences.iter() {
                if let Some(lemma) = info.mk_monotonicity_lemma(&app, other_app) {
                    self.inner.assert(&lemma);
                    info.lemmas.push(lemma);
                }
                if let Some(lemma) = info.mk_monotonicity_lemma(other_app, &app) {
                    self.inner.assert(&lemma);
                    info.lemmas.push(lemma);
                }
            }

            // Save a function application for later lemma creation.
            info.occurrences.insert(app);
        }
    }
}

impl<INNER: AbstractSolver> AbstractMonotoneSolver for InstantiatedMonotoneSolver<INNER> {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Positive)
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) -> Result<(), anyhow::Error> {
        self.set_monotonicity(f, i, Monotonicity::Negative)
    }
}

impl<INNER: AbstractSolver> AbstractSolver for InstantiatedMonotoneSolver<INNER> {
    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.inner.assert(formula);

        for app in extract_function_applications(formula) {
            self.ensure_monotonicity_lemmas_for_application(app);
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
            self.ensure_monotonicity_lemmas_for_application(app);
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

impl<INNER: AbstractBoundedIntSolver> AbstractBoundedIntSolver
    for InstantiatedMonotoneSolver<INNER>
{
    fn declare_int(
        &mut self,
        f: &FuncDecl,
        domain: Option<(u32, u32)>,
    ) -> Result<(), anyhow::Error> {
        self.inner.declare_int(f, domain)
    }
}
