use num_rational::BigRational;
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic, forall_const};
use z3::{DeclKind, FuncDecl, Model, SatResult};

use crate::{DNF, DNFClause, LiteralValue};

#[derive(Debug, PartialEq, Eq, Clone)]
/// Represents whether a function input is positively or negatively monotone
pub enum Monotonicity {
    Positive,
    Negative,
}

/// Interface for SMT solvers that handle monotonicity constraints on uninterpreted functions
pub trait MonotoneSMTSolver {
    /// Set input on index i for fn f as positively monotone.
    fn set_monotone(&mut self, f: &FuncDecl, i: usize);

    /// Set input on index i for fn f as negatively monotone.
    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize);

    /// Soft weighted optimization assertion.
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational);

    /// Hard satisfiability assertion.
    fn assert(&mut self, formula: &Bool);

    /// Check if the querry is satisfiable.
    fn check(&self) -> SatResult;

    /// Get the model for the last [Self::check] (if a model was found).
    fn get_model(&self) -> Option<Model>;

    /// Get lower bound value or approximation for the given optimization objective.
    fn get_lower(&self, objective_id: u32) -> Option<Dynamic>;

    /// Add a model handler that will be invoked for each model improvement produced
    /// by the optimizer.
    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>);

    fn set_verbose(&mut self);

    /// Downcast into InstantiationMonotoneSMTSolver if the solver implements
    /// the sub-trait as well.
    fn as_instantiation_solver(&self) -> Option<&dyn InstantiationMonotoneSMTSolver> {
        None
    }
}

pub trait InstantiationMonotoneSMTSolver: MonotoneSMTSolver {
    /// Getter for all collected monotonicities.
    fn get_all_monotonicity_defs(
        &self,
    ) -> &HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>;

    /// Get monotonicity of a particular function wrt. to its arg on given index.
    fn get_monotonicity_def(&self, fn_id: &FuncDeclIdentifier, idx: usize) -> Option<Monotonicity> {
        self.get_all_monotonicity_defs()
            .get(fn_id)
            .and_then(|defs| defs.get(&idx).cloned())
    }

    /// Getter for collected function occurances in all asserted formulas.
    fn get_collected_fn_occurences(&self) -> &HashMap<FuncDeclIdentifier, HashSet<FunctionApp>>;

    /// Make the intepretations of functions extracted from the model fully satisfy all
    /// monotonicity constraints.
    ///
    /// For now, this just returns a mapping "fn_id" -> "dnf string expression". The args in
    /// the dnf expressions are simply named x_0, x_1, ... (must be renamed before used in a BN).
    ///
    /// TODO: There are lots inefficiencies in this prototype, gotta refactor it once it is working.
    fn repair_monotonicity(&self, model: &Model) -> HashMap<FuncDeclIdentifier, String> {
        let mut monotone_fn_expressions = HashMap::new();
        for (fn_id, fn_apps) in self.get_collected_fn_occurences() {
            // Evaluate the fn applications and collect table rows with output 1 (to build 'dnf')
            let mut fixed_table_rows_1 = HashSet::new();

            for fn_app in fn_apps {
                let fn_output = model
                    .eval(&fn_app.full_app, true)
                    .unwrap()
                    .as_bool()
                    .unwrap();
                if fn_output {
                    let evaluated_args: Vec<bool> = fn_app
                        .args
                        .iter()
                        .map(|arg| model.eval(arg, true).unwrap().as_bool().unwrap())
                        .collect();
                    fixed_table_rows_1.insert(evaluated_args);
                }
            }

            if fixed_table_rows_1.is_empty() {
                monotone_fn_expressions.insert(fn_id.clone(), "false".to_string());
                continue;
            }

            let dnf = DNF::from_positive_table_rows(&fixed_table_rows_1);
            let arity = dnf.get_arity();

            // Now go over the clauses and modify them make the function monotone
            // Some clauses may have become the same, so we use HashSet
            let mut unique_dnf_clauses: HashSet<DNFClause> = HashSet::new();
            for clause in &dnf.clauses {
                let mut modified_clause = clause.clone();
                for (i, literal) in clause.literals.iter().enumerate() {
                    let monotonicity = self.get_monotonicity_def(fn_id, i);

                    // If activator is present as positive literal, or inhibitor as negative literal,
                    // remove it from the clause
                    if (matches!(monotonicity, Some(Monotonicity::Positive)) && literal.is_neg())
                        || (matches!(monotonicity, Some(Monotonicity::Negative))
                            && literal.is_pos())
                    {
                        modified_clause.literals[i] = LiteralValue::Missing;
                    }
                }
                unique_dnf_clauses.insert(modified_clause);
            }

            let unique_clauses_dnf = DNF::new(unique_dnf_clauses);
            let var_names: Vec<String> = (0..arity).map(|i| format!("x_{}", i)).collect();
            let expression = unique_clauses_dnf.create_dnf_expression(&var_names);

            monotone_fn_expressions.insert(fn_id.clone(), expression.to_string());
        }
        monotone_fn_expressions
    }

    /// Count current collected function applications (summed over all uninterpreted
    /// functions).
    fn count_fn_occurances(&self) -> usize {
        self.get_collected_fn_occurences()
            .values()
            .map(|apps| apps.len())
            .sum()
    }
}

/// SMT solver that uses quantified (forall) constraints to encode monotonicity properties
pub struct QuantifiedMonotoneSMTSolver {
    smt_solver: z3::Optimize,
    verbose: bool,
}

/// Helper to convert Boolean ASTs to dynamic AST references
fn make_dyn_vec(asts: &[Bool]) -> Vec<&dyn Ast> {
    asts.iter().map(|it| it as &dyn Ast).collect()
}

impl QuantifiedMonotoneSMTSolver {
    pub fn new() -> Self {
        // Gets rid of the "WARNING: optimization with quantified constraints is not supported"
        // Feel free to comment it out if needed.
        z3::set_global_param("warning", "false");

        QuantifiedMonotoneSMTSolver {
            smt_solver: z3::Optimize::new(),
            verbose: false,
        }
    }

    /// Creates a universal quantification constraint that enforces monotonicity.
    /// For positive monotonicity: false implies true in argument i => output is monotone increasing
    /// For negative monotonicity: true implies false in argument i => output is monotone decreasing
    fn get_monotonicity_constraint(&self, f: &FuncDecl, i: usize, is_positive: bool) -> Bool {
        let vars: Vec<_> = (0..f.arity())
            .map(|i| Bool::new_const(format!("arg_{}", i)))
            .collect();
        let mut args = vars.clone();

        args[i] = Bool::from_bool(true);
        let f_with_true = f.apply(&make_dyn_vec(&args)).as_bool().unwrap();

        args[i] = Bool::from_bool(false);
        let f_with_false = f.apply(&make_dyn_vec(&args)).as_bool().unwrap();

        let body = if is_positive {
            f_with_false.implies(f_with_true)
        } else {
            f_with_true.implies(f_with_false)
        };

        forall_const(&make_dyn_vec(&vars), &[], &body)
    }
}

impl MonotoneSMTSolver for QuantifiedMonotoneSMTSolver {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) {
        self.assert(&self.get_monotonicity_constraint(f, i, true));
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) {
        self.assert(&self.get_monotonicity_constraint(f, i, false));
    }

    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.smt_solver.assert_soft(formula, weight, None);
    }

    fn assert(&mut self, formula: &Bool) {
        self.smt_solver.assert(formula);
    }

    fn check(&self) -> SatResult {
        let res = self.smt_solver.check(&[]);
        if self.verbose {
            println!("{:?}", self.smt_solver.get_statistics());
        }
        res
    }

    fn get_model(&self) -> Option<Model> {
        self.smt_solver.get_model()
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.smt_solver.get_lower(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.smt_solver.register_model_handler(callback);
    }

    fn set_verbose(&mut self) {
        self.verbose = true;
    }
}

impl Default for QuantifiedMonotoneSMTSolver {
    fn default() -> Self {
        Self::new()
    }
}

type FuncDeclIdentifier = String;

/// SMT solver using instantiated monotonicity lemmas. Instead of universal quantification,
/// it creates specific implications between function applications that differ only in inputs
/// where monotonicity is defined. Lemmas are added as constraints are asserted.
pub struct FullInstantiationMonotoneSMTSolver {
    smt_solver: z3::Optimize,

    /// Map with required monotonicities in form of `{function_id: {input_index: monotonicity}}`.
    monotonicity_defs: HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>,

    /// Collection of occurances of each uninterpreted functions (across encountered fixed point
    /// or essentiality constraints). These are used to build instantiated monotonicity lemmas.
    fun_occurences: HashMap<FuncDeclIdentifier, HashSet<FunctionApp>>,

    /// Helper flag whether assert was already used, since all monotonicity constraints have
    /// to be declared before all assertions. Monotonicity lemmas are added as part of [Self::assert].
    has_asserted: bool,

    /// Helper field with the number of all asserted monotonicity lemmas.
    num_lemmas: u32,

    verbose: bool,
}

/// Function application representation that allows accessing the arguments easily,
/// without needing to process the AST.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FunctionApp {
    id: FuncDeclIdentifier,
    full_app: Bool,
    args: Vec<Bool>,
}

impl FunctionApp {
    pub fn new(id: FuncDeclIdentifier, full_app: Bool) -> Self {
        let args = get_fn_app_args(&full_app);
        FunctionApp { id, full_app, args }
    }
}

/// Extracts all uninterpreted function arguments into a vector (so that they
/// can be easily evaluated).
fn get_fn_app_args(app: &Bool) -> Vec<Bool> {
    match app.decl().kind() {
        DeclKind::UNINTERPRETED => app
            .children()
            .iter()
            .map(|child: &Dynamic| child.as_bool().unwrap())
            .collect(),
        _ => panic!("{} is not function application", app),
    }
}

/// Extracts all uninterpreted function applications from a boolean formula.
/// Uninterpreted functions are the ones where we might enforce monotonicity.
///
/// TODO: for now only works if functions are not nested (arguments do not contain
///       other function applications).
fn get_function_applications(fml: &Bool) -> HashSet<FunctionApp> {
    let mut todo = vec![fml.clone()];
    let mut res: HashSet<FunctionApp> = HashSet::new();
    let mut seen: HashSet<Bool> = HashSet::new();

    // Traverse formula tree, collecting uninterpreted function applications
    while let Some(cur) = todo.pop() {
        if !cur.is_app() {
            continue;
        }

        match cur.decl().kind() {
            DeclKind::UNINTERPRETED => {
                if cur.num_children() > 0 {
                    let fn_app = FunctionApp::new(cur.decl().name(), cur);
                    res.insert(fn_app);
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

/// Creates a monotonicity lemma between two applications of the same function.
/// Compares arguments: for each differing argument, applies the monotonicity constraint.
/// Returns a lemma: (assumptions) => (app1 implies app2)
///
/// None is returned if functions are applied to the exactly same arguments.
fn create_monotonicity_lemma(
    app1: &Bool,
    app2: &Bool,
    monotonicity_defs: &HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>,
) -> Option<Bool> {
    assert!(app1.is_app());
    assert!(app2.is_app());
    assert!(app1.decl().name() == app2.decl().name());

    let name = app1.decl().name();

    // For each differing same-index arguments between the two function, create a constraint
    // (positive mono: arg1<=arg2, negative mono: arg2<=arg1, no mono: arg1==arg2). Their
    // conjunction is then used as assumption for when app1 must imply app2
    let assumptions: Vec<_> = app1
        .children()
        .iter()
        .map(|ast| ast.as_bool().unwrap())
        .zip(app2.children().iter().map(|ast| ast.as_bool().unwrap()))
        .enumerate()
        .filter(|(_, (arg1, arg2))| arg1 != arg2)
        .map(|(i, (arg1, arg2))| {
            match monotonicity_defs.get(&name).and_then(|defs| defs.get(&i)) {
                Some(Monotonicity::Positive) => arg1.implies(arg2), // arg1 <= arg2
                Some(Monotonicity::Negative) => arg2.implies(arg1), // arg1 <= arg2
                None => arg1.iff(arg2),                             // arg1 == arg2
            }
        })
        .collect();

    if !assumptions.is_empty() {
        Some(Bool::and(&assumptions).implies(app1.implies(app2)))
    } else {
        None
    }
}

impl FullInstantiationMonotoneSMTSolver {
    pub fn new() -> Self {
        let solver = z3::Optimize::new();
        // let mut params = Params::new();
        // params.set_symbol("opt.maxsat_engine", "maxres");
        // params.set_symbol("opt.enable_core_rotate", "true");
        // params.set_symbol("opt.enable_sls", "true");
        // params.set_symbol("opt.optsmt_engine", "symba");
        // set_global_param("verbose", "100");
        // solver.set_params(&params);

        FullInstantiationMonotoneSMTSolver {
            smt_solver: solver,
            monotonicity_defs: HashMap::new(),
            fun_occurences: HashMap::new(),
            has_asserted: false,
            num_lemmas: 0,
            verbose: false,
        }
    }

    /// For a newly encountered function application, create lemmas relating it to all
    /// other already encountered applications of the same function.
    fn add_monotonicity_lemmas(&mut self, app: &Bool) {
        assert!(app.is_app());
        let decl = app.decl();
        for other in self.fun_occurences.get(&decl.name()).unwrap() {
            if let Some(lemma) =
                create_monotonicity_lemma(app, &other.full_app, &self.monotonicity_defs)
            {
                self.smt_solver.assert(&lemma);
                self.num_lemmas += 1;
            }
            if let Some(lemma) =
                create_monotonicity_lemma(&other.full_app, app, &self.monotonicity_defs)
            {
                self.smt_solver.assert(&lemma);
                self.num_lemmas += 1;
            }
        }
    }
}

impl MonotoneSMTSolver for FullInstantiationMonotoneSMTSolver {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) {
        if self.has_asserted {
            panic!("Monotonicity constraints have to be declared before all assertions.")
        }

        self.monotonicity_defs
            .entry(f.name())
            .and_modify(|d| {
                d.insert(i, Monotonicity::Positive);
            })
            .or_insert(HashMap::from([(i, Monotonicity::Positive)]));
    }

    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) {
        if self.has_asserted {
            panic!("Monotonicity constraints have to be declared before all assertions.")
        }

        self.monotonicity_defs
            .entry(f.name())
            .and_modify(|d| {
                d.insert(i, Monotonicity::Negative);
            })
            .or_insert(HashMap::from([(i, Monotonicity::Negative)]));
    }

    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.has_asserted = true;
        self.smt_solver.assert_soft(formula, weight, None);
    }

    // TODO: merge internals into trait (parametrized method with `make_lemmas` flag)
    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.smt_solver.assert(formula);

        // Go over all function applications in the asserted formula, and over all
        // function occurences already collected, and add all monotonicity lemmas
        let function_applications = get_function_applications(formula);
        for app in function_applications {
            let name = app.id.clone();
            if !self.monotonicity_defs.contains_key(&name) {
                continue;
            }

            let entry = self.fun_occurences.entry(name).or_default();
            if !(*entry).contains(&app) {
                (*entry).insert(app.clone());
                self.add_monotonicity_lemmas(&app.full_app);
            }
        }
    }

    fn check(&self) -> SatResult {
        if self.verbose {
            println!("{} monotonicity lemmas", self.num_lemmas);
        }
        let res = self.smt_solver.check(&[]);
        if self.verbose {
            println!("{:?}", self.smt_solver.get_statistics());
        }
        res
    }

    fn get_model(&self) -> Option<Model> {
        self.smt_solver.get_model()
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.smt_solver.get_lower(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.smt_solver.register_model_handler(callback);
    }

    fn set_verbose(&mut self) {
        self.verbose = true;
    }

    /// Downcast into InstantiationMonotoneSMTSolver.
    fn as_instantiation_solver(&self) -> Option<&dyn InstantiationMonotoneSMTSolver> {
        Some(self)
    }
}

impl Default for FullInstantiationMonotoneSMTSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl InstantiationMonotoneSMTSolver for FullInstantiationMonotoneSMTSolver {
    fn get_all_monotonicity_defs(
        &self,
    ) -> &HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>> {
        &self.monotonicity_defs
    }

    fn get_collected_fn_occurences(&self) -> &HashMap<FuncDeclIdentifier, HashSet<FunctionApp>> {
        &self.fun_occurences
    }
}

#[allow(dead_code)]
/// Wrapper to transform bool vector to z3 compatible structure and apply
/// function to these arguments.
pub fn apply_fn_to_table_row(table_row: &[bool], func_decl: &FuncDecl) -> Bool {
    let app1_bools: Vec<Bool> = table_row.iter().map(|&b| Bool::from_bool(b)).collect();
    let app1_args: Vec<&dyn Ast> = app1_bools.iter().map(|b| b as &dyn Ast).collect();
    func_decl.apply(&app1_args).as_bool().unwrap()
}

/// Similar to InstantiationMonotoneSMTSolver but uses lazy instantiation strategy.
/// This is currently just a prototype to play with.
pub struct LazyInstantiationMonotoneSMTSolver {
    smt_solver: z3::Optimize,

    /// Map with required monotonicities in form of `{function_id: {input_index: monotonicity}}`.
    monotonicity_defs: HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>,

    /// Collection of occurances of each uninterpreted functions (across encountered fixed point
    /// or essentiality constraints). These are used to build instantiated monotonicity lemmas.
    fun_occurences: HashMap<FuncDeclIdentifier, HashSet<FunctionApp>>,

    /// Helper flag whether assert was already used, since all monotonicity constraints have
    /// to be declared before all assertions.
    has_asserted: bool,

    /// Print some additional progress messages.
    verbose: bool,
}

impl LazyInstantiationMonotoneSMTSolver {
    pub fn new() -> Self {
        let solver = z3::Optimize::new();
        LazyInstantiationMonotoneSMTSolver {
            smt_solver: solver,
            monotonicity_defs: HashMap::new(),
            fun_occurences: HashMap::new(),
            has_asserted: false,
            verbose: false,
        }
    }
}

impl MonotoneSMTSolver for LazyInstantiationMonotoneSMTSolver {
    // Same imple as for InstantiationMonotoneSMTSolver for now.
    // TODO: maybe merge/decouple?
    fn set_monotone(&mut self, f: &FuncDecl, i: usize) {
        if self.has_asserted {
            panic!("Monotonicity constraints have to be declared before all assertions.")
        }

        self.monotonicity_defs
            .entry(f.name())
            .and_modify(|d| {
                d.insert(i, Monotonicity::Positive);
            })
            .or_insert(HashMap::from([(i, Monotonicity::Positive)]));
    }

    // Same imple as for InstantiationMonotoneSMTSolver for now.
    // TODO: maybe merge/decouple?
    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize) {
        if self.has_asserted {
            panic!("Monotonicity constraints have to be declared before all assertions.")
        }

        self.monotonicity_defs
            .entry(f.name())
            .and_modify(|d| {
                d.insert(i, Monotonicity::Negative);
            })
            .or_insert(HashMap::from([(i, Monotonicity::Negative)]));
    }

    fn assert_soft(&mut self, formula: &Bool, weight: BigRational) {
        self.has_asserted = true;
        self.smt_solver.assert_soft(formula, weight, None);
    }

    // TODO: Merge/decouple
    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.smt_solver.assert(formula);

        let function_applications = get_function_applications(formula);
        for app in function_applications {
            let name = app.id.clone();
            if !self.monotonicity_defs.contains_key(&name) {
                continue;
            }

            let entry = self.fun_occurences.entry(name).or_default();
            if !(*entry).contains(&app) {
                (*entry).insert(app.clone());
            }
        }
    }

    /// Iteratively search for a valid solution by lazily enforcing monotonicity.
    /// Monotonicity constraints are lazily added only for function table rows where
    /// the previous solution violates it.
    ///
    /// TODO: There are lots inefficiencies in this prototype, gotta refactor it once it
    /// is working.
    fn check(&self) -> SatResult {
        if self.verbose {
            println!(
                "> Check called. There are {} collected fn applications.",
                self.count_fn_occurances()
            );
        }

        // TODO: If multiple solutions are to be iterated, this counting is incorrect since
        //       we need to remember the number of enforced constraints in the state during
        //       successive check() calls (second check does not start at 0)
        // TODO: Similarly, we should double check what happens when using soft constraints
        //       and running optimization - I guess whole optimization is done for each check
        //       call? And only then we check the monotonicities?

        let mut n_enforced_lemmas = 0;
        loop {
            if self.verbose {
                println!("> Checking with {n_enforced_lemmas} enforced monotonicity lemmas..");
            }
            let res = self.smt_solver.check(&[]);

            if res != SatResult::Sat {
                return res; // If unsat is returned, the whole thing should be unsat
            }

            if self.verbose {
                println!("> Intermetiate solution found, testing for monotonicity..");
            }
            let current_model = self.get_model().unwrap();
            let mut n_new_enforced_lemmas = 0;

            // For each uninterpreted function, go over its occurences, evaluate them,
            // look for pairs that break monotonicity lemmas, and assert them for the next iteration.
            for fn_apps in self.fun_occurences.values() {
                // Collect rows with 0/1 separately, we only compare different output rows
                let mut unique_table_rows_0 = HashMap::new();
                let mut unique_table_rows_1 = HashMap::new();

                for fn_app in fn_apps {
                    let evaluated_args: Vec<bool> = fn_app
                        .args
                        .iter()
                        .map(|arg| current_model.eval(arg, true).unwrap().as_bool().unwrap())
                        .collect();
                    let fn_output: bool = current_model
                        .eval(&fn_app.full_app, true)
                        .unwrap()
                        .as_bool()
                        .unwrap();

                    if fn_output {
                        // Inserting once is enough, we just need one fn application currently
                        unique_table_rows_1.entry(evaluated_args).or_insert(fn_app);
                    } else {
                        unique_table_rows_0.entry(evaluated_args).or_insert(fn_app);
                    }
                }

                // Get the function declaration from any fn_app (they're all the same function)
                let func_decl = fn_apps.iter().next().unwrap().full_app.decl();
                let fn_id = func_decl.name();

                // Check for row pairs breaking monotonicity lemmas
                for (row_1, fn_app_1) in &unique_table_rows_1 {
                    for (row_0, fn_app_0) in &unique_table_rows_0 {
                        // Check if the two rows satisfy monotonicity lemma assumptions, and if so,
                        // assert the corresponding monotonicity lemma (in its general form)
                        let mut assumptions_sat = true;
                        for (i, (val_1, val_0)) in row_1.iter().zip(row_0.iter()).enumerate() {
                            // If the two values are equal, it cant break any of the three assumption types
                            if *val_1 != *val_0 {
                                match self
                                    .monotonicity_defs
                                    .get(&fn_id)
                                    .and_then(|defs| defs.get(&i))
                                {
                                    Some(Monotonicity::Positive) => {
                                        // Assumption: val_1 => val_0
                                        if *val_1 && !*val_0 {
                                            assumptions_sat = false;
                                            break;
                                        }
                                    }
                                    Some(Monotonicity::Negative) => {
                                        // Assumption: val_0 => val_1
                                        if !*val_1 && *val_0 {
                                            assumptions_sat = false;
                                            break;
                                        }
                                    }
                                    None => {
                                        // Assumption: val_0 <=> val_1
                                        assumptions_sat = false;
                                        break;
                                    }
                                }
                            }
                        }

                        // TODO: try creating monotonicity for all pairs of function applications
                        //       that resulted in the two rows

                        if assumptions_sat {
                            // Can be unwrapped, args must be different (since output is different)
                            let lemma = create_monotonicity_lemma(
                                &fn_app_1.full_app,
                                &fn_app_0.full_app,
                                &self.monotonicity_defs,
                            )
                            .unwrap();
                            self.smt_solver.assert(&lemma);
                            /*
                            // Prototype version with concrete rows assertion
                            // Assert the monotonicity constraint `f(row_1) => f(row_0)`
                            let app1 = apply_fn_to_table_row(row_1, &func_decl);
                            let app2 = apply_fn_to_table_row(row_0, &func_decl);
                            self.smt_solver.assert(&app1.implies(&app2));
                            */
                            n_new_enforced_lemmas += 1;
                        }
                    }
                }
            }

            // If there are no function with broken monotonicity, we have a SAT solution
            if n_new_enforced_lemmas == 0 {
                if self.verbose {
                    println!("> Solution found after enforcing {n_enforced_lemmas} lemmas..");
                }
                return SatResult::Sat;
            }
            n_enforced_lemmas += n_new_enforced_lemmas;
        }
    }

    fn get_model(&self) -> Option<Model> {
        self.smt_solver.get_model()
    }

    fn get_lower(&self, objective_id: u32) -> Option<Dynamic> {
        self.smt_solver.get_lower(objective_id)
    }

    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>) {
        self.smt_solver.register_model_handler(callback);
    }

    fn set_verbose(&mut self) {
        self.verbose = true;
    }

    /// Downcast into InstantiationMonotoneSMTSolver.
    fn as_instantiation_solver(&self) -> Option<&dyn InstantiationMonotoneSMTSolver> {
        Some(self)
    }
}

impl Default for LazyInstantiationMonotoneSMTSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl InstantiationMonotoneSMTSolver for LazyInstantiationMonotoneSMTSolver {
    fn get_all_monotonicity_defs(
        &self,
    ) -> &HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>> {
        &self.monotonicity_defs
    }

    fn get_collected_fn_occurences(&self) -> &HashMap<FuncDeclIdentifier, HashSet<FunctionApp>> {
        &self.fun_occurences
    }
}
