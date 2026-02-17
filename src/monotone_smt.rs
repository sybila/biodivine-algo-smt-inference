use num_rational::BigRational;
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic, forall_const};
use z3::{DeclKind, FuncDecl, Model, SatResult};

/// Represents whether a function input is positively or negatively monotone
enum Monotonicity {
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
}

/// SMT solver that uses quantified (forall) constraints to encode monotonicity properties
pub struct QuantifiedMonotoneSMTSolver {
    smt_solver: z3::Optimize,
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
        /*
        let res = self.smt_solver.check(&[]);
        println!("{:?}", self.smt_solver.get_statistics());
        res
        */
        self.smt_solver.check(&[])
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
pub struct InstantiationMonotoneSMTSolver {
    smt_solver: z3::Optimize,

    /// Map with required monotonicities in form of `{function_id: {input_index: monotonicity}}`.
    monotonicity_defs: HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>,

    /// Collection of occurances of each uninterpreted functions (across fixed point constraints
    /// or essentiality constraints). These are used to build instantiated monotonicity lemmas.
    fun_occurences: HashMap<FuncDeclIdentifier, HashSet<Bool>>,

    /// Helper flag whether assert was already used, since all monotonicity constraints have
    /// to be declared before all assertions. Monotonicity lemmas are added as part of [Self::assert].
    has_asserted: bool,

    /// Helper field with the number of all asserted monotonicity lemmas.
    num_lemmas: u32,
}

/// Extracts all uninterpreted function applications from a boolean formula.
/// Uninterpreted functions are the ones where we might enforce monotonicity.
fn get_function_applications(fml: &Bool) -> HashSet<Bool> {
    let mut todo = vec![fml.clone()];
    let mut res: HashSet<Bool> = HashSet::new();
    let mut seen: HashSet<Bool> = HashSet::new();

    // Traverse formula tree, collecting uninterpreted function applications
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

impl InstantiationMonotoneSMTSolver {
    pub fn new() -> Self {
        let solver = z3::Optimize::new();
        // let mut params = Params::new();
        // params.set_symbol("opt.maxsat_engine", "maxres");
        // params.set_symbol("opt.enable_core_rotate", "true");
        // params.set_symbol("opt.enable_sls", "true");
        // params.set_symbol("opt.optsmt_engine", "symba");
        // set_global_param("verbose", "100");
        // solver.set_params(&params);

        InstantiationMonotoneSMTSolver {
            smt_solver: solver,
            monotonicity_defs: HashMap::new(),
            fun_occurences: HashMap::new(),
            has_asserted: false,
            num_lemmas: 0,
        }
    }

    /// For a newly encountered function application, create lemmas relating it to all
    /// other already encountered applications of the same function.
    fn add_monotonicity_lemmas(&mut self, app: &Bool) {
        assert!(app.is_app());
        let decl = app.decl();
        for other in self.fun_occurences.get(&decl.name()).unwrap() {
            if let Some(lemma) = create_monotonicity_lemma(app, other, &self.monotonicity_defs) {
                self.smt_solver.assert(&lemma);
                self.num_lemmas += 1;
            }
            if let Some(lemma) = create_monotonicity_lemma(other, app, &self.monotonicity_defs) {
                self.smt_solver.assert(&lemma);
                self.num_lemmas += 1;
            }
        }
    }
}

impl MonotoneSMTSolver for InstantiationMonotoneSMTSolver {
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

    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.smt_solver.assert(formula);

        // Go over all function applications in the asserted formula, and over all
        // function occurences already collected, and add all monotonicity lemmas
        let function_applications = get_function_applications(formula);
        for app in function_applications {
            let name = app.decl().name();
            if !self.monotonicity_defs.contains_key(&name) {
                continue;
            }

            let entry = self.fun_occurences.entry(name).or_default();
            if !(*entry).contains(&app) {
                (*entry).insert(app.clone());
                self.add_monotonicity_lemmas(&app);
            }
        }
    }

    fn check(&self) -> SatResult {
        /*
        println!("{} monotonicity lemmas", self.num_lemmas);
        let res = self.smt_solver.check(&[]);
        println!("{:?}", self.smt_solver.get_statistics());
        res
        */
        self.smt_solver.check(&[])
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
}

impl Default for InstantiationMonotoneSMTSolver {
    fn default() -> Self {
        Self::new()
    }
}
/// Enum to specify literals in DNF clauses (positive/negative/missing).
pub enum LiteralValue {
    Positive,
    Negative,
    Missing,
}

/// Simplified representation for a dnf clause for a fixed number of variables.
/// For now, it is just a vector of ternary values specifying if particular variable
/// is used as positive/negative literal, or is missing.
pub struct DNFClause {
    pub literals: Vec<LiteralValue>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
/// Function application representation that allows accessing the arguments easily.
///
/// TODO: this is now more bloated than initially expected, should be refactored later...
pub struct FunctionApp {
    id: FuncDeclIdentifier,
    full_app: Bool,
    args: Vec<Bool>,
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

impl FunctionApp {
    pub fn new(id: FuncDeclIdentifier, full_app: Bool) -> Self {
        let args = get_fn_app_args(&full_app);
        FunctionApp { id, full_app, args }
    }
}

/// Extracts all uninterpreted function applications from a boolean formula.
/// Uninterpreted functions are the ones where we might enforce monotonicity.
///
/// TODO: merge with similar [get_function_applications]
/// TODO: for now only works if functions are not nested (arguments do not contain
///       other function applications).
fn get_fn_apps_with_args(fml: &Bool) -> HashSet<FunctionApp> {
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
}

impl LazyInstantiationMonotoneSMTSolver {
    pub fn new() -> Self {
        let solver = z3::Optimize::new();
        LazyInstantiationMonotoneSMTSolver {
            smt_solver: solver,
            monotonicity_defs: HashMap::new(),
            fun_occurences: HashMap::new(),
            has_asserted: false,
        }
    }

    fn get_monotonicity_def(
        &self,
        fn_id: &FuncDeclIdentifier,
        idx: usize,
    ) -> Option<&Monotonicity> {
        self.monotonicity_defs
            .get(fn_id)
            .and_then(|defs| defs.get(&idx))
    }

    #[allow(dead_code)]
    /// Count current collected function applications.
    fn count_fn_occurances(&self) -> usize {
        self.fun_occurences.values().map(|apps| apps.len()).sum()
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

    fn assert(&mut self, formula: &Bool) {
        self.has_asserted = true;
        self.smt_solver.assert(formula);

        let function_applications = get_fn_apps_with_args(formula);
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

    fn check(&self) -> SatResult {
        // Iteratively search for a valid solution by lazily enforcing monotonicity.
        // Monotonicity constraints are lazily added only for function table rows where
        // the previous solution violates it.

        // TODO: There is lots of cloning and other inefficiencies happening in this prototype,
        //       gotta refactor it once it is working

        println!(
            "> Check called. There are {} collected fn applications.",
            self.count_fn_occurances()
        );

        // TODO: If multiple solutions are to be iterated, this counting is incorrect since
        //       we need to remember the number of enforced constraints in the state during
        //       successive check() calls (second check does not start at 0)
        // TODO: Similarly, we should double check what happens when using soft constraints
        //       and running optimization - I guess whole optimization is done for each check
        //       call? And only then we check the monotonicities?

        let mut n_enforced_pairs = 0;
        loop {
            // Check for solution with the current set of enforced monotonicity row pairs
            println!("> Checking with {n_enforced_pairs} enforced monotonicity row pairs..");
            let res = self.smt_solver.check(&[]);

            // If unsat is returned, the whole thing should be unsat
            if res != SatResult::Sat {
                return res;
            }

            println!("> Intermetiate solution found, testing for monotonicity..");
            let current_model = self.get_model().unwrap();
            let mut n_new_enforced_pairs = 0;

            // For each uninterpreted function, go over its occurences, evaluate them,
            // look for pairs that break monotonicity, and assert them for the next iteration.
            for fn_apps in self.fun_occurences.values() {
                // Evaluate the fn applications and collect table rows. Rows with output 0/1 are
                // collected separately, since we only need to compare lines with different outputs.
                let mut unique_table_rows_0 = HashSet::new();
                let mut unique_table_rows_1 = HashSet::new();

                for fn_app in fn_apps {
                    let evaluated_args: Vec<bool> = fn_app
                        .args
                        .clone()
                        .into_iter()
                        .map(|arg| current_model.eval(&arg, true).unwrap().as_bool().unwrap())
                        .collect();
                    let fn_output: bool = current_model
                        .eval(&fn_app.full_app, true)
                        .unwrap()
                        .as_bool()
                        .unwrap();

                    if fn_output {
                        unique_table_rows_1.insert(evaluated_args);
                    } else {
                        unique_table_rows_0.insert(evaluated_args);
                    }
                }

                // Get the function declaration from any fn_app (they're all the same function)
                let func_decl = fn_apps.iter().next().unwrap().full_app.decl();
                let fn_id = func_decl.name();

                // Now check for pairs of rows that break monotonicity, that is rows that differ in
                // one value (and result in different output) in the following way:
                //     1) An activator input goes 0 -> 1 and output goes 1 -> 0
                //     2) An inhibitor input goes 1 -> 0 and output goes 1 -> 0
                // For pairs that break monotonicity, create the "f(row_1) => f(row_0)" asserts
                for row_1 in &unique_table_rows_1 {
                    for (i, value_1) in row_1.iter().enumerate() {
                        // Check whether a corresponding row with a flipped value is in the other set
                        // Only check for pairs that would violate monotonicity
                        let monotonicity = self.get_monotonicity_def(&fn_id, i);

                        if (!*value_1 && matches!(monotonicity, Some(Monotonicity::Positive)))
                            || (*value_1 && matches!(monotonicity, Some(Monotonicity::Negative)))
                        {
                            let mut row_0 = row_1.clone();
                            row_0[i] = !*value_1; // flip monotonic input
                            if unique_table_rows_0.contains(&row_0) {
                                // Assert the monotonicity constraint for the two rows
                                let app1 = apply_fn_to_table_row(row_1, &func_decl);
                                let app2 = apply_fn_to_table_row(&row_0, &func_decl);
                                self.smt_solver.assert(&app1.implies(&app2));
                                n_new_enforced_pairs += 1;
                            }
                        }
                    }
                }
            }

            // If there are no function with broken monotonicity, we have a SAT solution
            n_enforced_pairs += n_new_enforced_pairs;
            if n_new_enforced_pairs == 0 {
                println!(
                    "> Found a solution after enforcing {n_enforced_pairs} monotonicity row pairs.."
                );
                return SatResult::Sat;
            }
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
}

impl Default for LazyInstantiationMonotoneSMTSolver {
    fn default() -> Self {
        Self::new()
    }
}
