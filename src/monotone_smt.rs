use num_rational::BigRational;
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic, forall_const};
use z3::{DeclKind, FuncDecl, Model, SatResult};

enum Monotonicity {
    Positive,
    Negative,
}

pub trait MonotoneSMTSolver {
    fn set_monotone(&mut self, f: &FuncDecl, i: usize);
    fn set_antimonotone(&mut self, f: &FuncDecl, i: usize);
    fn assert_soft(&mut self, formula: &Bool, weight: BigRational);
    fn assert(&mut self, formula: &Bool);
    fn check(&self) -> SatResult;
    fn get_model(&self) -> Option<Model>;
    fn get_lower(&self, objective_id: u32) -> Option<Dynamic>;
    fn register_model_handler(&self, callback: Box<dyn Fn(&Model)>);
}

pub struct QuantifiedMonotoneSMTSolver {
    smt_solver: z3::Optimize,
}

fn make_dyn_vec(asts: &[Bool]) -> Vec<&dyn Ast> {
    asts.iter().map(|it| it as &dyn Ast).collect()
}

impl QuantifiedMonotoneSMTSolver {
    pub fn new() -> Self {
        QuantifiedMonotoneSMTSolver {
            smt_solver: z3::Optimize::new(),
        }
    }

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
        println!("{:?}", self.smt_solver.get_statistics());
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
}

type FuncDeclIdentifier = String;

pub struct InstantiationMonotoneSMTSolver {
    smt_solver: z3::Optimize,

    monotonicity_defs: HashMap<FuncDeclIdentifier, HashMap<usize, Monotonicity>>,
    fun_occurences: HashMap<FuncDeclIdentifier, HashSet<Bool>>,
    has_asserted: bool,

    num_lemmas: u32,
}

fn get_function_applications(fml: &Bool) -> HashSet<Bool> {
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

    fn add_monotonicity_lemma(&self, app1: &Bool, app2: &Bool) -> Option<Bool> {
        assert!(app1.is_app());
        assert!(app2.is_app());
        assert!(app1.decl().name() == app2.decl().name());

        let name = app1.decl().name();

        let assumptions: Vec<_> = app1
            .children()
            .iter()
            .map(|ast| ast.as_bool().unwrap())
            .zip(app2.children().iter().map(|ast| ast.as_bool().unwrap()))
            .enumerate()
            .filter(|(_, (arg1, arg2))| arg1 != arg2)
            .map(|(i, (arg1, arg2))| {
                match self
                    .monotonicity_defs
                    .get(&name)
                    .and_then(|defs| defs.get(&i))
                {
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

    fn add_monotonicity_lemmas(&mut self, app: &Bool) {
        assert!(app.is_app());
        let decl = app.decl();
        for other in self.fun_occurences.get(&decl.name()).unwrap() {
            if let Some(lemma) = self.add_monotonicity_lemma(app, other) {
                self.smt_solver.assert(&lemma);
                self.num_lemmas += 1;
            }
            if let Some(lemma) = self.add_monotonicity_lemma(other, app) {
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
        // println!("{} monotonicity lemmas", self.num_lemmas);
        let res = self.smt_solver.check(&[]);
        // println!("{:?}", self.smt_solver.get_statistics());
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
}
