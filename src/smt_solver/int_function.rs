use crate::smt_solver::CmpOp::{EQ, GE, LE};
use crate::smt_solver::Monotonicity;
use crate::smt_solver::Monotonicity::Positive;
use crate::smt_solver::typed_ast::AstType;
use Monotonicity::Negative;
use anyhow::anyhow;
use biodivine_lib_bdd::{Bdd, BddVariable, BddVariableSet};
use biodivine_lib_param_bn::{BinaryOp, FnUpdate, VariableId};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Display, Formatter};

/// A simple struct that represents an "integer function" by listing a disjunction
/// of terms for each output level. Note that the lists of terms are not necessarily exclusive
/// and the output is the highest that matches the input.
pub struct IntFunction {
    pub signature: (Vec<AstType>, AstType),
    pub terms: BTreeMap<u32, Vec<Vec<IntAtom>>>,
}

impl IntFunction {
    /// Remove the default output level (zero) from the function, simplifying its description.
    pub fn drop_default_output_level(&mut self) {
        self.terms.remove(&0);
    }

    /// Remove duplicate clauses from this [`IntFunction`] and ensure all clauses list atoms
    /// in an increasing order.
    pub fn remove_duplicates(&mut self) {
        for clauses in self.terms.values_mut() {
            let deduplicated = BTreeSet::from_iter(clauses.clone());
            if deduplicated.contains(&Vec::new()) {
                // If the result contains an empty clause, that empty clause is a tautology,
                // and we can just remove everything except for that empty clause.
                *clauses = vec![Vec::new()];
            }
            *clauses = Vec::from_iter(deduplicated.into_iter().map(|mut clause| {
                clause.sort();
                clause
            }));
        }
    }

    /// Eliminate all atoms that are universally true assuming the specified argument
    /// only falls within the given range of values.
    ///
    /// Note that this operation can also leave the function with many duplicated clauses
    /// (since multiple clauses simplify to the same clauses). These can be explicitly
    /// removed using [`Self::remove_duplicates`].
    pub fn clamp_argument(&mut self, arg_index: usize, domain: (u32, u32)) {
        for clauses in self.terms.values_mut() {
            for clause in clauses.iter_mut() {
                clause.retain(|atom| {
                    if atom.arg_index == arg_index {
                        // x >= min >= val || x <= max <= val
                        !(atom.op == GE && domain.0 >= atom.val
                            || atom.op == LE && domain.1 <= atom.val)
                    } else {
                        true
                    }
                })
            }
        }
    }

    /// Replace equality atoms of monotone arguments with inequalities reflecting the fact
    /// that each input combination with higher (or lower) values must also produce
    /// the same result.
    ///
    /// **Important:** Currently, the function assumes all atoms of the provided argument
    /// must be equalities.
    pub fn relax_monotone_argument(&mut self, arg_index: usize, monotonicity: Monotonicity) {
        for clauses in self.terms.values_mut() {
            for clause in clauses.iter_mut() {
                for atom in clause.iter_mut() {
                    if atom.arg_index != arg_index {
                        continue;
                    }
                    assert_eq!(atom.op, EQ);
                    match monotonicity {
                        // Change x = val to x >= val:
                        Positive => atom.op = GE,
                        // Change x = val to x <= val;
                        Negative => atom.op = LE,
                    }
                }
            }
        }
    }

    /// Convert this [`IntFunction`] to [`FnUpdate`] assuming all arguments and output of this
    /// function is Boolean.
    pub fn as_update_function(&self, args: &[VariableId]) -> Result<FnUpdate, anyhow::Error> {
        if self.signature.1 != AstType::Bool {
            return Err(anyhow!(
                "Conversion to `FnUpdate` failed: the function is not boolean."
            ));
        }
        for arg in self.signature.0.iter() {
            if *arg != AstType::Bool {
                return Err(anyhow!(
                    "Conversion to `FnUpdate` failed: the function is not boolean."
                ));
            }
        }
        if args.len() != self.signature.0.len() {
            return Err(anyhow!(
                "Expected {} arguments but got {}.",
                self.signature.0.len(),
                args.len()
            ));
        }

        let Some(clauses) = self.terms.get(&1) else {
            // This is a constant zero function:
            return Ok(FnUpdate::mk_false());
        };

        let clauses = clauses
            .iter()
            .map(|clause| {
                let clause = clause
                    .iter()
                    .map(|atom| {
                        let var = args[atom.arg_index];
                        let var = FnUpdate::mk_var(var);
                        assert!(atom.val == 0 || atom.val == 1);
                        if atom.val == 0 {
                            match atom.op {
                                LE | EQ => var.negation(), // x <= 0 = !x, x == 0 = !x
                                GE => FnUpdate::mk_true(), // x >= 0 = 1
                            }
                        } else {
                            match atom.op {
                                LE => FnUpdate::mk_true(), // x <= 1 = 1
                                GE | EQ => var,            // x >= 1 = x, x == 1 = x
                            }
                        }
                    })
                    .collect::<Vec<_>>();
                FnUpdate::mk_conjunction(&clause)
            })
            .collect::<Vec<_>>();

        Ok(FnUpdate::mk_disjunction(&clauses))
    }

    /// Create a [`IntFunction`] based on the given fully specified [`FnUpdate`]. Because
    /// [`FnUpdate`] does not have explicitly ordered arguments (or argument types), argument
    /// signatures must be also provided. The output of the function itself is always Boolean.
    ///
    pub fn from_update_function(
        expression: &FnUpdate,
        arg_signatures: &[(VariableId, AstType)],
    ) -> Self {
        // **First step:** Convert the expression into DNF via a BDD.

        // The BDD variables correspond exactly to the function arguments, given
        // by the `arg_signatures` list.

        let arg_count =
            u16::try_from(arg_signatures.len()).expect("Argument count must fit into `u16`.");
        let bdd_vars = BddVariableSet::new_anonymous(arg_count);

        // Each `VariableId` maps to an argument index given by `arg_signatures`:
        let bdd_var_map = arg_signatures
            .iter()
            .enumerate()
            .map(|(id, (var, _))| (*var, id))
            .collect::<HashMap<_, _>>();

        fn build(
            expression: &FnUpdate,
            bdd_vars: &BddVariableSet,
            bdd_var_map: &HashMap<VariableId, usize>,
        ) -> Bdd {
            match expression {
                FnUpdate::Const(value) => {
                    if *value {
                        bdd_vars.mk_true()
                    } else {
                        bdd_vars.mk_false()
                    }
                }
                FnUpdate::Var(var) => {
                    let bdd_var = bdd_var_map
                        .get(var)
                        .unwrap_or_else(|| panic!("Missing signature for `{var}`."));
                    bdd_vars.mk_var(BddVariable::from_index(*bdd_var))
                }
                FnUpdate::Param(_, _) => panic!("Expression must not contain parameters."),
                FnUpdate::Not(inner) => build(inner, bdd_vars, bdd_var_map).not(),
                FnUpdate::Binary(op, left, right) => {
                    let left = build(left, bdd_vars, bdd_var_map);
                    let right = build(right, bdd_vars, bdd_var_map);
                    match op {
                        BinaryOp::And => left.and(&right),
                        BinaryOp::Or => left.or(&right),
                        BinaryOp::Xor => left.xor(&right),
                        BinaryOp::Iff => left.iff(&right),
                        BinaryOp::Imp => left.imp(&right),
                    }
                }
            }
        }

        let bdd = build(expression, &bdd_vars, &bdd_var_map);
        let dnf = bdd.to_optimized_dnf();

        // **Second step:** Convert the DNF into `IntFunction` terms.

        let mut term_list = Vec::new();
        for clause in dnf {
            let clause = clause
                .to_values()
                .into_iter()
                .map(|(bdd_var, value)| {
                    if value {
                        IntAtom::ge(bdd_var.to_index(), 1)
                    } else {
                        IntAtom::le(bdd_var.to_index(), 0)
                    }
                })
                .collect::<Vec<_>>();
            term_list.push(clause);
        }

        let args = arg_signatures.iter().map(|(_, b)| *b).collect::<Vec<_>>();
        IntFunction {
            signature: (args, AstType::Bool),
            terms: BTreeMap::from_iter([(1, term_list)]),
        }
    }
}

/// A comparison operator enum used to represent inequalities in [`IntAtom`].
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum CmpOp {
    LE, // <=
    GE, // >=
    EQ, // ==
}

/// A single inequality between a function argument and a constant value.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct IntAtom {
    pub arg_index: usize,
    pub op: CmpOp,
    pub val: u32,
}

impl IntAtom {
    pub fn le(arg_index: usize, val: u32) -> IntAtom {
        IntAtom {
            arg_index,
            op: LE,
            val,
        }
    }

    pub fn ge(arg_index: usize, val: u32) -> IntAtom {
        IntAtom {
            arg_index,
            op: GE,
            val,
        }
    }

    pub fn eq(arg_index: usize, val: u32) -> IntAtom {
        IntAtom {
            arg_index,
            op: EQ,
            val,
        }
    }
}

impl Display for CmpOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LE => write!(f, "<="),
            GE => write!(f, ">="),
            EQ => write!(f, "=="),
        }
    }
}

impl Display for IntAtom {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "x_{} {} {}", self.arg_index, self.op, self.val)
    }
}

impl Display for IntFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let arg_types = self.signature.0.iter().map(|it| it.to_string()).join(", ");
        writeln!(f, "f({arg_types}): {} {{ ", self.signature.1)?;
        for (out, list) in self.terms.iter().rev() {
            let clauses = list
                .iter()
                .map(|clause| {
                    let clause = clause.iter().map(|it| it.to_string()).join(" & ");
                    format!("({})", clause)
                })
                .join(" | ");
            writeln!(f, "\t{out} <- {clauses};")?;
        }
        if !self.terms.contains_key(&0) {
            writeln!(f, "\t0 <- else")?;
        }
        writeln!(f, "}}")?;
        Ok(())
    }
}
