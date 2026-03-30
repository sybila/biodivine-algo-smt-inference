use crate::bn_inference::constraints::{check_state_exists, check_variable_exists, sorted_map};
use crate::smt_solver::typed_ast::AstType;
use anyhow::anyhow;
use biodivine_algo_smt_inference::bn_inference::constraints::{
    ConstraintStrings, check_variable_domain,
};
use biodivine_algo_smt_inference::bn_inference::{
    InferenceProblem, InferenceProblemEncoder, SimpleInferenceConstraint,
};
use biodivine_algo_smt_inference::smt_solver::AbstractSolver;
use biodivine_algo_smt_inference::smt_solver::typed_ast::TypedAst;
use biodivine_lib_param_bn::{BooleanNetwork, ModelAnnotation, VariableId};
use log::info;
use macros::InferenceConstraint;
use std::fmt::{Display, Formatter};
use z3::ast::{Bool, Int};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ComparedValue {
    Constant(u32),
    VariableInState(String, VariableId),
    UpdateFunctionOutputInState(String, VariableId),
}

impl ComparedValue {
    /// Check that this value can be safely evaluated in the context of the given `problem`.
    pub fn validate<SOLVER: 'static>(
        &self,
        problem: &InferenceProblem<SOLVER>,
    ) -> Result<(), anyhow::Error> {
        match self {
            ComparedValue::Constant(_) => Ok(()),
            ComparedValue::VariableInState(state, variable) => {
                check_state_exists(problem, state)?;
                check_variable_exists(problem, *variable)?;
                Ok(())
            }
            ComparedValue::UpdateFunctionOutputInState(state, variable) => {
                check_state_exists(problem, state)?;
                check_variable_exists(problem, *variable)?;
                Ok(())
            }
        }
    }

    pub fn as_constant(&self) -> Option<u32> {
        match self {
            ComparedValue::Constant(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_variable(&self) -> Option<VariableId> {
        match self {
            ComparedValue::Constant(_) => None,
            ComparedValue::VariableInState(_, var) => Some(*var),
            ComparedValue::UpdateFunctionOutputInState(_, var) => Some(*var),
        }
    }

    /// Get the underlying type of this value.
    pub fn get_ast_type<SOLVER: 'static>(&self, problem: &InferenceProblem<SOLVER>) -> AstType {
        match self {
            ComparedValue::Constant(value) => {
                if *value <= 1 {
                    AstType::Bool
                } else {
                    AstType::Int
                }
            }
            ComparedValue::VariableInState(_, variable) => problem[*variable].ast_type(),
            ComparedValue::UpdateFunctionOutputInState(_, variable) => {
                problem[*variable].ast_type()
            }
        }
    }

    /// Create a [`TypedAst`] representing this value, automatically converting Boolean constants
    /// to integers if necessary, but otherwise preserving type safety.
    pub fn as_ast<SOLVER: AbstractSolver + 'static>(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
        my_type: AstType,
        other_type: AstType,
    ) -> Result<TypedAst, anyhow::Error> {
        match self {
            ComparedValue::Constant(value) => {
                // If either value is int, "up-cast" to int, otherwise stay bool.
                // If there is still a type mismatch, it will be caught by the comparison operators.
                if my_type == AstType::Int || other_type == AstType::Int {
                    Ok(Int::from_u64(u64::from(*value)).into())
                } else {
                    assert!(my_type == AstType::Bool && other_type == AstType::Bool);
                    Ok(Bool::from_bool(*value == 1).into())
                }
            }
            ComparedValue::VariableInState(state, variable) => {
                if my_type != other_type {
                    return Err(anyhow!(
                        "Invalid comparison: `{}` has type `{}`, but need to be `{}`.",
                        self,
                        my_type,
                        other_type
                    ));
                }
                Ok(encoder.state_atom(state, *variable).clone())
            }
            ComparedValue::UpdateFunctionOutputInState(state, variable) => {
                if my_type != other_type {
                    return Err(anyhow!(
                        "Invalid comparison: `{}` has type `{}`, but need to be `{}`.",
                        self,
                        my_type,
                        other_type
                    ));
                }
                let args = encoder.problem[*variable]
                    .regulators_iter()
                    .map(|regulator| encoder.state_atom(state, regulator))
                    .collect::<Vec<_>>();
                Ok(encoder.mk_update_function_call(*variable, &args))
            }
        }
    }

    /// Parse compared value from the annotation string.
    pub fn read_from_key(key: &str, psbn: &BooleanNetwork) -> Result<Self, anyhow::Error> {
        if let Ok(constant) = key.parse::<u32>() {
            return Ok(ComparedValue::Constant(constant));
        }

        let split = key.split("/").collect::<Vec<_>>();

        if split.len() == 2 {
            let fst = split[0];
            let snd = split[1];
            return if let Some(fst) = fst.strip_prefix("$") {
                let id = psbn
                    .as_graph()
                    .find_variable(fst)
                    .ok_or_else(|| anyhow!("Variable not found: `{}`", fst))?;
                Ok(ComparedValue::UpdateFunctionOutputInState(
                    snd.to_string(),
                    id,
                ))
            } else {
                let id = psbn
                    .as_graph()
                    .find_variable(snd)
                    .ok_or_else(|| anyhow!("Variable not found: `{}`", snd))?;
                Ok(ComparedValue::VariableInState(fst.to_string(), id))
            };
        }

        Err(anyhow!(
            "Expected constant value, `state/variable`, or `$variable/state` expression. Got `{key}`."
        ))
    }
}

impl Display for ComparedValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ComparedValue::Constant(constant) => write!(f, "{constant}"),
            ComparedValue::VariableInState(state, variable) => {
                write!(f, "{state}/{variable:?}")
            }
            ComparedValue::UpdateFunctionOutputInState(state, variable) => {
                write!(f, "${variable:?}/{state}")
            }
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum CmpOp {
    Less,
    LessEqual,
    Equal,
    NotEqual,
    GreaterEqual,
    Greater,
}

impl Display for CmpOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CmpOp::Less => write!(f, "<"),
            CmpOp::LessEqual => write!(f, "<="),
            CmpOp::Equal => write!(f, "=="),
            CmpOp::NotEqual => write!(f, "!="),
            CmpOp::GreaterEqual => write!(f, ">="),
            CmpOp::Greater => write!(f, ">"),
        }
    }
}

impl CmpOp {
    pub fn read_from_key(key: &str) -> Result<CmpOp, anyhow::Error> {
        match key {
            ConstraintStrings::LESS => Ok(CmpOp::Less),
            ConstraintStrings::LESS_EQUAL => Ok(CmpOp::LessEqual),
            ConstraintStrings::EQUAL => Ok(CmpOp::Equal),
            ConstraintStrings::NOT_EQUAL => Ok(CmpOp::NotEqual),
            ConstraintStrings::GREATER => Ok(CmpOp::Greater),
            ConstraintStrings::GREATER_EQUAL => Ok(CmpOp::GreaterEqual),
            _ => Err(anyhow!("Invalid comparison: `{}`", key)),
        }
    }
}

#[derive(InferenceConstraint, Debug, PartialEq, Eq, Clone, Hash)]
pub struct ValueComparison {
    pub left: ComparedValue,
    pub right: ComparedValue,
    pub op: CmpOp,
}

impl ValueComparison {
    pub fn new(left: ComparedValue, op: CmpOp, right: ComparedValue) -> Self {
        ValueComparison { left, op, right }
    }

    /// Create a [`ValueComparison`] asserting that `variable == value` in a specific `state`.
    pub fn variable_assignment(state: &str, variable: VariableId, value: u32) -> Self {
        ValueComparison {
            left: ComparedValue::VariableInState(state.to_string(), variable),
            op: CmpOp::Equal,
            right: ComparedValue::Constant(value),
        }
    }

    /// If this value comparison corresponds to `state/var = const`, return the assignment
    /// as a tuple. This can be used for value propagation.
    ///
    /// TODO:
    ///     Currently, this is the only supported format for assignments. In the future, we could
    ///     expand this to (a) include the symmetric form; (b) do some additional value propagation.
    ///     For example, if a variable is Boolean, then `state1/var < state2/var` implies that
    ///     `state1/var = 0` and `state2/var = 1`. And so on...
    pub fn as_assignment(&self) -> Option<(String, VariableId, u32)> {
        let ComparedValue::VariableInState(state, variable) = &self.left else {
            return None;
        };
        let ComparedValue::Constant(value) = &self.right else {
            return None;
        };
        if self.op != CmpOp::Equal {
            return None;
        };

        Some((state.clone(), *variable, *value))
    }

    /// Read all value comparisons from the given model annotations.
    ///
    /// The method returns each constraint together with its metadata (again represented as
    /// an annotation).
    pub fn read_from<'a, SOLVER: AbstractSolver + 'static>(
        psbn: &BooleanNetwork,
        model_annotation: &'a ModelAnnotation,
    ) -> Result<Vec<(Self, &'a ModelAnnotation)>, anyhow::Error> {
        let mut result = Vec::new();
        let comparisons = model_annotation.get_child(&[ConstraintStrings::COMPARISON]);
        if let Some(comparisons) = comparisons {
            for (op, inner) in sorted_map(comparisons.children()) {
                let op = CmpOp::read_from_key(op)?;
                for (left, inner) in sorted_map(inner.children()) {
                    if inner.children().is_empty() {
                        return Err(anyhow!(
                            "Malformed value comparison for `{op}` and `{left}`."
                        ));
                    }
                    for (right, inner) in sorted_map(inner.children()) {
                        let left = ComparedValue::read_from_key(left, psbn)?;
                        let right = ComparedValue::read_from_key(right, psbn)?;
                        result.push((Self::new(left, op, right), inner));
                    }
                }
            }
        }

        Ok(result)
    }
}

impl<SOLVER: AbstractSolver + 'static> SimpleInferenceConstraint<SOLVER> for ValueComparison {
    fn validate(&self, problem: &InferenceProblem<SOLVER>) -> Result<(), anyhow::Error> {
        // Check that the variables and states exist:
        self.left.validate(problem)?;
        self.right.validate(problem)?;
        // Check that comparisons all fall within the correct domain:
        if let (Some(variable), Some(constant)) =
            (self.left.as_variable(), self.right.as_constant())
        {
            check_variable_domain(problem, variable, constant)?;
        }
        if let (Some(constant), Some(variable)) =
            (self.left.as_constant(), self.right.as_variable())
        {
            check_variable_domain(problem, variable, constant)?;
        }
        Ok(())
    }

    fn mk_assertion(
        &self,
        encoder: &InferenceProblemEncoder<SOLVER>,
    ) -> Result<Bool, anyhow::Error> {
        info!(
            "Making value comparison assertion `{} {} {}`.",
            self.left, self.op, self.right
        );

        let left_type = self.left.get_ast_type(&encoder.problem);
        let right_type = self.right.get_ast_type(&encoder.problem);

        let left_ast = self.left.as_ast(encoder, left_type, right_type)?;
        let right_ast = self.right.as_ast(encoder, right_type, left_type)?;

        match self.op {
            CmpOp::Less => left_ast.lt(&right_ast),
            CmpOp::LessEqual => left_ast.le(&right_ast),
            CmpOp::Equal => left_ast.eq(&right_ast),
            CmpOp::NotEqual => Ok(left_ast.eq(&right_ast)?.not()),
            CmpOp::GreaterEqual => right_ast.le(&left_ast),
            CmpOp::Greater => right_ast.lt(&left_ast),
        }
    }
}
