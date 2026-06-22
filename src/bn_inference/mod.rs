mod inference_problem;
pub use inference_problem::InferenceProblem;

mod inference_problem_encoder;
pub use inference_problem_encoder::InferenceProblemEncoder;

mod inference_constraint;
pub use inference_constraint::DynInferenceConstraint;
pub use inference_constraint::InferenceConstraint;
pub use inference_constraint::SimpleInferenceConstraint;

mod update_function_definition;
pub use update_function_definition::UpdateFunctionDefinition;

pub mod constraints;

#[cfg(test)]
mod integration_tests;
