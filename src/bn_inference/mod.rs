mod inference_problem;
pub use inference_problem::InferenceProblem;

mod inference_problem_encoder;
pub use inference_problem_encoder::InferenceProblemEncoder;

mod inference_constraint;
pub use inference_constraint::InferenceConstraint;
pub use inference_constraint::SimpleInferenceConstraint;

pub mod constraints;

mod inference_solution_iterator;
pub use inference_solution_iterator::{BlockingStrategy, InferenceSolutionIterator};
