/// Test that on fully specified networks, the inference process validates the
/// expected properties and/or identifies the correct models for expected steady states.
mod inference_fully_specified;

/// Some very simple tests to verify that uninterpreted function symbols also work as intended.
mod inference_simple_partially_specified;

/// Tests the SMT inference method on a few toy models.
mod inference_toy_models;

/// Very simple tests for naive inference method using toy models.
mod inference_naive;
