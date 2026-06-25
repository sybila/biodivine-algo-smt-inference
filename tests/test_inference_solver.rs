use assert_cmd::Command;
use predicates::prelude::*;
use predicates::str::{contains, ends_with};

// These are simple end-to-end tests that we can use to verify the solver binaries are
// working as expected. Right now, it only uses relatively simple examples. In the future,
// we need a much better coverage especially for negative test cases.

#[test]
fn run_inference_enumerate_states() {
    // If we only enumerate `s1`, we should get 8 solutions.
    Command::cargo_bin("inference_problem_solver")
        .unwrap()
        .arg("data/example_simple/three-state-cycle.aeon")
        .arg("--solutions=200")
        .arg("--print-state-valuations")
        .arg("--projection=s1/*")
        .assert()
        .success()
        .stdout(contains("Solution #8").and(contains("Solution #9").not()));

    // If we enumerate `s1` and `s2`, we should get 8*4=32 solutions.
    Command::cargo_bin("inference_problem_solver")
        .unwrap()
        .arg("data/example_simple/three-state-cycle.aeon")
        .arg("--solutions=200")
        .arg("--print-state-valuations")
        .arg("--projection=s1/*")
        .arg("--projection=s2/*")
        .assert()
        .success()
        .stdout(contains("Solution #32").and(contains("Solution #33").not()));
}

#[test]
fn run_inference_enumerate_functions() {
    // In this model, there are two ways to get the fixed-points: identity and negation.
    Command::cargo_bin("inference_problem_solver")
        .unwrap()
        .arg("data/example_simple/two-fixed-points.aeon")
        .arg("--solutions=200")
        .arg("--print-update-rules")
        .arg("--projection=$*")
        .assert()
        .success()
        .stdout(contains("Solution #2").and(contains("Solution #3").not()))
        .stdout(contains("1 <- (x_0 == 1);").and(contains("1 <- (x_0 == 0);")));
}

#[test]
fn run_inference_toy_model_4v_fully_specified() {
    // Run the test on a fully specified 4-variable model with activations only.
    // The model has three fixed points '0000', '0100', '1111'.
    // The specification requires two fixed points '0110' (fp_1) and '0001' (fp_2).

    // In other words, exact inference should fail, but weighted should work,
    // with error 1 (0.5+0.5).

    Command::cargo_bin("inference_problem_solver")
        .unwrap()
        .arg("data/toy_models/4v-activ-fully-spec.aeon")
        .assert()
        .success()
        .stdout(ends_with("0\n"));

    Command::cargo_bin("inference_problem_solver_weighted")
        .unwrap()
        .arg("data/toy_models/4v-activ-fully-spec.aeon")
        .assert()
        .success()
        .stdout(ends_with("1\n"))
        .stdout(contains("[Some(1), Some(1)]\n"));
}
