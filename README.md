# SMT inference of Boolean networks from uncertain data

This repository implements a prototype tool for inference of logic-based models (Boolean and Thomas networks) from biological observations. Internally, the tool uses SMT and uninterpreted functions to encode the properties of the desired model into a query processed by the Z3 solver. The project also provides standalone solvers that wrap the existing Z3 API and extend it with support for monotonic function arguments and bounded integers (see also the [architecture diagram](./ARCHITECTURE_DIAGRAM.png)).

### Inference solver binaries

There are currently two solver binaries: An exact solver and a weighted solver. To build either binary, make sure you have the Rust toolchain installed, then run `cargo build --release --bin inference_problem_solver` or `cargo build --release --bin inference_problem_solver_weighted`. The resulting binary should be located in `./target/release/`.

Alternatively, you can also directly run the solver using:
```
cargo run --release --bin inference_problem_solver -- [OPTIONS] <INPUT_PATH>
cargo run --release --bin inference_problem_solver_weighted -- [OPTIONS] <INPUT_PATH>
```

Use `--help` to list the available options. The input file is an `.aeon` model file containing desired regulations of the influence graph, with the constraint language described below.

By default, the solver only prints `0/1/?` to indicate that the query is SAT/UNSAT/UNKNOWN. If the model is Boolean, you can print it to a file using `--output-path`. For Boolean and multivalued models, you can also print the update rules directly using a proprietary format with `--print-update-rules`. Use option `--solver` to choose a strategy, which can be one of `instantiated-eager` (default), `instantiated-lazy`, `quantified-individual`, `quantified-merge`. In the weighted solver, you can specify `--print-intermediate-results` to print a result whenever the solver discovers a better incremental solution.

### Input format

Input for the inference process is an `.aeon` file, describing a partially specified Boolean network. Additional constraints for the inference solver are given as "annotations" within the `.aeon` file. The order of constraints in the file does not influence satisfiability, but it can influence computation time, since it also changes the order in which assertions are given to the solver.

**Soft constraints** For some constraints, we indicate that they can be augmented with `weight` (decimal; default is `1.0`) and `priority_class` (int; default is `0`) to indicate that they are *soft constraints*. Soft constraints do not have to be satisfied, but the solver will try to minimize the weight of violated soft constraints in each priority class, with priority classes being sorted in ascending order. Some examples are given at later in this tutorial. 

**Regulation constraints** The influence graph within the `.aeon` file directly encodes the regulation properties, which are interpreted according to the following mapping:

```
a -> b # essential, monotone (activation)
a -| b # essential, anti-monotone (inhibition)
a -? b # essential, no monotonicity constraint
a ->? b # monotone (activation), no essentiality constraint
a -|? b # anti-monotonce (inhibition), no essentiality constraint
a -?? b # no constraints
```

**Partially specified update functions** In the `.aeon` file, you can partially define selected update functions of the model using uninterpreted function symbols. *This feature is currently not supported by the inference solver. However, soon you should be able to specify concrete update functions for variables where they are fully known. Support for general uninterpreted expressions is then coming later.*

**Variable domains** By default, all variables are Boolean. If you wish to define certain variable as multivalued, use the following annotation:

```
# Domain of variable with name "v93" is [0,1,2].

#! variable : v93 : max_value : 2
```

Note that multivalued models currently cannot be written out as `.aeon` models using `--output-path`. However, you can use `--print-update-rules` to show the resulting update functions.

**State declarations** You can declare the existence of model states with specific properties that the inference engine will try to match. In general, you use `state_name/variable_name` to reference the value of a variable in a declared state. State names must start with a letter and can only contain letters, numbers, and underscores.

```
# All states that are referenced somewhere 
# in the file have to be declared. Duplicate 
# declarations are not allowed.

#! state : declare : stateA
#! state : declare : stateB
```

**Comparison constraints** As suggested by the name, comparison constraints compare two values using one of `equal`, `not_equal`, `less`, `less_equal`, `greater`, and `greater_equal`. The compared values must have the same "type" and can be:

 - The value of a variable in a state, e.g., `stateA/variableX`;
 - The output of an update function evaluated in a state, e.g. `$variableX/stateA`.
 - An `int` constant (with `1` interpreted as `true`, and `0` as `false`).

The compared values need to be enclosed in backticks (i.e, \`). In general, all comparison constraints can be also given as soft constraints.

```
# Assert that 'stateA/varX >= stateB/varX'. The trailing `:` 
# indicates that the constraint has no weight or priority class.

#! comparison : greater_equal : `stateA/varX` : `stateB/varX` :

# Assert that 'stateA/varX' is equal to update function of 'varX'
# evaluated in 'stateB'.

#! comparison : equal : `stateA/varX` : `$varX/stateB` :
```

**General state constraints** | It is possible to express many properties using combinations of comparisons as described above. However, for convenience, we also provide the following general state constraints, which are effectively just conjunctions of comparisons involving different states and update functions. An advantage of this formulation is that these combined constraints can have their weight and/or priority class assigned as a whole.

```
# Assert that 'stateA == stateB' with weight '1.2', 
# and 'stateA != stateB' with weight '0.8', 
# both in the default priority class '0'.

#! state : equal : stateA : stateB : weight : 1.2
#! state : not_equal : stateA : stateB : weight : 0.8

# Soft constraints with default weight '1' in priority class '2'
# that assert 'stateA' and 'stateB' are a fixed-points.

#! state : fixed_point : stateA : priority_class : 2
#! state : fixed_point : stateB : priority_class : 2
```

Note that for the whole states, the only supported comparisons are `equal` and `not-equal`, as there are multiple partial orders that we could consider to implement the remaining comparisons.

### Enumeration of solutions

> WARNING: Enumeration of multiple solutions in the weighted solver is not supported, but is technically feasible
> and will be coming in later versions. 

By default, the solver will report `0/1` to indicate that the problem is UNSAT/SAT (it can also report `?` if the
solving process is interrupted). If you specify some `--print-*` argument, the respective part of the solution will
be also printed (assuming the solution exists).

If you want to enumerate more than one solution, use `--solutions=X` to indicate an upper limit. You can then
use one or more `--projection=X` arguments to indicate that you only want the enumerated solutions to be unique
with respect to some subset of the specification (specific variable in a state = `state/var`, all variables in
a state = `state/*`, specific variable across all states = `*/var`, all state data = `*/*`, specific update function
 = `$var`, all update functions = `$*`; don't forget to escape `$` if running from `bash`). The solver will
still print everything that was requested, but only enforce uniqueness for the items indicated by `--projection`.

**Important note on function enumeration:** Currently, the solver does not enumerate specific functions, but rather
"classes of partial function specifications", such that all functions in a class are indistinguishable by the provided
inference problem. Due to some technical limitations, the class is simply reported using one representative function.
In the future, we want to provide a more rigorous way to print the whole class, not just one function from it.

As an example, consider an inference problem that does not use function `f(x, y)` at all. Then, the solver will only
report one "class of functions" (represented by `f(x, y) = false`), because from the point of view of the inference
problem, it is irrelevant which `f` is chosen. Similarly, if the inference problem only requires that `f(1,1) = 1`,
the solver will only report `f(x,y) = x & y` because all the other functions that satisfy the specification agree
with `x & y` on the value of `f(1,1)`. In other words, multiple function classes are typically only reported when
there are multiple different "sets of points" that the inference problem can enforce about `f`. For example, if
the inference problem enforces `f(1,1) = 1` OR `f(0,0) = 1`, then there would be two function classes, one represented
using `x & y` and the other represented by `!x & !y`.