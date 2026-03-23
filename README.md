# SMT inference of Boolean networks from uncertain data

This repository implements a prototype tool for inference of logic-based models (Boolean and Thomas networks) from biological observations. Internally, the tool uses SMT and uninterpreted functions to encode the properties of the desired model into a query processed by the Z3 solver. The project also provides standalone solvers that wrap the existing Z3 API and extend it with support for monotonic function arguments and bounded integers (see also the [architecture diagram](./ARCHITECTURE_DIAGRAM.png)).

### Exact inference solver

To build the main binary, make sure you have Rust toolchain installed, then run `cargo build --release --bin inference_problem_solver`. The resulting binary should be located in `./target/release/`.

Alternatively, you can also directly run the solver using:
```
cargo run --release --bin inference_problem_solver -- [OPTIONS] <INPUT_PATH>
```

Use `--help` to list the available options. The input file is an `.aeon` model file containing desired regulations of the influence graph, interpreted as follows:

```
# Essential activation
a -> b
# Essential inhibition
a -| b
# Essential without monotonicity
a -? b
# Non-essential activation / inhibition
a ->? b
a -|? b
# Non-essential without monotonicity
a -?? b
```

Any update function in the `.aeon` file are ignored. To specify desired fixed-points, use model annotations as follows:

```
# Enforces existence of fixed point with ID "1" and variable assignment a=1, b=0, c=1. 
# Unused variables are left unconstrained. 
#!fix:1:#`{"a": 1, "b": 0, "c": 1}`#
```

To specify that a variable is multivalued, you have to explicitly declare its domain as follows:

```
# Domain of variable with name "v93" is [0,1,2]. 
#!variable:v93:max_value:2
```

By default, the solver only prints `0/1/?` to indicate that the query is SAT/UNSAT/UNKNOWN. If the model is Boolean, you can print it to a file using `--output-path`. For Boolean and multivalued models, you can also print the update rules directly using a proprietary format with `--print-update-rules`. Use option `--solver` to choose a strategy, which can be one of `instantiated-eager` (default), `instantiated-lazy`, `quantified-individual`, `quantified-merge`.

### Input format

Input for the inference process is an `.aeon` file, describing a partially specified Boolean network. Additional constraints for the inference solver are given as "annotations" within the `.aeon` file. The order of constraints in the file does not influence satisfiability, but it can influence computation time, since it also changes the order in which assertions are given to the solver.

**Soft constraints** | For some constraints, we indicate that they can be augmented with `weight` (decimal; default is `1.0`) and `priority_class` (int; default is `0`) to indicate that they are *soft constraints*. Soft constraints do not have to be satisfied, but the solver will try to minimize the weight of violated soft constraints in each priority class, with priority classes being sorted in ascending order. 

**Regulation constraints** | The influence graph within the `.aeon` file directly encodes the regulation properties, which are interpreted according to the following mapping:

```
a -> b # essential, monotone (activation)
a -| b # essential, anti-monotone (inhibition)
a -? b # essential, no monotonicity constraint
a ->? b # monotone (activation), no essentiality constraint
a -|? b # anti-monotonce (inhibition), no essentiality constraint
a -?? b # no constraints
```

**Partially specified update functions** | In the `.aeon` file, you can partially define selected update functions of the model using uninterpreted function symbols. *This feature is currently not supported by the inference solver. However, soon you should be able to specify concrete update functions for variables where they are fully known. Support for general uninterpreted expressions is then coming later.*

**Variable domains** | By default, all variables are Boolean. If you wish to define certain variable as multivalued, use the following annotation:

```
# Domain of variable with name "v93" is [0,1,2].
 
#!variable:v93:max_value:2
```

Note that multivalued models currently cannot be written out as `.aeon` models using `--output-path`. However, you can use `--print-update-rules` to show the resulting update functions.

**State declarations** | You can declare the existence of model states with specific properties that the inference engine will try to match. In general, you use `state_name/variable_name` to reference the value of a variable in a declared state, but constraints are allowed to change this convention if necessary. State names must start with a letter and can only contain letters, numbers, and underscores.

```
# All states that are referenced somewhere 
# in the file have to be declared. Duplicate 
# declarations are not allowed.

#!state:declare:stateA
#!state:declare:stateB
```

**Comparison constraints** | As suggested by the name, comparison constraints compare two values using one of `equal`, `not_equal`, `less`, `less_equal`, `greater`, and `greater_equal`. The compared values must have the same "type" and can be:

 - The value of a variable in a state, e.g., `stateA/variableX`;
 - The output of an update function evaluated in a state, e.g. `$variableX/stateA`.
 - An `int` constant (with `1` interpreted as `true`, and `0` as `false`).

In general, all comparison constraints can be also given as soft constraints.

```
# Assert that `stateA/varX >= stateB/varX`. The trailing `:` 
# indicates that the constraint has no weight or priority class.

#! comparison : greater_equal : stateA/varX : stateB/varX :

# Assert that `stateA/varX` is equal to update function of `varX`
# evaluated in `stateB`.

#! comparison : equal : stateA/varX : $varX/stateB :
```

**General state constraints** | It is possible to express many properties using combinations of comparisons as described above. However, for convenience, we also provide the following general state constraints, which are effectively just conjunctions of comparisons involving different states and update functions. An advantage of this formulation is that these combined constraints can have their weight and/or priority class assigned as a whole.

```
# Assert that `stateA == stateB` with weight `1.2`, 
# and `stateA != stateB` with weight `0.8`, 
# both in the default priority class `0`.

#! state : equal : stateA : state B : weight : 1.2
#! state : not_equal : stateA : state B : weight : 0.8

# Soft constraints with default weight `1` in priority class `2`
# that assert `stateA` and `stateB` are a fixed-points.

#! state : fixed_point : stateA : priority_class : 2
#! state : fixed_point : stateB : priority_class : 2
```

Note that for the whole states, the only supported comparisons are `equal` and `not-equal`, as there are multiple partial orders that we could consider to implement the remaining comparisons.

 > Soon, an option to express state successors as a single constraint should be added as well.