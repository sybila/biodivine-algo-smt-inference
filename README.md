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

Additionally, you can control the amount of logging with option `--verbose`. This can provide additional information, such as the number of lemmas for instantiation-based approaches, or number of iterations performed by the lazy instantiation approach.

You can also override the internal Z3 solver parameters with `--z3-param` option (for example, use as `--z3-param smt.ematching=false`, or see help message for more details). You can also override the default Z3 tactic with option `--z3-tactic` (for example, use as `--z3-tactic qsat`, or see help message for more details).
