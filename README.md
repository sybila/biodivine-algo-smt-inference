# SMT inference of Boolean networks from uncertain data

Work in progress...

### Benchmarking binary (hard constraints, single solution)

There is now binary `inference_problem_solver` for benchmarking the SMT strategies on boolean (and multi-valued) network inference with hard constraints. It takes an AEON model file containing a regulatory graph (including monotonicity/essentiality constraints) complemented with fixed points specification in model annotations. If the model is multi-valued, there should also be additional annotations specifying maximal values of each variable.  

The binary runs a selected solver strategy and computes a single solution. By default, it prints 0/1/? on standard output to signify whether the z3 determined the input was SAT/UNSAT/UNKNOWN. The resulting model can be fully extracted and saved (for boolean cases) or printed.

Compile and run it using the command below. Use option `--solver` to choose a strategy, which can be one of `instantiated-eager` (default), `instantiated-lazy`, `quantified-individual`, `quantified-merge`. You can use `--help` flag for more information on arguments and additional options (such as `output-path`, `verbose`, and various optimization flags).

```
cargo run --release --bin inference_problem_solver [OPTIONS] <MODEL_PATH>
```

### How to run optimization

There is currently one "large benchmark" based on neural cell differentiation. The benchmark has two variants: Smaller "scc" variant (only covers strongly connected component of transcription factors; 308 genes) and "full" variant (also includes various network "outputs"; 8379 genes). Both variants have some soft and hard observations based on a real scRNA-seq dataset. However, the hard observations are not satisfiable in the "full" variant; therefore, we also allow overriding all hard constraints with soft ones (using a high weight). Finally, since the number of monotonic regulation constraints has a strong impact on runtime, you can set how many of them should be "retained" (the rest will be ignored).

To run the benchmark, use:

```bash
cargo run --release --bin example_neural_differentiation $TYPE $OVERRIDE $MONOTONIC
```

Here, `$TYPE` is either `scc` (smaller problem) or `full` (larger problem). `$OVERRIDE` is either `retain_hard` (keeps hard contraints as given in the observations file) or `override_soft` (overrides all hard constraints with soft ones). Finally, `$MONOTONIC` is the number of regulation constraints that should be retained (additional constraints are simply ignored).

 > For the `full` variant, `retain_hard` option always returns `unsat`. Only `override_soft` returns valid solutions. For the `scc` variant, both options should work, but can differ in computation time.
