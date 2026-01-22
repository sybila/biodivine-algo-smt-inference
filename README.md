# SMT inference of Boolean networks from uncertain data

Work in progress...


### How to run

There is currently one "large benchmark" based on neural cell differentiation. The benchmark has two variants: Smaller "scc" variant (only covers strongly connected component of transcription factors; 308 genes) and "full" variant (also includes various network "outputs"; 8379 genes). Both variants have some soft and hard observations based on a real scRNA-seq dataset. However, the hard observations are not satisfiable in the "full" variant; therefore, we also allow overriding all hard constraints with soft ones (using a high weight). Finally, since the number of monotonic regulation constraints has a strong impact on runtime, you can set how many of them should be "retained" (the rest will be ignored).

To run the benchmark, use:

```bash
cargo run --release --bin example_neural_differentiation $TYPE $OVERRIDE $MONOTONIC
```

Here, `$TYPE` is either `scc` (smaller problem) or `full` (larger problem). `$OVERRIDE` is either `retain_hard` (keeps hard contraints as given in the observations file) or `override_soft` (overrides all hard constraints with soft ones). Finally, `$MONOTONIC` is the number of regulation constraints that should be retained (additional constraints are simply ignored).

 > For the `full` variant, `retain_hard` option always returns `unsat`. Only `override_soft` returns valid solutions. For the `scc` variant, both options should work, but can differ in computation time.
