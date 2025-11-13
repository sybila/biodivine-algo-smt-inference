Some Python scripts for quick model analysis to design useful toy test cases and so on. These may become the part of the Rust codebase later, or can be removed. The scripts usually rely on the [aeon.py](https://pypi.org/project/biodivine-aeon/) library.
- `check_fixed_points.py` - explores all fixed-point combinations of a coloured model. Not usable for large PSBNs since it enumerates the model interpretations for output.
- `inference_from_imprecise_fps.py` - runs naive inference procedure, starting from a given PSBN and potentially imprecise fixed-point specification. It uses BDD representation to compute fixed points for all model interpretations at once, and then tries to "loosen" the specification until some satisfying interpretations are found. For now, this loosening is done in a naive enumerative way, and all observation values are considered with uniform equal weights.

Examples to run from main repo dir:
```
python3 scripts/check_fixed_points.py data/myeloid/myeloid-fully-specified.aeon
python3 scripts/naive_fps_inference.py data/myeloid/myeloid-fully-specified.aeon data/myeloid/dataset-fps-original-UNSAT.csv
```