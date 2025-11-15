Various models and datasets for testing, benchmarking, and case studies.

- `myeloid` contains a simple model of 12 variables describing blood cell differentiation.The model and data comes from the following two papers: [Hierarchical Differentiation of Myeloid Progenitors Is Encoded in the Transcription Factor Network](https://doi.org/10.1371/journal.pone.0022649) (original work), [A Method to Identify and Analyze Biological Programs through Automated Reasoning](10.1038/npjsba.2016.10) (follow-up work and case study).
  - There is a fully specified BN model crafted by the authors of the first paper. Then, there are two datasets. The authors first designed a fixed-point dataset based on experiments, but since they were not able to fit it, they modified it a bit (single bit flip).
- `toy_models` contains a few very small toy examples. For each model, there is a fully specified version, a partially specified variant, and a specification CSV.
  - `4v-activ` is a sparse 4-variable model with activations only
  - `4v-B` is a more dense model with various regulations
  - `5v` is a 5-variable extension of the `4v-B` model