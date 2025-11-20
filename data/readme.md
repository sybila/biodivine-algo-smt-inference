Various models and datasets for testing, benchmarking, and case studies.

- `myeloid` contains a simple model of 12 variables describing blood cell differentiation.The model and data comes from the following two papers: [Hierarchical Differentiation of Myeloid Progenitors Is Encoded in the Transcription Factor Network](https://doi.org/10.1371/journal.pone.0022649) (original work), [A Method to Identify and Analyze Biological Programs through Automated Reasoning](10.1038/npjsba.2016.10) (follow-up work and case study).
  - There is a fully specified BN model crafted by the authors of the first paper. Then, there are two datasets. The authors first designed a fixed-point dataset based on experiments, but since they were not able to fit it, they modified it a bit (single bit flip).
- `toy_models` contains a few very small toy examples. For each model, there is a fully specified version, a partially specified variant, and a specification CSV.
  - `4v-activ` is a sparse 4-variable model with activations only
  - `4v-B` is a more dense model with various regulations
  - `5v` is a 5-variable extension of the `4v-B` model
- `neural_differentiation` contains a large benchmark instance based on real biological data.
  - The biological data comes from [this study](https://www.nature.com/articles/s41586-021-03670-5) of neural cell differentiation.
  - The data has been binarized using scBoolSeq on a per-cell-type basis (i.e. not per-measurement, but per "cluster of similar cells").
    - Here, the binarization process can produce 0/1/nan, i.e. some portion of values remains unknown.
  - Confidence scores were then assigned to each binarized value based on differential expression.
    - This process compares the distribution of RNA measurements between said value and all distributions across values of the same gene binarized to a different value.
    - Intuitively, if the value is 1, the confidence expresses "how different is the distribution of these measurements compared to closes zero".
  - A literature-based "base GRN" was obtained from OmniPath. 
    - This GRN has a lot of relevant genes (4000+), but only a relatively small portion represents a strongly connected component.
    - Also, in this setting, we definitely do not expect all regulations to be essential (i.e. we do not have evidence that they play a role *in this particular biological process*, just that they are common across various cells).
    - This allows us to "scale" the inference problem: The smallest instance should cover the central SCC. Then we can gradually add other "input/output" variables as needed.
    - Some of the data was filtered using `preprocess_data.py`, but all outputs should be commited in the repository.