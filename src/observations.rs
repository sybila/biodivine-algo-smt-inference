use crate::{InferenceProblem, StateSpecification};
use biodivine_lib_param_bn::BooleanNetwork;
use num_rational::BigRational;
use num_traits::FromPrimitive;
use std::collections::BTreeMap;

/// A single observation, i.e., a mapping from variables to binary values.
///
/// TODO: add proper weights
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Observation {
    pub values: BTreeMap<String, bool>,
}

impl Observation {
    /// Create `Observation` object from prepared value map.
    pub fn new(values: BTreeMap<String, bool>) -> Observation {
        Self { values }
    }
}

/// Serializable struct to load and represent a dataset of observations.
///
/// Each observation is a named assignment of binary values to a subset of
/// the dataset's `variables`.
///
/// TODO: add proper weights
#[derive(Clone, Debug, PartialEq)]
pub struct Dataset {
    pub observations: BTreeMap<String, Observation>,
    pub variables: Vec<String>,
}

impl Dataset {
    /// Parse a dataset from a CSV string. The header line specifies variables, following lines
    /// represent individual observations (id and values).
    ///
    /// The resulting dataset has an empty annotation string (same for all its observations).
    ///
    /// For example, the following might be a valid CSV string for a dataset with 2 observations:
    ///    ID,YOX1,CLN3,YHP1,ACE2,SWI5,MBF
    ///    Observation1,0,1,0,1,0,1
    ///    Observation2,1,0,*,1,0,*
    ///
    /// TODO: Add weights
    ///
    pub fn parse_dataset_from_csv(csv_content: &str) -> Result<Dataset, String> {
        let mut reader = csv::Reader::from_reader(csv_content.as_bytes());

        // parse variable names from the header (skip ID column)
        let header = reader.headers().map_err(|e| e.to_string())?.clone();
        let variables = header
            .iter()
            .skip(1)
            .map(|s| s.to_string())
            .collect::<Vec<String>>();

        // parse all rows as observations and build a map id -> Observation
        let mut observations: BTreeMap<String, Observation> = BTreeMap::new();
        for result in reader.records() {
            let record = result.map_err(|e| e.to_string())?;
            if record.is_empty() {
                return Err("Cannot import empty observation.".to_string());
            }

            let id = record.get(0).unwrap().to_string().trim().to_string();

            // require the same number of value columns as variables
            if record.len().saturating_sub(1) != variables.len() {
                return Err(format!(
                    "Observation '{}' has {} value columns but header lists {} variables",
                    id,
                    record.len().saturating_sub(1),
                    variables.len()
                ));
            }

            let mut values_map: BTreeMap<String, bool> = BTreeMap::new();
            for (var_name, cell) in variables.iter().zip(record.iter().skip(1)) {
                let var_name = var_name.trim();
                match cell.trim() {
                    "0" => {
                        values_map.insert(var_name.to_string(), false);
                    }
                    "1" => {
                        values_map.insert(var_name.to_string(), true);
                    }
                    "" | "*" | "ND" | "?" => {
                        // unspecified / ignored value -> do not insert into the map
                    }
                    other => {
                        return Err(format!(
                            "Invalid cell value '{}' for variable '{}' in observation '{}'",
                            other, var_name, id
                        ));
                    }
                }
            }

            let observation = Observation::new(values_map);
            observations.insert(id.to_string(), observation);
        }

        Ok(Dataset {
            observations,
            variables,
        })
    }

    /// Load a dataset from a given CSV file. Reads the file into a string and then parses it
    /// into a dataset using [Self::parse_dataset_from_csv].
    pub fn load_dataset(csv_path: &str) -> Result<Dataset, String> {
        let csv_content = std::fs::read_to_string(csv_path).map_err(|e| e.to_string())?;
        Self::parse_dataset_from_csv(&csv_content)
    }

    /// Convert this dataset into a list of `StateSpecification` objects using the provided
    /// `BooleanNetwork` to map variable names to `VariableId` indices.
    ///
    /// Each observation in the dataset becomes a `StateSpecification` where all observed
    /// values are asserted as a "may" constraints with uniform weight (0.5).
    ///
    /// Returns an error if any variable name in the dataset does not exist in the network.
    ///
    /// TODO: Add proper weights
    pub fn to_specification_list(
        &self,
        network: &BooleanNetwork,
    ) -> Result<BTreeMap<String, StateSpecification>, String> {
        let mut specs = BTreeMap::new();

        for (obs_id, observation) in &self.observations {
            let mut spec = StateSpecification::new();

            // For each variable value in the observation, find its VariableId in the network
            // and assert it as a "must" constraint.
            for (var_name, value) in &observation.values {
                // Find the VariableId by name in the network
                let var_id = network
                    .as_graph()
                    .find_variable(var_name)
                    .ok_or_else(|| format!("Variable '{}' not found in the network", var_name))?;

                let weight = BigRational::from_f32(0.5).unwrap();
                spec.assert_may(var_id, *value, &weight);
            }

            specs.insert(obs_id.clone(), spec);
        }

        Ok(specs)
    }

    /// Combine this dataset with the provided `BooleanNetwork` into an `InferenceProblem`
    /// instance.
    ///
    /// The dataset is used to derive fixed-point specification. See [`Self::to_specifications`]
    /// for details.
    ///
    /// Returns an error if any variable name in the dataset does not exist in the network.
    ///
    /// TODO: Add proper weights
    pub fn to_inference_problem(
        &self,
        network: &BooleanNetwork,
    ) -> Result<InferenceProblem, String> {
        let specs = self.to_specification_list(network)?;

        let mut problem = InferenceProblem::new(network.clone());
        for (obs_id, obs_specification) in specs {
            problem.make_state(&obs_id);
            problem.assert_fixed_point(&obs_id);
            problem.assert_state_observation(&obs_id, &obs_specification);
        }

        Ok(problem)
    }
}
