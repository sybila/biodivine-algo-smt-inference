use biodivine_algo_smt_inference::{InferenceProblem, StateSpecification};
use biodivine_lib_param_bn::BooleanNetwork;
use csv::ReaderBuilder;
use num_rational::BigRational;
use num_traits::{FromPrimitive, ToPrimitive, Zero};
use std::collections::BTreeMap;
use std::fs::File;
use z3::ast::Dynamic;

fn main() {
    let obs_path = "./data/neural_differentiation/table_scc_observations.tsv";
    let conf_path = "./data/neural_differentiation/table_scc_confidence.tsv";

    let (obs_genes, obs_cells, obs_data) = load_table(obs_path);
    println!(
        "Loaded observations from {}: {} genes, {} cell types",
        obs_path,
        obs_genes.len(),
        obs_cells.len()
    );

    let (conf_genes, conf_cells, conf_data) = load_table(conf_path);
    println!(
        "Loaded confidence from {}: {} genes, {} cell types",
        conf_path,
        conf_genes.len(),
        conf_cells.len()
    );

    assert_eq!(obs_genes, conf_genes);
    assert_eq!(obs_cells, conf_cells);

    let mut observations = obs_cells
        .iter()
        .map(|it| (it.clone(), StateSpecification::new()))
        .collect::<BTreeMap<_, _>>();

    let mut model =
        BooleanNetwork::try_from_file("./data/neural_differentiation/omnipath_largest_scc.aeon")
            .unwrap();
    strip_monotonicity(&mut model);
    let model = model.name_implicit_parameters();

    let mut max_objective = BigRational::zero();
    for (gene, (obs_row, conf_row)) in obs_genes.iter().zip(obs_data.iter().zip(conf_data.iter())) {
        let Some(gene_id) = model.as_graph().find_variable(gene) else {
            continue;
        };

        for (cell_type, (obs, confs)) in obs_cells.iter().zip(obs_row.iter().zip(conf_row.iter())) {
            assert_eq!(obs.is_some(), confs.is_some());

            if let (Some(obs), Some(conf)) = (obs, confs) {
                assert!(*obs == 1.0 || *obs == 0.0);
                let obs = *obs == 1.0;
                let specification = observations.get_mut(cell_type).unwrap();
                if *conf == 1.0 {
                    specification.assert_must(gene_id, obs);
                } else {
                    let conf = BigRational::from_f64(*conf).unwrap();
                    max_objective += &conf;
                    specification.assert_may(gene_id, obs, &conf);
                }
            }
        }
    }

    for (cell, spec) in observations.iter() {
        let hard_spec = spec.make_required_assertion_map().len();
        let soft_spec = spec.make_optional_assertion_map().len();
        println!(
            "Cell type {cell} has {hard_spec} hard assertions and {soft_spec} soft assertions"
        );
    }

    let mut inference = InferenceProblem::new(model.clone());

    let mut states = BTreeMap::new();
    for (cell, spec) in observations.iter() {
        let state = inference.make_state(cell);
        states.insert(cell.to_string(), state);
        inference.assert_state_observation(cell, spec);
        inference.assert_fixed_point(cell);
    }

    println!("Starting solver...");

    let solver = inference.build_solver();
    println!("Has solution? {:?}", solver.check(&[]));
    println!(
        "Optimal solution has error {} (max error is {})",
        parse_fraction(solver.get_lower(0).unwrap()),
        max_objective.to_f64().unwrap()
    );

    let result = solver.get_model().unwrap();

    for (cell, state) in states {
        println!("Cell: {cell}");
        let req = observations.get(&cell).unwrap();
        let inferred_state = state.extract_state(&result);
        let mut penalty = BigRational::zero();
        let mut missed = 0;
        for (var, conf) in req.make_optional_assertion_map() {
            let actual = inferred_state[var.to_index()];
            if actual != conf.0 {
                penalty += &conf.1;
                missed += 1;
            }
        }
        println!(
            "Missed: {missed} with penalty {}",
            penalty.to_f64().unwrap()
        );
    }
}

fn parse_fraction(ast: Dynamic) -> f64 {
    ast.as_real().unwrap().approx_f64()
}

fn strip_monotonicity(model: &mut BooleanNetwork) {
    for mut reg in model.as_graph().regulations().cloned().collect::<Vec<_>>() {
        model
            .as_graph_mut()
            .remove_regulation(reg.regulator, reg.target)
            .unwrap();
        reg.monotonicity = None;
        model.as_graph_mut().add_raw_regulation(reg).unwrap();
    }
}

fn load_table(path: &str) -> (Vec<String>, Vec<String>, Vec<Vec<Option<f64>>>) {
    let file = File::open(path).unwrap();
    let mut rdr = ReaderBuilder::new().delimiter(b'\t').from_reader(file);

    let headers = rdr.headers().unwrap().clone();
    // First column is "gene", skip it to get cell types
    let cell_types: Vec<String> = headers.iter().skip(1).map(|s| s.to_string()).collect();

    let mut genes = Vec::new();
    let mut data = Vec::new();

    for result in rdr.records() {
        let record = result.unwrap();
        // First column is gene name
        let gene = record
            .get(0)
            .ok_or("Missing gene name")
            .unwrap()
            .to_string();
        genes.push(gene);

        let mut row_data = Vec::new();
        for i in 1..record.len() {
            let val_str = record.get(i).unwrap_or("");
            let val = if val_str.trim().is_empty() {
                None
            } else {
                Some(val_str.trim().parse::<f64>().unwrap())
            };
            row_data.push(val);
        }

        // Verify row length matches cell_types length (optional but good)
        if row_data.len() != cell_types.len() {
            // It's possible record.len() varies if csv isn't strictly rectangular, but usually it is.
            // csv crate ensures records match header length by default unless flexible is set.
            // But let's trust the csv crate's default behavior (strict).
        }

        data.push(row_data);
    }

    (genes, cell_types, data)
}
