use biodivine_algo_smt_inference::bn_inference::constraints::{
    StateHasExactObservation, StateHasWeightedObservation, StateIsFixedPoint,
};
use biodivine_algo_smt_inference::bn_inference::{InferenceProblem, InferenceProblemEncoder};
use biodivine_algo_smt_inference::deprecated::state_specification::StateSpecification;
use biodivine_algo_smt_inference::smt_solver::{
    AbstractSolver, BoundedIntSolver, DynMonotoneBoundedIntOptimizeSolver,
    InstantiatedMonotoneSolver, QuantifiedMonotoneSolver,
};
use biodivine_lib_param_bn::BooleanNetwork;
use csv::ReaderBuilder;
use num_rational::BigRational;
use num_traits::{FromPrimitive, ToPrimitive, Zero};
use std::collections::BTreeMap;
use std::fs::File;
use z3::ast::Dynamic;

fn main() -> Result<(), anyhow::Error> {
    env_logger::init();
    let args = std::env::args().collect::<Vec<_>>();
    assert_eq!(
        args.len(),
        5,
        "Expected 4 arguments: (scc | full) (retain_hard | override_soft) #retained_monotonicity_constraints #solver"
    );

    let problem_type = args[1].clone();
    assert!(
        problem_type == "scc" || problem_type == "full",
        "First argument must be `scc` or `full`"
    );

    let retain_hard = args[2] == "retain_hard";
    assert!(
        args[2] == "retain_hard" || args[2] == "override_soft",
        "Second argument must be `retain_hard` or `override_soft`"
    );

    let retained_monotonicity = args[3]
        .parse::<usize>()
        .expect("Third argument must be a non-negative integer");

    let solver_class = &args[4];
    assert!(
        args[4] == "quantified" || args[4] == "instantiation",
        "Fourth argument must be `quantified` or `instantiation`"
    );

    let obs_path =
        format!("./data/neural_differentiation/table_{problem_type}_observations_filtered.tsv");
    let conf_path =
        format!("./data/neural_differentiation/table_{problem_type}_confidence_filtered.tsv");

    let (obs_genes, obs_cells, obs_data) = load_table(obs_path.as_str());
    println!(
        "Loaded observations from {}: {} genes, {} cell types",
        obs_path,
        obs_genes.len(),
        obs_cells.len()
    );

    let (conf_genes, conf_cells, conf_data) = load_table(conf_path.as_str());
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

    let mut model = BooleanNetwork::try_from_file(format!(
        "./data/neural_differentiation/omnipath_{problem_type}.aeon"
    ))
    .unwrap();

    strip_monotonicity(&mut model, retained_monotonicity);

    let model = model.name_implicit_parameters();

    let mut total_weights = BigRational::zero();
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
                    if retain_hard {
                        specification.assert_must(gene_id, obs);
                    } else {
                        // Overriding "must" assertions to ensure the query is always satisfiable.
                        let conf = BigRational::from_f64(0.9999999).unwrap();
                        total_weights += &conf;
                        specification.assert_may(gene_id, obs, &conf);
                    }
                } else {
                    let conf = BigRational::from_f64(*conf).unwrap();
                    total_weights += &conf;
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

    let mut inference_problem =
        InferenceProblem::<DynMonotoneBoundedIntOptimizeSolver>::from_influence_graph(
            model.as_graph(),
        )?;

    for (cell, spec) in observations.iter() {
        assert!(inference_problem.declare_state(cell.as_str()));
        let observation = spec.to_observation();
        let hard_obs_constraint =
            StateHasExactObservation::new(cell.as_str(), observation.only_exact_observations());
        let soft_obs_constraint = StateHasWeightedObservation::new(
            cell.as_str(),
            observation.only_weighted_observations(),
        );
        let fix_constraint = StateIsFixedPoint::new(cell.as_str());
        inference_problem.assert_constraint(hard_obs_constraint)?;
        inference_problem.assert_constraint(soft_obs_constraint)?;
        inference_problem.assert_constraint(fix_constraint)?;
    }

    println!("Starting solver...");

    let inner_solver = BoundedIntSolver::new_strict(z3::Optimize::new());
    let mut solver: DynMonotoneBoundedIntOptimizeSolver = if solver_class == "quantified" {
        Box::new(QuantifiedMonotoneSolver::new(inner_solver, true))
    } else {
        Box::new(InstantiatedMonotoneSolver::new(inner_solver))
    };

    let _encoder = InferenceProblemEncoder::new(inference_problem, &mut solver, true)?;

    //let states_copy = states.clone();
    //let observations_copy = observations.clone();
    solver.register_model_handler(Box::new(move |_result| {
        println!("Solver made progress!");
        //print_solver_model(result, &states_copy, &observations_copy);
    }));

    println!("Has solution? {:?}", solver.check());
    println!(
        "Optimal solution has penalty {} (max possible penalty is {})",
        parse_fraction(solver.get_lower(0).unwrap()),
        total_weights.to_f64().unwrap()
    );

    //if let Some(result) = solver.get_model() {
    //    print_solver_model(&result, &states, &observations);
    //}

    Ok(())
}

fn parse_fraction(ast: Dynamic) -> f64 {
    ast.as_real().unwrap().approx_f64()
}

fn strip_monotonicity(model: &mut BooleanNetwork, mut retain: usize) {
    for mut reg in model.as_graph().regulations().cloned().collect::<Vec<_>>() {
        if reg.monotonicity.is_none() {
            // Non-monotonic regulations are just ignored.
            continue;
        }

        if retain > 0 {
            // We retain the first X monotonic regulations we encounter.
            retain -= 1;
            continue;
        }

        // Otherwise replace the regulation with a new, non-monotonic one.
        model
            .as_graph_mut()
            .remove_regulation(reg.regulator, reg.target)
            .unwrap();
        reg.monotonicity = None;
        model.as_graph_mut().add_raw_regulation(reg).unwrap();
    }

    let still_monotonic = model
        .as_graph()
        .regulations()
        .filter(|it| it.monotonicity.is_some())
        .count();
    println!(
        "After filtering, number of monotonic regulations is: {}",
        still_monotonic
    );
}

// fn print_solver_model(
//     model: &Model,
//     states: &BTreeMap<String, SmtState>,
//     observations: &BTreeMap<String, StateSpecification>,
// ) {
//     println!("==== Model ====");
//     let mut total_penalty = BigRational::zero();
//     for (cell, state) in states.iter() {
//         print!("\t > Cell: {cell}; ");
//         let req = observations.get(cell).unwrap();
//         let inferred_state = state.extract_state(model);
//         let mut penalty = BigRational::zero();
//         let mut missed = 0;
//         for (var, conf) in req.make_optional_assertion_map() {
//             let actual = inferred_state[var.to_index()];
//             if actual != conf.0 {
//                 penalty += &conf.1;
//                 missed += 1;
//             }
//         }
//         println!(
//             "Missed: {missed} observations with penalty {}",
//             penalty.to_f64().unwrap()
//         );
//         total_penalty += penalty;
//     }
//     println!("Total penalty: {}", total_penalty.to_f64().unwrap());
// }

fn load_table(path: &str) -> (Vec<String>, Vec<String>, Vec<Vec<Option<f64>>>) {
    let file = File::open(path).unwrap();
    let mut rdr = ReaderBuilder::new().delimiter(b'\t').from_reader(file);

    let headers = rdr.headers().unwrap().clone();
    // The first column is "gene", skip it to get cell types
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
