import os
import pandas as pd
from pathlib import Path
from copy import copy

from biodivine_aeon import RegulatoryGraph

def get_monotonicity(is_stim, is_inhib):
    if is_stim and not is_inhib:
        return "activation"
    elif is_inhib and not is_stim:
        return "inhibition"
    else:
        return None

def main():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Input files
    omnipath_file = os.path.join(base_dir, "omnipath_full.tsv")
    confidence_file = os.path.join(base_dir, "table_full_confidence.tsv")
    observations_file = os.path.join(base_dir, "table_full_observations.tsv")
    
    # Check inputs exist
    for f in [omnipath_file, confidence_file, observations_file]:
        if not os.path.exists(f):
            print(f"Error: Input file {f} not found.")
            return

    # Output files
    full_graph_file = os.path.join(base_dir, "omnipath_full.aeon")
    scc_graph_file = os.path.join(base_dir, "omnipath_largest_scc.aeon")
    scc_genes_file = os.path.join(base_dir, "omnipath_largest_scc_genes.txt")
    scc_confidence_file = os.path.join(base_dir, "table_scc_confidence.tsv")
    scc_observations_file = os.path.join(base_dir, "table_scc_observations.tsv")

    # Load observed genes
    observed_genes_file = os.path.join(base_dir, "observed_genes.txt")
    print(f"Loading allowed genes from {observed_genes_file}...")
    if not os.path.exists(observed_genes_file):
        print(f"Error: {observed_genes_file} not found.")
        return
        
    allowed_genes = eval(Path(observed_genes_file).read_text())
        
    print(f"Found {len(allowed_genes)} allowed genes.")

    # (a) Load gene-gene regulations
    print(f"Loading regulations from {omnipath_file}...")
    df_omnipath = pd.read_csv(omnipath_file, sep='\t')
    
    edges = []
    genes = set()
    
    for _, row in df_omnipath.iterrows():
        source = str(row['source_genesymbol'])
        target = str(row['target_genesymbol'])
        
        # Skip invalid gene names if any
        if source.lower() == 'nan' or target.lower() == 'nan':
            continue
            
        # FILTER: Only use genes that appear in table_full_observations.tsv
        if source not in allowed_genes or target not in allowed_genes:
            continue

        # Parse booleans safely (pandas usually handles this, but being explicit is safer if mixed types)
        def parse_bool(val):
            if isinstance(val, bool):
                return val
            return str(val).lower() == 'true'

        is_stim = parse_bool(row['consensus_stimulation'])
        is_inhib = parse_bool(row['consensus_inhibition'])
        
        edges.append((source, target, is_stim, is_inhib))
        genes.add(source)
        genes.add(target)
        
    print(f"Found {len(genes)} genes and {len(edges)} regulations after filtering.")

    # (b) Build RegulatoryGraph
    print("Building full RegulatoryGraph...")
    sorted_genes = sorted(list(genes))
    
    rg = RegulatoryGraph(sorted_genes)
    
    for source, target, is_stim, is_inhib in edges:
        # Determine monotonicity
        monotonicity = get_monotonicity(is_stim, is_inhib)
        
        # Add regulation: source, target, is_observable=False, monotonicity
        if rg.find_regulation(source, target) is None:
            rg.add_regulation({
                'source': source,
                'target': target,
                'essential': False,
                'monotonicity': monotonicity
            })

    # (c) Output full graph
    print(f"Saving full graph to {full_graph_file}...")
    Path(full_graph_file).write_text(rg.to_aeon())
    
    # (d) Run SCC decomposition
    
    print("Running SCC decomposition...")
    sccs = rg.strongly_connected_components()
    if not sccs:
        print("No SCCs found.")
        return

    largest_scc = max(sccs, key=len)

    print(f"Found {len(sccs)} SCCs. Largest SCC has {len(largest_scc)} genes.")

    # (e) Output SCC graph and genes
    print("Building SCC RegulatoryGraph...")
    rg_scc = copy(rg)
    rg_scc.drop(set(rg.variables()) - set(largest_scc))
    
    print(f"Saving SCC graph to {scc_graph_file}...")
    Path(scc_graph_file).write_text(rg_scc.to_aeon())
    
    print(f"Saving SCC genes to {scc_genes_file}...")
    scc_genes_set = { rg.get_variable_name(x) for x in largest_scc }
    Path(scc_genes_file).write_text(str(scc_genes_set))

    # (f) Filter tables
    print("Filtering tables...")
    
    df_conf = pd.read_csv(confidence_file, sep='\t')
    df_obs = pd.read_csv(observations_file, sep='\t')
    
    # Ensure 'gene' column is present
    if 'gene' not in df_conf.columns:
        print(f"Error: 'gene' column not found in {confidence_file}")
    if 'gene' not in df_obs.columns:
        print(f"Error: 'gene' column not found in {observations_file}")

    # Filter
    df_conf_scc = df_conf[df_conf['gene'].isin(scc_genes_set)]
    df_obs_scc = df_obs[df_obs['gene'].isin(scc_genes_set)]
    
    print(f"Saving filtered tables to {scc_confidence_file} and {scc_observations_file}...")
    df_conf_scc.to_csv(scc_confidence_file, sep='\t', index=False)
    df_obs_scc.to_csv(scc_observations_file, sep='\t', index=False)

    print("Preprocessing complete.")

if __name__ == "__main__":
    main()
