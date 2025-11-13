"""Naive BN inference from imprecise fixed-point specification

This script runs naive inference procedure, starting from a given PSBN and
potentially imprecise fixed-point specification. It uses BDD representation
to compute fixed points for all model interpretations at once, and then tries
to "loosen" the specification until some satisfying interpretations are found. 

For now, this loosening is done in a naive enumerative way, one bit value at 
a time, and all observation values are considered with uniform equal weights.

It is not usable for large models with very imprecise specification since it 
handles the loosened specification variants in an enumerative way. However, if
we can fit the data with up to ~6 bit flips, this works kinda well for models 
of any size.

Usage: python naive_fps_inference.py <psbn_file> <specification_csv> [--print-colors]
"""

import sys
import os
import csv
import copy
from itertools import combinations
from biodivine_aeon import AsynchronousGraph, BooleanNetwork, FixedPoints


def parse_observations_csv(csv_path):
    """Parse observations from a specification CSV into a dict.

    Expected CSV format:
      ID, v_1, v_2, v_3, ...
      observation_1, 1, 0, 1, ...
      observation_2, 0, 0, 0, ...
      ...

    Empty cells are treated as unspecified (variable omitted from that fixed-point dict).
    Returns: {observation: {var_name: int(value), ...}, ...}
    """
    if not os.path.exists(csv_path):
        raise FileNotFoundError(f"Specification CSV not found: {csv_path}")

    spec = {}
    with open(csv_path, newline='') as f:
        reader = csv.reader(f)
        try:
            header = next(reader)
        except:
            raise ValueError(f"Specification file is empty.")

        # header[0] expected to be the ID column
        vars = [h.strip() for h in header[1:]]
        if len(vars) == 0:
            raise ValueError(f"List of variables is empty.")
        for row in reader:
            # skip empty or whitespace-only rows (no constraints)
            if not row or all(not c.strip() for c in row):
                continue

            obs_id = row[0].strip()
            values = {}
            for var, cell in zip(vars, row[1:]):
                cell = cell.strip()
                if cell == "":
                    continue  # unspecified
                elif cell == "1":
                    values[var] = True
                elif cell == "0":
                    values[var] = False
                else:
                    # Throw error on any other than binary value
                    raise ValueError(f"Unsupported specification value `{cell}`.")
            spec[obs_id] = values
    if len(spec) == 0:
        raise ValueError(f"Specification file has no observations.")
    return spec


def loosen_specification(full_specification, ignore_indices):
    """
    Remove specific (fp, var) entries from the full specification.
    This effectively loosens the original specification, removing some constraints.
    """
    result = copy.deepcopy(full_specification)
    for fp, var in ignore_indices:
        if fp in result and var in result[fp]:
            del result[fp][var]
    return result


def main(psbn_path, csv_path, print_colors):
    # Load Boolean network and build colored STG
    bn = BooleanNetwork.from_file(psbn_path)
    bn = bn.infer_valid_graph()
    stg = AsynchronousGraph(bn)

    print(f"Total variables: {bn.variable_count()}")
    print(f"Total colors: {stg.mk_unit_colors().cardinality()}")
    print("------")

    # Parse the fixed point specification
    observations_spec = parse_observations_csv(csv_path)

    print("Specified fixed-point observations:")
    for obs_id, values in observations_spec.items():
        print(f"{obs_id}: {values}")
    print("------")

    # Precompute indexable entries (indices to 2d observation matrix)
    indices = [
        (fp_id, var)
        for fp_id, vars_dict in observations_spec.items()
        for var in vars_dict.keys()
    ]

    # Compute colored fixed points symbolically
    fixed_points = FixedPoints.symbolic(stg)
    print(f"Total colored fixed points: {fixed_points.cardinality()}")
    print(f"Total fixed point states: {fixed_points.vertices().cardinality()}")
    print(f"Total fixed point colors: {fixed_points.colors().cardinality()}")
    print("------")

    # Try progressively removing constraints (making N of the fixed-point
    # values non-determined instead)
    # We stop this "constraint loosening" once closest specification is found
    found_solution = False
    for num_to_remove in range(len(indices) + 1):
        if found_solution:
            break

        print(f"\nTrying with {num_to_remove} values removed:")
        for ignore_set in combinations(indices, num_to_remove):
            current_spec = loosen_specification(observations_spec, ignore_set)

            # Start with all colors, refine with fixed-point constraints
            satisfying_colors = fixed_points.colors()
            for fp_subspec in current_spec.values():
                spec_vertices = stg.mk_subspace(fp_subspec).vertices()
                matched_colors = fixed_points.intersect_vertices(spec_vertices).colors()
                satisfying_colors = satisfying_colors.intersect(matched_colors)
                if satisfying_colors.is_empty():
                    break

            # If some colors satisfy this specification, inform the user
            if not satisfying_colors.is_empty():
                found_solution = True
                print("\tFound matching specification!")
                print("\t-> Removed values:", ignore_set)
                print("\t-> Matching specification:", current_spec)
                print(f"\t-> {satisfying_colors.cardinality()} colors satisfy this specification")

                # Only enumerate colors if selected by the user (can be untractable in general)
                if print_colors:
                    print("\t-> Matching colors:")
                    for c in satisfying_colors:
                        print(f"\t---> {c}")
                print()

    if not found_solution:
        print("No matching specification found")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python naive_fps_inference.py <psbn_file> <specification_csv> [--print-colors]")
        sys.exit(1)

    psbn_path = sys.argv[1]
    csv_path = sys.argv[2]
    print_colors = "--print-colors" in sys.argv

    main(psbn_path, csv_path, print_colors)
