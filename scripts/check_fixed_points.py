"""Exploration of model fixed points

This script explores all fixed-point combinations across all interpretations
of a PSBN model. It prints a short fixed-point summary, then enumerates all
interpretations and their fixed point combinations, and then a list of unique
fixed point combinations.

It is not usable for large PSBNs since it enumerates the model interpretations
for output.

Usage: python check_fixed_points.py <boolean_network_file>
"""

import sys
from biodivine_aeon import (AsynchronousGraph, BooleanNetwork,
    ColoredVertexSet, FixedPoints)


def collect_fp_combinations(fixed_points: ColoredVertexSet, print_all: bool):
    """Iterate over all colors and collect unique fixed-point combinations.
    This is a very naive way to do this, but good enough to explore toy models.

    If flag `print_all` is set, print fixed-points for all interpretations.
    """
    fixed_point_colors  = fixed_points.colors()
    unique_combinations = set()
    if print_all:
        print("Fixed point combinations per model color:")

    count = 1
    while not fixed_point_colors.is_empty():
        # Pick one color and restrict to its fixed points
        color_singleton = fixed_point_colors.pick_singleton()
        fps_single_color = fixed_points.intersect_colors(color_singleton)

        # Extract vertex values as binary strings
        fps_values = [tuple(v.values()) for v in fps_single_color.vertices()]
        binary_vectors = [''.join('1' if x else '0' for x in fp) for fp in fps_values]
        # Sets cant deal with lists, so we just make it a tuple
        unique_combinations.add(tuple(binary_vectors))

        if print_all:
            print(count, binary_vectors)
            print("\t->", next(iter(color_singleton)))  # print the only color in the set

        fixed_point_colors = fixed_point_colors.minus(color_singleton)
        count += 1

    if print_all:
        print("------")
    return unique_combinations


def main(path: str):
    # Load and prepare PSBN and its colored STG
    bn = BooleanNetwork.from_file(path)
    bn = bn.infer_valid_graph()
    stg = AsynchronousGraph(bn)

    print(f"Total colors: {stg.mk_unit_colors().cardinality()}")
    print("------")

    # Compute fixed-points across all interpretations (colors)
    fixed_points = FixedPoints.symbolic(stg)

    print(f"Total colored fixed points: {fixed_points.cardinality()}")
    print(f"Total fixed point states: {fixed_points.vertices().cardinality()}")
    print(f"Total fixed point colors: {fixed_points.colors().cardinality()}")
    print("------")

    print("Raw fixed point vertices projection (across all colors):")
    for fp in fixed_points.vertices():
        print(fp)
    print("------")

    # Iterate over all interpretations and collect the unique combinations
    # Print all colors and their fixed-points while iterating
    unique_combinations = collect_fp_combinations(fixed_points, print_all=True)

    print("Unique fixed point combinations:")
    for fp_combination in unique_combinations:
        print(list(fp_combination))


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python check_fixed_points.py <boolean_network_file>")
        sys.exit(1)
    main(sys.argv[1])
