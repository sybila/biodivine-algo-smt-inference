import csv
import argparse
import os

def convert_csv_to_annotations(csv_path, weight=None):
    if not os.path.exists(csv_path):
        print(f"Error: File '{csv_path}' not found.")
        return

    with open(csv_path, mode='r', encoding='utf-8') as f:
        # Using DictReader to handle headers automatically
        reader = csv.DictReader(f)
        
        # Clean up column names (remove leading/trailing whitespace)
        reader.fieldnames = [name.strip() for name in reader.fieldnames]
        
        state_col = reader.fieldnames[0]
        var_cols = reader.fieldnames[1:]
        rows = list(reader)

        # 1. Output State Declarations
        unique_states = []
        for row in rows:
            state = str(row[state_col]).strip()
            if state not in unique_states:
                unique_states.append(state)
                print(f"#!state:declare:{state}")

        # 2. Output Variable Comparisons
        for row in rows:
            state = str(row[state_col]).strip()
            for var in var_cols:
                value = str(row[var]).strip()
                
                # Base format
                base_str = f"#! comparison : equal : {state}/{var}: {value} :"
                
                # Append weight if provided, otherwise leave trailing colon
                if weight is not None:
                    print(f"{base_str} weight: {weight}")
                else:
                    print(base_str)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert CSV specification to model annotations.")
    parser.add_argument("path", help="Path to the specification CSV file")
    parser.add_argument("--weight", type=float, help="Optional weight value for the annotations")

    args = parser.parse_args()

    convert_csv_to_annotations(args.path, args.weight)
