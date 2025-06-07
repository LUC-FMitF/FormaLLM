#!/usr/bin/env python3
"""
@file data_split_step.py
Splits the dataset defined in all_models.json into training, validation, and test sets.

This script reads the all_models.json file, shuffles the dataset, and writes three new JSON files
(train.json, val.json, test.json) to the outputs/ directory. It is designed to be robust to the script's
location in the filesystem hierarchy and should be placed in the steps/ directory.

Usage:
    python data_split_step.py
"""

import json
import random
from pathlib import Path

# Resolve project root from script location
project_root = Path(__file__).resolve().parent.parent
data_dir = project_root / "data"
output_dir = project_root / "outputs"

# Ensure output directory exists
output_dir.mkdir(parents=True, exist_ok=True)

# Parameters
input_json_path = data_dir / "all_models.json"
train_ratio = 0.7
val_ratio = 0.15
test_ratio = 0.15

# Load data
with open(input_json_path, "r") as f:
    all_data = json.load(f)["data"]

# Shuffle and split
random.shuffle(all_data)
n_total = len(all_data)
n_train = int(n_total * train_ratio)
n_val = int(n_total * val_ratio)

train_data = all_data[:n_train]
val_data = all_data[n_train:n_train + n_val]
test_data = all_data[n_train + n_val:]

# Save splits
splits = {
    "train.json": train_data,
    "val.json": val_data,
    "test.json": test_data,
}

for filename, data in splits.items():
    with open(output_dir / filename, "w") as f:
        json.dump({"data": data}, f, indent=2)

print(f"Dataset split into {len(train_data)} train, {len(val_data)} val, {len(test_data)} test samples.")
