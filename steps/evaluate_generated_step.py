#!/usr/bin/env python3
"""
Evaluate Generated TLA+ Specs with TLC
--------------------------------------
Evaluates each .generated.tla spec using TLC. Resolves .cfg files using
project heuristics and logs results under outputs/evaluations/.

Author: Brian Ortiz
License: MIT
"""

import subprocess
import warnings
from pathlib import Path
from typing import Optional
from zenml import step
import csv

@step
def evaluate_tla(specs: dict) -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    generated_dir = project_root / "outputs" / "generated"
    eval_output_dir = project_root / "outputs" / "evaluations"
    eval_output_dir.mkdir(parents=True, exist_ok=True)

    def resolve_file(model_name: str, filename: str, subdir: str) -> Optional[Path]:
        model_dir = data_dir / model_name
        expected = model_dir / subdir / filename
        if expected.exists():
            return expected
        for search_dir in [model_dir, data_dir]:
            fallback = list(search_dir.rglob(filename))
            if fallback:
                warnings.warn(f"[{model_name}] Using fallback {Path(filename).suffix.upper()} file: {fallback[0]}")
                return fallback[0]
        warnings.warn(f"[{model_name}] Missing required file: {filename}")
        return None

    results = {}

    for model_name, spec in specs.items():
        print(f"\n--- {model_name} ---")

        # Write Spec to disk
        tla_path = generated_dir / f"{model_name}.generated.tla"
        tla_path.write_text(spec.strip())

        cfg_path = generated_dir / f"{model_name}.cfg"
        if not cfg_path.exists():
            # Fallback: check for original .cfg in dataset
            cfg_path = resolve_file(model_name, f"{model_name}.cfg", "cfg")

        if not cfg_path or not cfg_path.exists():
            print(f"Skipping {model_name} due to missing .cfg file.")
            results[model_name] = "SKIPPED"
            continue
        
        result = subprocess.run(
            ["tlc", "-nowarning", "-config", str(cfg_path), str(tla_path)],
            capture_output=True, text=True
        )

        log_path = eval_output_dir / f"{model_name}.tlc.log"
        log_path.write_text(result.stdout + "\n=== STDERR ===\n" + result.stderr)

        if "The specification is correct" in result.stdout:
            results[model_name] = "PASS"
        elif "TLC encountered an unexpected exception" in result.stdout:
            results[model_name] = "ERROR"
        else:
            results[model_name] = "FAIL"

        
        results_path = eval_output_dir / "evaluation_results.csv"
        with results_path.open("w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["Model", "Result"])
            for model, outcome in results.items():
                writer.writerow([model, outcome])

    return results