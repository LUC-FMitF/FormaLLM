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
        print(f"\n--- Evaluating  {model_name} ---")

        # Write the LLM Generated Spec to disk
        tla_path = generated_dir / f"{model_name}.generated.tla"
        tla_path.write_text(spec.strip())

        result = subprocess.run(
            ["tlc", "-nowarning", "-config", str(tla_path)],
            capture_output=True, text=True
        )

        log_path = eval_output_dir / f"{model_name}.tlc.log"
        log_path.write_text(result.stdout + "\n=== STDERR ===\n" + result.stderr)

        if "The specification is correct" in result.stdout:
            results[model_name] = "PASS"
        elif "TLC threw an error" in result.stdout:
            results[model_name] = "ERROR"
        else:
            results[model_name] = "FAIL"

    return results