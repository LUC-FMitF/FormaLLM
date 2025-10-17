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
import mlflow

@step(enable_cache=False)
def evaluate_tla(specs: dict) -> dict:
    import os
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    
    # Get model info from environment
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    model_output_dir = project_root / "outputs" / f"{backend}_{model}"
    
    generated_dir = model_output_dir / "generated"
    eval_output_dir = model_output_dir / "evaluations"
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
    
    # Setup model-specific MLflow tracking
    mlflow_dir = model_output_dir / "mlruns"
    mlflow.set_tracking_uri(f"file://{mlflow_dir}")
    mlflow.set_experiment(f"tla_eval_{backend}_{model}")

    for model_name, spec in specs.items():
        print(f"\n--- {model_name} ---")

        tla_path = generated_dir / f"{model_name}.tla"

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

        log_text = result.stdout + "\n=== STDERR ===\n" + result.stderr
        log_path = eval_output_dir / f"{model_name}.tlc.log"
        log_path.write_text(log_text)

        # Print some of the TLC output in ZenML logs
        print(result.stdout[:500])

        with mlflow.start_run(run_name=model_name, nested=True):
            mlflow.log_param("model_name", model_name)
            mlflow.log_param("return_code", result.returncode)
            mlflow.log_artifact(str(log_path))

            mlflow.log_text(log_text, f"{model_name}_tlc_output.txt")

            if "The specification is correct" in result.stdout:
                result_status = "PASS"
                mlflow.log_metric("tlc_result", 1)
            elif "TLC threw an error" in result.stdout or "TLC encountered an unexpected exception" in result.stdout:
                result_status = "ERROR"
                mlflow.log_metric("tlc_result", -1)
            else:
                result_status = "FAIL"
                mlflow.log_metric("tlc_result", 0)

            mlflow.log_param("result_status", result_status)
            results[model_name] = result_status

        
        results_path = eval_output_dir / "evaluation_results.csv"
        with results_path.open("w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(["Model", "Result"])
            for model, outcome in results.items():
                writer.writerow([model, outcome])

    return results