#!/usr/bin/env python3
"""
Evaluate Generated TLA+ Specs with Comprehensive TLC and SANY Metrics
---------------------------------------------------------------------
Evaluates each .tla spec using TLC model checker and extracts comprehensive metrics:

SANY Metrics (Syntax Analysis):
  - Parse success/failure status
  - Error categorization and location analysis  
  - First error type and message extraction

TLC Metrics (Model Checking Analysis):
  - Execution status (PASS/FAIL/ERROR/SEMANTIC_ERROR/TIMEOUT)
  - Semantic error analysis and categorization
  - State space exploration metrics (states, depth, outdegree)
  - Performance metrics (execution time, memory usage)
  - Temporal properties detection
  - TLC configuration analysis

Outputs:
  - MLflow logging with comprehensive metrics
  - CSV exports: sany_metrics.csv, tlc_metrics.csv, evaluation_results.csv
  - Individual TLC log files for each model

Author: Brian Ortiz  
License: MIT
"""

import subprocess
import warnings
import shutil
from pathlib import Path
from typing import Optional
from zenml import step
import csv
import mlflow
import os
from steps.sany_metrics import SANYMetricsCollector
from steps.tlc_metrics import TLCMetricsCollector

@step(enable_cache=False)
def evaluate_tla(parsed: dict) -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    
    # Get model info from environment
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    model_output_dir = project_root / "outputs" / f"{backend}_{model}"
    
    generated_dir = model_output_dir / "generated"
    eval_output_dir = model_output_dir / "evaluations"
    sany_logs_dir = model_output_dir / "sany_logs"
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
    sany_metrics_list = []
    tlc_metrics_list = []
    tlc_results_list = []
    
    # Setup model-specific MLflow tracking
    mlflow_dir = model_output_dir / "mlruns"
    mlflow.set_tracking_uri(f"file://{mlflow_dir}")
    mlflow.set_experiment(f"tla_eval_{backend}_{model}")

    for model_name, parse_status in parsed.items():
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
        
        # Clean up TLC state directory to prevent timestamp conflicts on re-runs
        states_dir = generated_dir / "states"
        if states_dir.exists():

            shutil.rmtree(states_dir, ignore_errors=True)
        
        result = subprocess.run(
            ["tlc", "-workers", "auto", "-nowarning", "-config", str(cfg_path), str(tla_path)],
            capture_output=True, text=True
        )

        log_text = result.stdout + "\n=== STDERR ===\n" + result.stderr
        log_path = eval_output_dir / f"{model_name}.tlc.log"
        log_path.write_text(log_text)

        # Extract SANY metrics (from sany_logs created by parse_step.py)
        sany_log_path = sany_logs_dir / f"{model_name}.sany.log"
        sany_metrics = SANYMetricsCollector.extract_metrics(model_name, sany_log_path)

        # Extract comprehensive TLC metrics
        tlc_metrics = TLCMetricsCollector.extract_metrics(model_name, log_path, result.returncode)

        # Print comprehensive metrics in ZenML logs
        print(result.stdout[:500])
        print(f"[SANY] Parse status: {sany_metrics.parse_status}, First error line: {sany_metrics.first_error_line}")
        print(f"[TLC] Status: {tlc_metrics.execution_status}, Semantic errors: {tlc_metrics.semantic_error_count}, States: {tlc_metrics.distinct_states}")

        with mlflow.start_run(run_name=model_name, nested=True):
            mlflow.log_param("model_name", model_name)
            mlflow.log_artifact(str(log_path))
            mlflow.log_text(log_text, f"{model_name}_tlc_output.txt")

            # Log SANY metrics (factual data)
            SANYMetricsCollector.log_to_mlflow(sany_metrics)
            if sany_log_path.exists():
                mlflow.log_artifact(str(sany_log_path))

            # Log comprehensive TLC metrics
            TLCMetricsCollector.log_to_mlflow(tlc_metrics)

            # Use TLC metrics execution status for result
            result_status = tlc_metrics.execution_status
            results[model_name] = result_status

            # Legacy MLflow metrics for compatibility
            if result_status == "PASS":
                mlflow.log_metric("tlc_result", 1)
            elif result_status in ["ERROR", "TIMEOUT"]:
                mlflow.log_metric("tlc_result", -1)
            else:
                mlflow.log_metric("tlc_result", 0)
            
            mlflow.log_param("result_status", result_status)
            mlflow.log_param("return_code", result.returncode)

            # Collect for CSV export
            sany_metrics_list.append(SANYMetricsCollector.to_csv_row(sany_metrics))
            tlc_metrics_list.append(TLCMetricsCollector.to_csv_row(tlc_metrics))
            tlc_results_list.append({"Model": model_name, "Result": result_status})

    
    # Export SANY metrics to CSV (after all models processed)
    if sany_metrics_list:
        sany_metrics_path = eval_output_dir / "sany_metrics.csv"
        with sany_metrics_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=SANYMetricsCollector.export_csv_header())
            writer.writeheader()
            writer.writerows(sany_metrics_list)

    # Export comprehensive TLC metrics to CSV
    if tlc_metrics_list:
        tlc_metrics_path = eval_output_dir / "tlc_metrics.csv"
        with tlc_metrics_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=TLCMetricsCollector.export_csv_header())
            writer.writeheader()
            writer.writerows(tlc_metrics_list)

    # Export TLC results to CSV (legacy format for compatibility)
    if tlc_results_list:
        results_path = eval_output_dir / "evaluation_results.csv"
        with results_path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=["Model", "Result"])
            writer.writeheader()
            writer.writerows(tlc_results_list)

    return results