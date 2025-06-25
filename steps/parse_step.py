import subprocess
import logging
from pathlib import Path
from typing import Dict
from zenml import step
import os
import mlflow

# Ensure your MLflow version supports tracing (>=2.14.3)
from packaging.version import Version
assert Version(mlflow.__version__) >= Version("2.14.3"), (
    "MLflow tracing requires version 2.14.3 or newer. "
    "Upgrade with: pip install -U mlflow"
)

# Decorated helper to run SANY and return structured output
@mlflow.trace(name="run_sany_check", attributes={"tool": "SANY", "type": "tla_parser"})
def run_sany(model_name: str, tla_path: str, tools_jar_path: str) -> Dict[str, str]:
    result = subprocess.run(
        [
            "java",
            "-cp",
            tools_jar_path,
            "tla2sany.SANY",
            tla_path,
        ],
        capture_output=True,
        text=True,
        timeout=30,
    )
    return {
        "returncode": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr
    }

@step
def sanity_check_sany(specs: Dict[str, str]) -> Dict[str, str]:
    """
    Runs the SANY parser on each generated TLA+ file to validate syntax.
    Logs output and results to MLflow with tracing.
    """
    project_root = Path(__file__).resolve().parent.parent
    generated_dir = project_root / "outputs" / "generated"
    tools_jar_path = os.environ.get("TLA_TOOLS_DIR", "/opt/tla") + "/tla2tools.jar"
    sany_logs_dir = project_root / "outputs" / "sany_logs"
    sany_logs_dir.mkdir(parents=True, exist_ok=True)

    results = {}
    mlflow.set_experiment("tla_sanity_check")

    for model_name in specs.keys():
        tla_path = generated_dir / f"{model_name}.generated.tla"

        if not tla_path.exists():
            results[model_name] = "MISSING"
            continue

        with mlflow.start_run(run_name=f"sany_{model_name}", nested=True):
            try:
                parsed = run_sany(model_name, str(tla_path), tools_jar_path)
                output = parsed["stdout"] + "\n" + parsed["stderr"]

                log_file = sany_logs_dir / f"{model_name}.sany.log"
                log_file.write_text(output)
                mlflow.log_artifact(str(log_file))

                if parsed["returncode"] == 0 and "Parsing completed" in output:
                    mlflow.log_metric("sany_result", 1)
                    results[model_name] = "PASS"
                else:
                    mlflow.log_metric("sany_result", 0)
                    logging.warning(f"[{model_name}] SANY output:\n{output}")
                    results[model_name] = "FAIL"

            except Exception as e:
                error_msg = str(e)
                log_file = sany_logs_dir / f"{model_name}.sany.error.log"
                log_file.write_text(error_msg)
                mlflow.log_artifact(str(log_file))
                mlflow.log_metric("sany_result", -1)
                logging.error(f"[{model_name}] SANY error: {e}")
                results[model_name] = "ERROR"

    return results

