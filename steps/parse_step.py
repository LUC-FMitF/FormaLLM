import subprocess
import logging
from pathlib import Path
from typing import Dict
from zenml import step
import os

@step
def sanity_check_sany(specs: Dict[str, str]) -> Dict[str, str]:
    """
    Runs the SANY parser on each generated TLA+ file to validate syntax.
    """
    project_root = Path(__file__).resolve().parent.parent
    generated_dir = project_root / "outputs" / "generated"
    tools_jar_path = os.environ.get("TLA_TOOLS_DIR", "/opt/tla") + "/tla2tools.jar"

    results = {}

    for model_name in specs.keys():
        tla_path = generated_dir / f"{model_name}.generated.tla"

        if not tla_path.exists():
            results[model_name] = "MISSING"
            continue

        try:
            result = subprocess.run(
                [
                    "java",
                    "-cp",
                    tools_jar_path,
                    "tla2sany.SANY",
                    str(tla_path),
                ],
                capture_output=True,
                text=True,
                timeout=30,
            )

            output = result.stdout + "\n" + result.stderr
            if result.returncode == 0 and "Parsing completed" in output:
                results[model_name] = "PASS"
            else:
                logging.warning(f"[{model_name}] SANY output:\n{output}")
                results[model_name] = "FAIL"
        except Exception as e:
            logging.error(f"[{model_name}] SANY error: {e}")
            results[model_name] = "ERROR"

    return results
