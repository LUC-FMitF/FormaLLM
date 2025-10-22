"""
Pytest configuration and shared fixtures for FormaLLM tests.
"""
import os
import sys
import pytest
from pathlib import Path
from typing import Dict
from dotenv import load_dotenv

# Add project root to Python path
PROJECT_ROOT = Path(__file__).parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

# Load test environment
env_path = PROJECT_ROOT / ".env"
if env_path.exists():
    load_dotenv(env_path)


@pytest.fixture
def project_root() -> Path:
    """Return the project root directory."""
    return PROJECT_ROOT


@pytest.fixture
def data_dir(project_root) -> Path:
    """Return the data directory."""
    return project_root / "data"


@pytest.fixture
def outputs_dir(project_root) -> Path:
    """Return the outputs directory."""
    return project_root / "outputs"


@pytest.fixture
def test_data_dir() -> Path:
    """Return the test fixtures directory."""
    return Path(__file__).parent / "fixtures"


@pytest.fixture
def sample_model_metadata() -> Dict:
    """Return sample model metadata for testing."""
    return {
        "id": "test_001",
        "model": "test_model",
        "tla_original": "test_model.tla",
        "tla_clean": "test_model_clean.tla",
        "comments": "test_model_comments.txt",
        "comments_clean": "test_model_comments_clean.txt",
        "cfg": "test_model.cfg"
    }


@pytest.fixture
def sample_tla_spec() -> str:
    """Return a simple valid TLA+ specification for testing."""
    return """
---- MODULE TestModule ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x
============================
"""


@pytest.fixture
def sample_comments() -> str:
    """Return sample comments for TLA+ generation."""
    return """
This is a simple counter specification.
We have a variable x that starts at 0.
On each step, x increments by 1.
"""


@pytest.fixture
def sample_cfg_file() -> str:
    """Return a sample TLC configuration file."""
    return """
INIT Init
NEXT Next
SPECIFICATION Spec
INVARIANT TypeOK
"""


@pytest.fixture
def mock_env_vars(monkeypatch):
    """Set up mock environment variables for testing."""
    monkeypatch.setenv("LLM_BACKEND", "openai")
    monkeypatch.setenv("LLM_MODEL", "gpt-4")
    monkeypatch.setenv("TLA_TOOLS_DIR", "/opt/tla")
    monkeypatch.setenv("MLFLOW_TRACKING_URI", "file:///tmp/test_mlruns")
    monkeypatch.setenv("NUM_FEW_SHOTS", "3")


@pytest.fixture
def tla_tools_jar(tmp_path) -> Path:
    """Create a mock TLA+ tools jar path."""
    tools_dir = tmp_path / "tla_tools"
    tools_dir.mkdir()
    jar_path = tools_dir / "tla2tools.jar"
    jar_path.touch()
    return jar_path


@pytest.fixture(autouse=True)
def reset_mlflow():
    """Reset MLflow state between tests."""
    import mlflow
    mlflow.end_run()
    yield
    mlflow.end_run()
