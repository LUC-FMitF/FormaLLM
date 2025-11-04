# FormaLLM Development Guide

Guide for developers contributing to FormaLLM.

## Development Environment Setup

### Clone and Install

```bash
git clone https://github.com/LUC-FMitF/FormaLLM.git
cd FormaLLM

# Create virtual environment
python -m venv venv
source venv/bin/activate

# Install in development mode
pip install -r requirements.txt
pip install -e .  # If setup.py exists
```

### IDE Setup

**VS Code**:
```bash
# Install recommended extensions
code --install-extension ms-python.python
code --install-extension ms-python.vscode-pylance
code --install-extension eamodio.gitlens
```

**Configuration** (`.vscode/settings.json`):
```json
{
  "python.defaultInterpreterPath": "${workspaceFolder}/venv/bin/python",
  "python.linting.enabled": true,
  "python.linting.pylintEnabled": true,
  "python.formatting.provider": "black",
  "[python]": {
    "editor.formatOnSave": true,
    "editor.defaultFormatter": "ms-python.python"
  }
}
```

## Code Structure

### Pipeline Steps (`steps/`)

Each step is a ZenML `@step` decorated function:

```python
from zenml import step
import os

@step(enable_cache=False)
def my_step(input_data: dict) -> dict:
    """
    Description of what this step does.
    
    Args:
        input_data: Dict mapping model_name -> content
        
    Returns:
        Dict mapping model_name -> result
    """
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    
    results = {}
    for model_name, content in input_data.items():
        # Process content
        results[model_name] = processed_result
    
    return results
```

**Key Patterns**:
- Cache disabled: `enable_cache=False` (external tool dependencies)
- Input/Output: Must be serializable (dict, str, int, etc.)
- Environment: Read backend/model from `os.getenv()`
- MLflow: Log with `mlflow.log_*()` functions
- Error handling: Catch and log, don't crash pipeline

### Adding a New Step

1. Create `steps/new_step.py`:

```python
from zenml import step
import mlflow

@step(enable_cache=False)
def new_step(input_data: dict) -> dict:
    """Description."""
    results = {}
    
    with mlflow.start_run(nested=True) as run:
        for model_name, content in input_data.items():
            # Implement logic
            results[model_name] = result
            
            mlflow.log_metric(f"{model_name}_metric", value)
    
    return results
```

2. Register in `pipelines/tla_pipeline.py`:

```python
from steps.new_step import new_step

@pipeline
def tla_pipeline():
    # ... existing steps ...
    new_results = new_step(previous_output)
    # ... remaining steps ...
```

3. Test:

```bash
python run_pipeline.py
```

## Modifying Existing Steps

### Changing Prompt Template

File: `steps/prompt_step.py`

```python
# Add custom prompt
SYSTEM_PROMPT = """You are an expert in formal specification languages..."""

# Modify few-shot examples
def load_training_examples(count=3):
    # Load from outputs/train.json
    # Return as list of (comment, tla, cfg) tuples
    pass
```

### Changing Validation Logic

File: `steps/parse_step.py` (SANY) and `steps/evaluate_generated_step.py` (TLC)

```python
# Modify SANY pattern matching
def extract_errors(log_content: str) -> List[str]:
    # Parse SANY output
    # Return list of error messages
    pass

# Modify TLC parsing
def extract_metrics(log_content: str) -> TLCMetrics:
    # Extract state space info
    # Extract performance data
    # Return structured metrics
    pass
```

### Changing Metrics Collection

File: `steps/sany_metrics.py` or `steps/tlc_metrics.py`

Add new fields to dataclass:

```python
@dataclass
class SANYMetrics:
    # ... existing fields ...
    new_field: str  # Add new field
```

Update extraction logic:

```python
def extract_metrics(model_name: str, log_path: Path) -> SANYMetrics:
    # ... existing extraction ...
    new_field = extract_new_info(log_content)
    
    return SANYMetrics(
        # ... existing fields ...
        new_field=new_field
    )
```

Update CSV export:

```python
@staticmethod
def export_csv_header() -> List[str]:
    return [
        # ... existing fields ...
        'new_field'
    ]

@staticmethod
def to_csv_row(metrics: SANYMetrics) -> Dict:
    return {
        # ... existing fields ...
        'new_field': metrics.new_field
    }
```

## Data Collection Scripts

Scripts in `scripts/` perform analysis on collected data.

### Understanding Data Files

**Main metrics**:
- `outputs/spec_differences_metrics.csv`: Difference metrics between generated and ground truth
- `outputs/combined_tlc_metrics.csv`: TLC validation results
- `outputs/combined_sany_metrics.csv`: SANY parsing results

### Creating New Analysis Script

File: `scripts/analyze_topic.py`

```python
import pandas as pd
import numpy as np
from pathlib import Path

def load_data() -> pd.DataFrame:
    """Load and merge all relevant data."""
    diff_df = pd.read_csv("outputs/spec_differences_metrics.csv")
    tlc_df = pd.read_csv("outputs/combined_tlc_metrics.csv")
    
    # Merge on model_name and backend_model
    merged = diff_df.merge(tlc_df, on=['model_name', 'backend_model'])
    return merged

def analyze_topic(df: pd.DataFrame):
    """Perform analysis."""
    # Your analysis here
    print(df.describe())
    
    # Save results
    df.to_csv("outputs/analysis_results.csv", index=False)

if __name__ == "__main__":
    df = load_data()
    analyze_topic(df)
```

Run:

```bash
python scripts/analyze_topic.py
```

## Testing

### Unit Tests

Create `tests/test_module.py`:

```python
import unittest
from steps.parse_step import SANYParser

class TestSANYParser(unittest.TestCase):
    def test_extract_error(self):
        log = """..error message.."""
        parser = SANYParser()
        errors = parser.extract_errors(log)
        self.assertEqual(len(errors), 1)

if __name__ == '__main__':
    unittest.main()
```

Run tests:

```bash
python -m pytest tests/
```

### Manual Testing

Test LLM backend:

```bash
python test_llm.py
```

Test single specification:

```bash
python -c "
from steps.prompt_step import prompt_step
results = prompt_step({'spec_name': 'content'})
print(results)
"
```

## Code Style

### Python Style Guide

Follow [PEP 8](https://pep8.org/):

```bash
# Format code
pip install black
black scripts/ steps/

# Check style
pip install pylint
pylint scripts/ steps/
```

### Docstrings

Use Google-style docstrings:

```python
def function_name(param1: str, param2: int) -> bool:
    """
    Brief description.
    
    Longer description if needed. Explain parameters,
    return values, and any exceptions.
    
    Args:
        param1: Description of param1
        param2: Description of param2
        
    Returns:
        Description of return value
        
    Raises:
        ValueError: If param2 is negative
        
    Example:
        >>> result = function_name("test", 42)
        >>> print(result)
        True
    """
    if param2 < 0:
        raise ValueError("param2 must be non-negative")
    
    return True
```

### Type Hints

Always use type hints:

```python
from typing import Dict, List, Optional, Tuple

def process_data(
    records: List[Dict[str, str]],
    threshold: float = 0.5
) -> Tuple[int, Optional[str]]:
    """Process records and return count and status."""
    return len(records), "complete"
```

## Debugging

### Enable Verbose Logging

```python
import logging

logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)

logger.debug("Debug message")
logger.info("Info message")
logger.warning("Warning message")
logger.error("Error message")
```

### Debug Single Model

```python
from steps.prompt_step import prompt_step
from pathlib import Path

model_name = "DieHard"
comment_file = Path(f"data/{model_name}/txt/{model_name}_comments_clean.txt")
comment = comment_file.read_text()

result = prompt_step({model_name: comment})
print(result[model_name])
```

### MLflow Debugging

```bash
# View all runs
mlflow ui --backend-store-uri file://$(pwd)/outputs/mlruns

# Check specific run
mlflow runs list --experiment-name tla_prompt_generation
mlflow runs describe -r <run-id>
```

## Common Tasks

### Update Few-Shot Examples

Edit `outputs/train.json`:

```json
[
  {
    "model": "spec_name",
    "comment": "Natural language description",
    "tla": "EXTENDS ... specification",
    "cfg": "Configuration..."
  }
]
```

### Add New Specification to Dataset

1. Create `data/{spec_name}/txt/` and add comment file
2. Create `data/{spec_name}/tla/` and add ground truth
3. Create `data/{spec_name}/cfg/` and add config
4. Update `data/all_models.json` with metadata

### Regenerate Analysis

```bash
# Clear old results
rm -rf outputs/spec_differences_metrics.csv

# Collect differences
python scripts/collect_spec_differences.py

# Run statistical analysis
python scripts/correlate_differences_with_validation.py

# Generate visualizations
python scripts/graph_results.py
```

## Performance Optimization

### Caching

Currently disabled to ensure fresh external tool outputs:

```python
@step(enable_cache=False)
def step_name(input_data: dict) -> dict:
    # ... implementation ...
```

To enable caching for pure Python steps:

```python
@step(enable_cache=True)
def pure_python_step(input_data: dict) -> dict:
    # ... no external tool calls ...
```

### Parallel Processing

Use `concurrent.futures` for batch processing:

```python
from concurrent.futures import ThreadPoolExecutor

def process_batch(models: List[str]) -> Dict[str, str]:
    results = {}
    
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {
            executor.submit(process_one, model): model 
            for model in models
        }
        
        for future in futures:
            model = futures[future]
            results[model] = future.result()
    
    return results
```

## Contributing

1. **Fork** the repository
2. **Create** a feature branch: `git checkout -b feature/my-feature`
3. **Make changes** and follow code style
4. **Test** thoroughly: `python test_llm.py && pytest`
5. **Commit** with clear messages: `git commit -m "Add feature description"`
6. **Push** to branch: `git push origin feature/my-feature`
7. **Create** Pull Request with description

## Troubleshooting

### Issue: "Module not found"

```bash
# Reinstall dependencies
pip install -r requirements.txt
```

### Issue: "MLflow tracking fails"

```bash
# Check MLflow URI
echo $MLFLOW_TRACKING_URI

# Set if missing
export MLFLOW_TRACKING_URI="file://$(pwd)/outputs/mlruns"
```

### Issue: "TLA+ tools not found"

```bash
# Verify path
ls /opt/tla/tla2tools.jar

# Or set custom path
export TLA_TOOLS_DIR="/your/path"
```

## Resources

- [ZenML Documentation](https://docs.zenml.io/)
- [LangChain Documentation](https://python.langchain.com/)
- [MLflow Documentation](https://mlflow.org/docs/)
- [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
- [PEP 8 Style Guide](https://pep8.org/)

## Questions?

- Check existing issues: https://github.com/LUC-FMitF/FormaLLM/issues
- Review pull requests: https://github.com/LUC-FMitF/FormaLLM/pulls
- Contact maintainers for guidance
