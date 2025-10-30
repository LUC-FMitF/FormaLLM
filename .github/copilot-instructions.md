# FormaLLM AI Assistant Instructions

## Project Overview
FormaLLM is a research pipeline that uses Large Language Models (LLMs) to automatically generate formal TLA+ specifications from natural language comments. It validates generated specifications using SANY parser (syntax) and TLC model checker (runtime behavior). Supports multiple LLM backends: OpenAI GPT-4, Anthropic Claude, and local Ollama models.

## Core Architecture

### Data Flow: Input → LLM → Validation → Evaluation
```
data/<model_name>/{txt/, tla/, cfg/}
         ↓ (comments)
    prompt_step.py (LangChain + LLM)
         ↓ (generated .tla/.cfg)
    parse_step.py (SANY syntax check)
         ↓ (parse results)
    evaluate_generated_step.py (TLC runtime check)
         ↓ (TLC output)
    graph_results.py (CSV + visualization)
         ↓
outputs/<backend>_<model>/{generated/, evaluations/, mlruns/}
```

### Pipeline Orchestration
- **Entry**: `run_pipeline.py` sets environment variables → calls `pipelines/tla_pipeline.py`
- **ZenML Execution**: `tla_pipeline()` chains all steps with automatic caching and MLflow logging
- **Multi-Backend Support**: Environment variables `LLM_BACKEND` and `LLM_MODEL` select backend (openai/anthropic/ollama)

## Data Organization & File Resolution

### Directory Structure
- **Input Data**: `data/<model_name>/` contains 3 subdirectories:
  - `txt/`: Natural language comments (`<model>_comments_clean.txt`)
  - `tla/`: Ground-truth specifications (`<model>.tla`)
  - `cfg/`: TLC configuration files (`<model>.cfg`) - sometimes absent
- **Metadata**: `data/all_models.json` maps 1800+ models with fields: `comments_clean`, `tla_clean`, `cfg`
- **Outputs**: `outputs/<backend>_<model>/` contains per-model results in subdirectories: `generated/`, `evaluations/`, `mlruns/`, `sany_logs/`

### File Resolution with Fallback Search
Steps use robust file lookup (`prompt_step.py` lines 60-70):
```python
# 1. Try expected path: data/<model>/<subdir>/<filename>
# 2. Fallback to rglob search within data/ directory
# 3. Warn if file not found; return empty string
```
**Important**: Always check file existence before reading; use `Path.rglob()` as last resort (can be slow on large projects).

## LLM Integration & Prompting

### Few-Shot Learning Pipeline
- `prompt_step.py` loads few-shot examples from `outputs/train.json` (default: 3 examples, configurable via `NUM_FEW_SHOTS` env var)
- Constructs `ChatPromptTemplate` with: System prompt → Examples → New comment → "Generate TLA+ spec"
- Supports 3 backends via LangChain:
  - **OpenAI**: `ChatOpenAI` with `OPENAI_API_KEY`
  - **Anthropic**: `ChatAnthropic` with `ANTHROPIC_API_KEY`
  - **Ollama**: `ChatOllama` with `OLLAMA_BASE_URL` (default: `http://localhost:11434`)

### MLflow Tracing & Logging
- `@mlflow.trace()` decorator wraps subprocess calls (e.g., SANY, TLC) to capture tool outputs
- Each pipeline step sets model-specific MLflow tracking URI: `outputs/<backend>_<model>/mlruns`
- Experiment names per-step: `tla_prompt_generation`, `tla_sanity_check_<backend>_<model>`, `tla_eval_<backend>_<model>`
- Artifacts logged: Generated `.tla`/`.cfg` files, validation logs, TLC output

## TLA+ Validation Pipeline

### SANY Parser (Syntax Validation)
- **Tool**: `java -cp /opt/tla/tla2tools.jar tla2sany.SANY <file.tla>`
- **Timeout**: 30 seconds (prevents hanging on invalid specs)
- **Success Signal**: `"Parsing completed"` in output
- **Artifact**: Logs saved to `sany_logs/<model>.sany.log`
- **Result States**: `PASS`, `FAIL`, `ERROR`, `MISSING`

### TLC Model Checker (Runtime Validation)
- **Tool**: `tlc -nowarning -config <file.cfg> <file.tla>`
- **Prerequisites**: Both `.tla` and `.cfg` required; `.cfg` resolved via fallback search if not in `generated/`
- **Success Signal**: `"The specification is correct"` in stdout
- **Failure Signals**: `"TLC threw an error"` or `"unexpected exception"` → `ERROR` status
- **Result States**: `PASS`, `FAIL`, `ERROR`, `SKIPPED` (missing .cfg)
- **Artifact**: Full TLC output logged to `<backend>_<model>/evaluations/<model>.tlc.log`

## Development Workflow

### Quick Start
```bash
./run.sh --setup           # Interactive backend selection + API key configuration
python test_llm.py --all   # Verify LLM backend connectivity
python run_pipeline.py     # Execute full pipeline (uses .env settings)
```

### Adding New Models
1. Create `data/<new_model_name>/` with subdirectories: `txt/`, `tla/`, `cfg/`
2. Add entry to `data/all_models.json` with fields: `model`, `comments_clean`, `tla_clean`, `cfg`
3. Update data splits: Add to `outputs/train.json`, `val.json`, or `test.json`
4. Re-run pipeline; outputs appear in `outputs/<backend>_<model>/generated/`

### Modifying Pipeline Steps
- **File**: Each step is decorated with `@step(enable_cache=False)` (no caching due to external tool deps)
- **Inputs/Outputs**: Steps return `Dict[str, str]` mapping `model_name → content/result_status`
- **Environment Access**: Load backend/model from `os.getenv("LLM_BACKEND")` and `os.getenv("LLM_MODEL")`
- **ZenML Requirements**: Return type must match downstream step input type

### Configuration via Environment Variables
- `LLM_BACKEND`: `openai` | `anthropic` | `ollama` (set by `run.sh --setup`)
- `LLM_MODEL`: Model name (e.g., `gpt-4`, `claude-3-5-sonnet-20241022`, `llama3.3`)
- `NUM_FEW_SHOTS`: Number of examples for few-shot learning (default: 3)
- `TLA_TOOLS_DIR`: Path to TLA+ tools JAR (default: `/opt/tla`)
- `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`: Required for respective backends
- `OLLAMA_BASE_URL`: Ollama endpoint (default: `http://localhost:11434`)

## Common Pitfalls & Solutions

| Issue | Root Cause | Fix |
|-------|-----------|-----|
| **Import Error**: `ModuleNotFoundError: No module named 'zenml'` | Missing dependencies | Run `pip install -r requirements.txt` |
| **TLC: Missing .cfg file** | Fallback search fails | Ensure `cfg/` subdirectory exists or check `data/all_models.json` |
| **SANY timeout** | Infinite loop in invalid spec | Already handled (30s timeout); check syntax |
| **"Parsing completed" not in output** | SANY failed silently | Check stderr in logs; grammar error likely |
| **MLflow artifacts not logged** | Wrong tracking URI | Verify `mlflow.set_tracking_uri()` called before `start_run()` |
| **Ollama connection refused** | Service not running | Run `docker-compose up ollama` or check `OLLAMA_BASE_URL` |
| **Generated files missing** | LLM returned empty | Check `LLM_MODEL` is valid for backend; review model output |

## Testing & Debugging

### View Generated Specifications
```bash
ls outputs/<backend>_<model>/generated/
cat outputs/<backend>_<model>/generated/<model_name>.tla
```

### Check Validation Logs
```bash
tail -f outputs/<backend>_<model>/evaluations/<model_name>.tlc.log
tail -f outputs/<backend>_<model>/sany_logs/<model_name>.sany.log
```

### Compare Results Across Models
```bash
python compare_models.py  # Generates comparison CSV and charts
```

### MLflow Dashboard
```bash
mlflow ui --backend-store-uri file://$(pwd)/mlruns
# Then visit http://localhost:5000
```