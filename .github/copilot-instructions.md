# FormaLLM AI Assistant Instructions

## Project Overview
FormaLLM is a research pipeline that uses Large Language Models to generate formal TLA+ specifications from natural language comments. The system validates generated specs using TLA+ SANY parser and TLC model checker.

## Architecture & Data Flow
- **Entry Point**: `run_pipeline.py` → `pipelines/tla_pipeline.py` (ZenML orchestration)
- **Pipeline Steps**: `prompt_step.py` → `parse_step.py` → `evaluate_generated_step.py` → `graph_results.py`
- **Data Structure**: `data/<model_name>/{txt/,tla/,cfg/}` contains comments, ground-truth specs, and configs
- **Outputs**: Generated specs in `outputs/generated/`, evaluations in `outputs/evaluations/`

## Key Patterns & Conventions

### Data Organization
- Each formal model has a dedicated directory: `data/<model_name>/`
- Standard subdirectories: `txt/` (comments), `tla/` (specs), `cfg/` (TLC configs)
- File naming: `<model>_comments.txt`, `<model>.tla`, `<model>.cfg`
- Metadata in `data/all_models.json` maps model IDs to file paths

### Pipeline Development
- All steps use `@step` decorator from ZenML for orchestration
- Steps return dictionaries mapping `model_name → content/results`
- Use `pathlib.Path` for cross-platform file handling
- Environment variables: `TLA_TOOLS_DIR` (default: `/opt/tla`) for TLA+ tools location

### LLM Integration
- LangChain handles prompting with few-shot examples from `outputs/train.json`
- MLflow auto-logging captures LangChain traces: `mlflow.langchain.autolog()`
- Experiments organized by pipeline step: "tla_prompt_generation", "tla_eval", etc.
- API keys in `.env` file (not tracked in git)

### TLA+ Validation Pipeline
- **SANY Parser**: Syntax validation via `java -cp tla2tools.jar tla2sany.SANY <file>`
- **TLC Model Checker**: Runtime validation requires both `.tla` and `.cfg` files
- **File Resolution**: Uses fallback search with `Path.rglob()` for missing files
- **Timeout Handling**: 30-second subprocess timeouts prevent hanging on invalid specs

### Error Handling & Logging
- Result states: `PASS`, `FAIL`, `ERROR`, `SKIPPED`, `MISSING`
- MLflow tracing with `@mlflow.trace()` decorator for external tool calls
- Comprehensive logging to both console and MLflow for debugging

## Development Workflow

### Running the Pipeline
```bash
python run_pipeline.py  # Executes full ZenML pipeline
```

### Adding New Models
1. Create `data/<model_name>/` directory structure
2. Add entry to `data/all_models.json`
3. Update train/val/test splits in `outputs/*.json`

### Modifying Pipeline Steps
- Steps are independent and cacheable by ZenML
- Return types must match expected inputs of downstream steps
- Use `enable_cache=False` for steps with external dependencies

### TLA+ Tools Integration
- Ensure Java runtime available for TLA+ tools
- Tools expect absolute paths and proper classpath setup
- Use subprocess with timeout for external tool calls

## Common Pitfalls
- **File Path Resolution**: Always use absolute paths; fallback search can be slow
- **MLflow Tracking**: Set tracking URI before creating experiments
- **TLC Dependencies**: Generated `.cfg` files required for TLC evaluation
- **Environment Setup**: Missing `TLA_TOOLS_DIR` breaks validation steps