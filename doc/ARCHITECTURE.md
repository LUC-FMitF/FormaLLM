# FormaLLM Architecture

Technical overview of the FormaLLM research pipeline.

## System Overview

FormaLLM is a modular pipeline that:
1. Generates TLA+ formal specifications from natural language comments using LLMs
2. Validates specifications with SANY parser (syntax) and TLC model checker (semantics)
3. Analyzes validation results to understand LLM specification generation quality

```
Natural Language Comments
         ↓
    [LLM Models]
         ↓
   Generated .tla/.cfg
         ↓
    [SANY Parser]  (Syntax Validation)
         ↓
    [TLC Checker]  (Semantic Validation)
         ↓
   Validation Results & Metrics
         ↓
   [Analysis & Visualization]
```

## Core Components

### 1. Data Layer (`data/`)

**Structure**:
```
data/
├── all_models.json           # Metadata for 1800+ specifications
├── {spec_name}/              # One directory per specification
│   ├── txt/                  # Natural language comments
│   ├── tla/                  # Ground-truth TLA+ specifications
│   └── cfg/                  # TLC configuration files
└── train.json, val.json, test.json  # Data splits
```

**Key Files**:
- `all_models.json`: Maps specification names to comment/spec/config file paths
- `train.json`: Few-shot examples for LLM prompting (default: 3 examples)
- `val.json`, `test.json`: Validation/test sets

### 2. Pipeline Steps (`steps/`)

#### Prompt Step (`prompt_step.py`)
- **Input**: Natural language comments + few-shot examples
- **Process**:
  - Load training examples from `outputs/train.json`
  - Build ChatPromptTemplate with LangChain
  - Send to LLM backend (OpenAI/Anthropic/Ollama)
  - Parse LLM output into `.tla` and `.cfg` files
- **Output**: Generated specifications in `outputs/{backend}_{model}/generated/`
- **MLflow**: Logs prompts, LLM responses, and generated artifacts

#### Parse Step (`parse_step.py`)
- **Input**: Generated `.tla` files
- **Process**:
  - Run SANY parser: `java -cp /opt/tla/tla2tools.jar tla2sany.SANY <file.tla>`
  - Extract parse status (PASS/FAIL/ERROR)
  - Capture error messages and line numbers
  - Timeout: 30 seconds per specification
- **Output**: SANY logs and metrics in `sany_logs/`
- **MLflow**: Logs parse results and error analysis

#### Evaluation Step (`evaluate_generated_step.py`)
- **Input**: Generated `.tla` and `.cfg` files
- **Process**:
  - Run TLC model checker: `tlc -config <file.cfg> <file.tla>`
  - Extract execution status (PASS/FAIL/ERROR/SEMANTIC_ERROR)
  - Analyze state space metrics (states generated, depth, etc.)
  - Capture performance data (execution time, memory)
- **Output**: TLC logs and comprehensive metrics in `evaluations/`
- **MLflow**: Logs validation results and state space analysis

#### Analysis Step (`graph_results.py`)
- **Input**: Combined validation results from all steps
- **Process**:
  - Aggregate results across models and backends
  - Generate summary statistics
  - Create visualizations
  - Produce comparison tables
- **Output**: CSV summaries and PNG charts in `outputs/`

### 3. Orchestration (`pipelines/tla_pipeline.py`)

**ZenML Pipeline**:
```python
@pipeline
def tla_pipeline():
    # 1. Data split (train/val/test)
    data_split_step()
    
    # 2. LLM generation
    prompts = prompt_step()
    
    # 3. Syntax validation
    parses = parse_step(prompts)
    
    # 4. Semantic validation
    evaluations = evaluate_generated_step(parses)
    
    # 5. Results analysis
    graph_results(evaluations)
```

**ZenML Features**:
- Automatic caching (disabled for external tool dependencies)
- Parameter management
- Artifact versioning
- MLflow integration
- Pipeline lineage tracking

### 4. LLM Backends (`langchain` integration)

**Supported Backends**:

| Backend | Library | API | Models |
|---------|---------|-----|--------|
| **OpenAI** | `langchain-openai` | Commercial | GPT-4, GPT-4-Turbo |
| **Anthropic** | `langchain-anthropic` | Commercial | Claude 3, Claude 3.5 |
| **Ollama** | `langchain-ollama` | Local | Llama, CodeLlama, Deepseek |

**Selection via Environment**:
```bash
LLM_BACKEND=openai      # or anthropic, ollama
LLM_MODEL=gpt-4         # Backend-specific model
```

**Few-Shot Learning**:
- Default: 3 examples from training set
- Configurable via `NUM_FEW_SHOTS` env var
- Loaded from `outputs/train.json`

### 5. Validation Tools

#### SANY Parser
- **Tool**: TLA+ Syntax Analyzer (`tla2sany.SANY`)
- **Purpose**: Validate TLA+ grammar and semantic structure
- **Timeout**: 30 seconds
- **Success Indicator**: "Parsing completed" in output
- **Output**: Parse tree or error messages

#### TLC Model Checker
- **Tool**: TLA+ Model Checker (`tlc`)
- **Purpose**: Verify temporal properties and invariants
- **Timeout**: Depends on state space size (typically 60+ seconds)
- **Success Indicator**: "Model checking completed. No error has been found."
- **Output**: State space analysis or counterexample

### 6. Metrics Collection

#### SANY Metrics (`steps/sany_metrics.py`)
- Parse status (PASS/FAIL/ERROR)
- Error classification (type, location)
- First error line and message
- File size and line count

#### TLC Metrics (`steps/tlc_metrics.py`)
- Execution status (PASS/FAIL/ERROR/SEMANTIC_ERROR/TIMEOUT)
- State space: states generated, distinct states, depth
- Performance: execution time, memory usage, worker count
- Semantic errors: count, categorization, first error
- Temporal properties: detection and verification status

### 7. Experiment Tracking (`MLflow`)

**Tracking Configuration**:
```python
mlflow.set_tracking_uri(f"file://{outputs_dir}/mlruns")
mlflow.set_experiment(f"tla_{backend}_{model}")
```

**Logged Artifacts**:
- Generated `.tla` and `.cfg` files
- Validation logs (SANY, TLC)
- Metrics: pass/fail counts, state space analysis
- Model performance comparison

**Access Results**:
```bash
mlflow ui --backend-store-uri file://$(pwd)/outputs/mlruns
# Visit http://localhost:5000
```

## Data Flow

### From Comment to Validation

```
1. INPUT: Natural language comment (from data/{spec}/txt/)
   ↓
2. PROMPT: Build few-shot prompt with examples
   ↓
3. LLM: Send to backend (OpenAI/Anthropic/Ollama)
   ↓
4. GENERATION: Parse LLM output into .tla/.cfg files
   ↓
5. SANY: Syntax validation (parse_step.py)
   ├─ PASS → Continue to TLC
   └─ FAIL → Record error
   ↓
6. TLC: Semantic validation (evaluate_generated_step.py)
   ├─ PASS → Model verified ✓
   ├─ FAIL → Invariant violated ✗
   └─ ERROR → Timeout or crash
   ↓
7. OUTPUT: Metrics and validation results
   ├─ Stored in outputs/{backend}_{model}/
   └─ Logged to MLflow
```

## Directory Structure

```
FormaLLM/
├── data/                           # Input specifications
│   ├── all_models.json
│   ├── {spec_name}/
│   │   ├── txt/
│   │   ├── tla/
│   │   └── cfg/
│   ├── train.json
│   ├── val.json
│   └── test.json
│
├── steps/                          # Pipeline components
│   ├── prompt_step.py
│   ├── parse_step.py
│   ├── evaluate_generated_step.py
│   ├── sany_metrics.py
│   ├── tlc_metrics.py
│   └── graph_results.py
│
├── pipelines/                      # ZenML orchestration
│   └── tla_pipeline.py
│
├── outputs/                        # Results
│   ├── {backend}_{model}/
│   │   ├── generated/              # Generated .tla/.cfg
│   │   ├── evaluations/            # TLC logs & metrics
│   │   ├── sany_logs/              # SANY logs
│   │   └── mlruns/                 # MLflow experiments
│   ├── train.json, val.json
│   └── *.csv                       # Analysis results
│
├── run.sh                          # Setup & execution
├── run_pipeline.py                 # Entry point
├── requirements.txt                # Dependencies
└── docker-compose.yml              # Local services
```

## Execution Flow

### Single Run

```bash
python run_pipeline.py
```

**Environment Configuration**:
```bash
export LLM_BACKEND=ollama
export LLM_MODEL=llama3.1
export OPENAI_API_KEY=sk-...  # If using OpenAI
```

**Steps Executed**:
1. Load data splits
2. Generate specifications with LLM
3. Validate with SANY parser
4. Validate with TLC model checker
5. Generate analysis and visualizations

### Multi-Backend Comparison

**Setup**:
```bash
./run.sh --setup       # Configure multiple backends
python test_llm.py --all  # Verify all backends
```

**Run for Each Backend**:
```bash
for backend in openai anthropic ollama; do
    export LLM_BACKEND=$backend
    python run_pipeline.py
done
```

**Results Comparison**:
```bash
python scripts/compare_models.py
# Generates: comparison CSV and visualizations
```

## Performance Considerations

### Memory & Time

- **SANY Parse**: ~100-500ms per specification
- **TLC Model Check**: 1-10+ seconds (depends on state space)
- **LLM Generation**: 5-30 seconds (depends on backend and model)

### Parallelization

- **Current**: Sequential processing (one spec at a time)
- **Possible**: Batch TLC models with `-workers` parameter
- **Future**: Distribute across multiple machines via Ray or Dask

## Extension Points

### Adding a New LLM Backend

1. Create new step: `steps/{backend}_step.py`
2. Use LangChain: `langchain-{backend}` package
3. Implement interface: `generate(comment) → (tla, cfg)`
4. Register in `run.sh` setup script

### Adding Custom Analysis

1. Create new script: `scripts/analyze_{topic}.py`
2. Load results from `outputs/spec_differences_with_validation.csv`
3. Perform analysis and generate outputs
4. Integrate into pipeline via `graph_results.py`

### Adding New Metrics

1. **SANY**: Modify `steps/sany_metrics.py`
2. **TLC**: Modify `steps/tlc_metrics.py`
3. Update CSV headers and MLflow logging
4. Update analysis scripts to use new metrics

## Related Documentation

- [Setup Guide](SETUP_GUIDE.md): Installation and configuration
- [Development Guide](DEVELOPMENT.md): Contributing and modifications
- [Project README](../README.md): Overview and quick start
