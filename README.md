# TLA+ LLM Research Pipeline

This project explores the use of Large Language Models (LLMs) to automatically generate formal specifications in [TLA+](https://lamport.azurewebsites.net/tla/tla.html) from natural language descriptions (comments). The generated specifications are syntactically validated using the TLA+ SANY parser and optionally executed with TLC.

---

## 📂 Project Structure

```
FormaLLM/
├── .devcontainer/        
│   └──Dockerfile         # Custom environment with Java, Python, etc.
│   └──devcontainer.json  # VS Code dev container config
├── data/                 # Original and supporting data files
│   └── <model_name>/
│       ├── txt/          # Natural language comments
│       ├── tla/          # Ground-truth .tla files
│       └── cfg/          # Ground-truth .cfg files
├── outputs/
│   ├── evaluations/      # TLC logs
│   ├── generated/        # LLM-generated .tla and .cfg files
│   ├── test.json         # Testing metadata
│   ├── train.json        # Training metadata
│   └── val.json          # Validation metadata
├── steps/
│   ├── data_split_step.py         # Used for initial train, validation, test split
│   ├── evaluate_generated_step.py # TLC evaluation 
│   ├── graph_results.py.          # Results summar CSV + bar chart
│   ├── parse_step.py              # SANY validation
│   ├── prompt_step.py             # LangChain/LLM prompting logic
│   └── setup.sh.                  # Zenml + MLFlow setup script for experiments/logging
├── pipelines/
│   └── tla_pipeline.py   # Orchestrates full pipeline
├── requirements.txt      # Python environment
├── run.sh                # Interactive pipeline runner (recommended)
├── run_pipeline.py       # ZenML pipeline runner with CLI args
├── run_standalone.py     # Standalone runner (no ZenML, useful for compatibility)
├── test_llm.py           # Quick LLM backend test script
├── OLLAMA_MODELS.md      # Documentation for Ollama models
├── mlruns/               # MLflow experiment logs (locally)
└── .env                  # File containing API keys (not tracked in source control)
```

---

## 🔧 Technologies and Tools

### LLM Backends (Configurable)
The pipeline supports multiple LLM backends:
- **OpenAI GPT-4** (via `langchain-openai`) - High-quality commercial API
- **Anthropic Claude** (via `langchain-anthropic`) - Alternative commercial API
- **Ollama** (via `langchain-ollama`) - Local/open-source models (llama3.1, codellama, deepseek-r1, etc.)

All backends are used interchangeably through the same LangChain interface.

### LangChain
- Handles the prompt logic and LLM chaining.
- Few-shot examples are embedded into prompts to improve generation quality.

### MLflow
- Logs all LLM traces, inputs/outputs, and artifacts.
- Tracks model performance over time.
- Automatically captures LangChain events using `mlflow.langchain.autolog()`.

### ZenML
- Orchestrates the full pipeline across modular steps.
- Handles reproducibility, caching, logging, and parameterization.

### TLC / SANY (Java)
- Validates the generated `.tla` files using the official TLA+ parser (SANY).
- Run through subprocess calls from within Python.

---

## Pipeline Overview

1. **Prompting Step (`prompt_step.py`)**
   - Loads training (few-shot) and validation data.
   - Builds prompts using comments and examples.
   - Sends the prompt to the LLM using LangChain.
   - Saves generated `.tla` and `.cfg` files under `outputs/generated/`.

2. **TLC Evaluation (`evaluate_generated_step.py`)**
   - Loads each generated `.tla` and `.cfg` file.
   - Runs the TLC via Java subprocess.
   - Logs `PASS`, `FAIL`, or `ERROR` status per file.

3. **Sanity Check Step (`parse_step.py`)**
   - Loads each generated `.tla` file.
   - Runs the SANY parser via Java subprocess.
   - Logs `PASS`, `FAIL`, or `ERROR` status per file.

4. **Tables and Graphs (`graph_results.py`)**
   -  Reads `evaluation_results.csv` from the `outputs/evaluations/` directory.
   - Counts the number of models with each result (`PASS`, `FAIL`, `ERROR`, etc.).
   - Saves Artifacts**:
       - `evaluation_summary.csv`: Tabular breakdown of results by type.
       - `evaluation_summary.png`: Bar chart of model validation outcomes.
   -  Prints the summary table directly to the console for quick insights.


5. **Pipeline Orchestration (`tla_pipeline.py`)**
   - Built using ZenML’s `@pipeline` decorator.
   - Chains the prompt and sanity steps.
   - Automatically tracks MLflow logs per run.

6. **Execution**

   **Option A: Interactive Script (Recommended)**
   ```bash
   ./run.sh
   ```
   - Select LLM backend (GPT-4, Claude, or Ollama)
   - Enter API keys for paid services (OpenAI/Anthropic)
   - Choose from available Ollama models
   - Select execution mode (ZenML orchestrated or standalone)

   **Option B: Direct Execution**
   ```bash
   # Using environment variables
   LLM_BACKEND=ollama LLM_MODEL=llama3.1 python run_standalone.py

   # Or with CLI arguments
   python run_standalone.py --backend ollama --model llama3.1

   # ZenML orchestrated pipeline
   python run_pipeline.py --backend openai --model gpt-4
   ```

---

## LLM Backend Configuration

### Supported Backends

#### 1. OpenAI (GPT-4)
```bash
export OPENAI_API_KEY="your-api-key-here"
./run.sh  # Select option 1
```

#### 2. Anthropic (Claude)
```bash
export ANTHROPIC_API_KEY="your-api-key-here"
./run.sh  # Select option 2
```

#### 3. Ollama (Local Models)
```bash
# Install Ollama first: https://ollama.ai
ollama pull llama3.1  # or any other model
./run.sh  # Select option 3
```

**Popular Ollama Models:**
- `llama3.1` - 8B params, 4.7GB - Recommended for general use
- `codellama` - 7B params, 3.8GB - Code generation specialist
- `deepseek-r1` - 7B params, 4.7GB - Reasoning & code
- `qwq` - 32B params, 20GB - Advanced reasoning
- `phi4` - 14B params, 9.1GB - Microsoft flagship
- `mistral` - 7B params, 4.1GB - Fast & capable

See [OLLAMA_MODELS.md](OLLAMA_MODELS.md) for the complete list.

### API Key Management

**For paid APIs (OpenAI/Anthropic):**
1. The interactive script (`./run.sh`) will prompt for API keys
2. Or set environment variables:
   ```bash
   export OPENAI_API_KEY="sk-..."
   export ANTHROPIC_API_KEY="sk-ant-..."
   ```

**For Ollama:**
- No API key needed
- Runs 100% locally
- Requires Ollama to be installed and running

---

## Quick Start

### Using Ollama (Local, No API Key Required)
```bash
# 1. Install Ollama
# Visit https://ollama.ai

# 2. Pull a model
ollama pull llama3.1

# 3. Run the pipeline
./run.sh
# Select: 3 (Ollama) → 1 (llama3.1) → 2 (Standalone mode)
