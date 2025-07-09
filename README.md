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
├── run_pipeline.py       # Entry point to launch the ZenML pipeline
├── mlruns/               # MLflow experiment logs (locally)
└── .env                  # File containing API keys (not tracked in source control)
```

---

## 🔧 Technologies and Tools

### OpenAI API (via `langchain-openai`)
- Powers the LLM prompting for TLA+ generation.
- Uses `gpt-4` to generate valid TLA+ specs and optional TLC configs.

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
   ```bash
   python run_pipeline.py
