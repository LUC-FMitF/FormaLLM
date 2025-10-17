# FormaLLM: Multi-LLM TLA+ Research Pipeline

This project explores the use of Large Language Models (LLMs) to automatically generate formal specifications in [TLA+](https://lamport.azurewebsites.net/tla/tla.html) from natural language descriptions (comments). The system supports multiple LLM backends (OpenAI, Anthropic, local Ollama), automated setup, and Docker Compose integration for comprehensive testing environments.

**Quick Start:** Run `./run.sh --setup` to interactively configure your LLM backends and start testing!

---

## Project Structure

```
FormaLLM/
├── .devcontainer/        
│   ├── Dockerfile         # Enhanced with Docker-in-Docker support
│   └── devcontainer.json  # Auto-setup via postCreateCommand
├── data/                 # Original and supporting data files
│   └── <model_name>/
│       ├── txt/          # Natural language comments
│       ├── tla/          # Ground-truth .tla files
│       └── cfg/          # Ground-truth .cfg files
├── outputs/
│   ├── evaluations/      # TLC logs and results
│   ├── generated/        # LLM-generated .tla and .cfg files
│   ├── test.json         # Testing metadata
│   ├── train.json        # Training metadata
│   └── val.json          # Validation metadata
├── steps/
│   ├── data_split_step.py         # Train/validation/test split
│   ├── evaluate_generated_step.py # TLC evaluation with multi-backend
│   ├── graph_results.py           # Results summary CSV + visualization
│   ├── parse_step.py              # SANY validation
│   └── prompt_step.py             # Enhanced multi-LLM prompting
├── pipelines/
│   └── tla_pipeline.py   # ZenML orchestration
├── requirements.txt      # Python dependencies
├── run.sh                # Enhanced multi-LLM setup & runner
├── docker-compose.yml    # Local LLM services (Ollama, MLflow, etc.)
├── .env.template         # Configuration template
├── run_pipeline.py       # ZenML pipeline runner
├── test_llm.py           # Multi-backend testing script
├── OLLAMA_MODELS.md      # Ollama model documentation
├── mlruns/               # MLflow experiment logs
└── .env                  # Your configuration (not tracked)
```

---

## Getting Started

### Option 1: Dev Container (Recommended)
The dev container automatically sets up the environment and prompts for LLM configuration:

1. **Open in VS Code Dev Container** (requires Docker)
2. **Automatic Setup**: The `postCreateCommand` runs `./run.sh --setup` 
3. **Follow Prompts**: Select your LLM backends and enter API keys
4. **Start Testing**: Run `python test_llm.py` or `./run.sh`

### Option 2: Manual Setup
```bash
# 1. Clone and install dependencies
git clone <repository>
cd FormaLLM
pip install -r requirements.txt

# 2. Configure LLM backends
./run.sh --setup

# 3. Test your configuration
python test_llm.py --all

# 4. Run the pipeline
./run.sh
```

---

## LLM Backend Configuration

### Supported Backends
The pipeline supports multiple LLM backends with seamless switching:

- **OpenAI GPT-4** (via `langchain-openai`) - High-quality commercial API
- **Anthropic Claude** (via `langchain-anthropic`) - Alternative commercial API  
- **Ollama** (via `langchain-ollama`) - Local/open-source models with Docker support

All backends use the same LangChain interface for consistent behavior.

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

   6. **Pipeline Execution**

   **Interactive Setup & Execution (Recommended)**
   ```bash
   # First-time setup
   ./run.sh --setup
   
   # Run pipeline with configured backend
   ./run.sh
   ```

   **Quick Commands**
   ```bash
   # Test LLM connections
   python test_llm.py --all
   
   # Direct pipeline execution
   python run_pipeline.py
   ```

---

## Multi-LLM Setup & Configuration

### 1. OpenAI GPT Configuration
```bash
./run.sh --setup  # Select option 1 or 4
# Enter your OpenAI API key when prompted
# Default model: gpt-4
```

**Environment Variables:**
```bash
OPENAI_API_KEY=sk-your-key-here
OPENAI_MODEL=gpt-4
LLM_BACKEND=openai
```

### 2. Anthropic Claude Configuration  
```bash
./run.sh --setup  # Select option 2 or 4
# Enter your Anthropic API key when prompted
# Default model: claude-3-5-sonnet-20241022
```

**Environment Variables:**
```bash
ANTHROPIC_API_KEY=sk-ant-your-key-here
ANTHROPIC_MODEL=claude-3-5-sonnet-20241022
LLM_BACKEND=anthropic
```

### 3. Ollama (Local) Configuration
```bash
./run.sh --setup  # Select option 3 or 4
# Choose to start via Docker Compose (recommended)
# Select your preferred model
```

**Docker Compose Integration:**
```bash
# Start Ollama service
docker-compose --profile ollama up -d

# Check service status
docker-compose ps

# View logs
docker-compose logs ollama

# Pull additional models
docker-compose exec ollama ollama pull codellama
```

**Popular Ollama Models:**
- `llama3.1` (8B, 4.7GB) - Recommended for general use
- `codellama` (7B, 3.8GB) - Code generation specialist  
- `deepseek-r1` (7B, 4.7GB) - Reasoning & code
- `qwq` (32B, 20GB) - Advanced reasoning
- `phi4` (14B, 9.1GB) - Microsoft flagship
- `mistral` (7B, 4.1GB) - Fast & capable

See [OLLAMA_MODELS.md](OLLAMA_MODELS.md) for the complete list.

---

## Docker Compose Services

The project includes comprehensive Docker Compose setup for local development:

```bash
# Start specific services
docker-compose --profile ollama up -d        # Ollama only
docker-compose --profile local-llm up -d     # All local LLMs
docker-compose --profile tracking up -d      # MLflow tracking
docker-compose --profile local-llm --profile tracking up -d  # Full setup
```

**Available Services:**
- **Ollama**: Local LLM inference (port 11435 - uses 11435 to avoid conflict with native installs)
- **LocalAI**: OpenAI-compatible local API (port 8080) 
- **Text Generation WebUI**: Gradio interface (port 7860)
- **MLflow Server**: Experiment tracking (port 5001)
- **Redis**: Caching (port 6379)

---

## Testing & Validation

### Test LLM Backends
```bash
# Test current backend
python test_llm.py

# Test all configured backends
python test_llm.py --all
```

### Environment Validation
```bash
# Check configuration
cat .env

# Validate Docker services
docker-compose ps

# Test pipeline end-to-end  
./run.sh
```

---

## Advanced Configuration

### Environment Variables (.env)
```bash
# Core LLM settings
LLM_BACKEND=ollama              # openai|anthropic|ollama
LLM_MODEL=llama3.1              # Backend-specific model

# OpenAI settings
OPENAI_API_KEY=sk-...
OPENAI_MODEL=gpt-4

# Anthropic settings  
ANTHROPIC_API_KEY=sk-ant-...
ANTHROPIC_MODEL=claude-3-5-sonnet-20241022

# Ollama settings
OLLAMA_ENABLED=true
OLLAMA_BASE_URL=http://localhost:11434  # Use 11435 for Docker Compose Ollama
OLLAMA_MODEL=llama3.1

# Pipeline settings
MLFLOW_TRACKING_URI=file:///workspaces/FormaLLM/mlruns
TLA_TOOLS_DIR=/opt/tla
```

Copy `.env.template` to `.env` and customize for your setup.

---

## Quick Start Workflows

### Ollama (Local, No API Keys)
```bash
./run.sh --setup
# → Select: 3 (Ollama)  
# → Choose: y (Docker Compose)
# → Model: llama3.1
python test_llm.py
./run.sh
```

### OpenAI (Commercial)
```bash  
./run.sh --setup
# → Select: 1 (OpenAI)
# → Enter: Your API key
python test_llm.py
./run.sh
```

### Multi-Backend Testing
```bash
./run.sh --setup
# → Select: 4 (Configure All)
# → Enter API keys and configure Ollama
python test_llm.py --all
./run.sh  # Switch backends as needed
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

## Enhanced Features

### Developer Experience Improvements
- **Automated Setup**: Dev container with `postCreateCommand` for zero-config start
- **Visual Feedback**: Color-coded terminal output with progress indicators
- **Smart Error Handling**: Specific troubleshooting guidance for configuration issues
- **⚡ Quick Testing**: Multi-backend validation with health checks

### Infrastructure & Deployment
- **Docker Integration**: Full Docker Compose stack for local LLM services
- **Experiment Tracking**: Enhanced MLflow integration with automatic logging
- **Environment Management**: Template-based configuration with security best practices
- **Flexible Backends**: Seamless switching between commercial and local LLMs

### Production Ready Features
- **Security**: API key validation and secure environment handling
- **Monitoring**: Comprehensive health checks and service orchestration
- **Scalability**: Profile-based deployment for different scenarios
- **Documentation**: Comprehensive setup guides and troubleshooting tips

---

## Additional Resources

- **[Ollama Models](OLLAMA_MODELS.md)**: Complete list of supported local models
- **[.env.template](.env.template)**: Configuration template with all options
- **[Docker Compose](docker-compose.yml)**: Service definitions and profiles
- **[Copilot Instructions](.github/copilot-instructions.md)**: AI coding agent guidance

---

## Contributing

1. **Fork the repository** and create your feature branch
2. **Test your changes** with `python test_llm.py --all`
3. **Update documentation** as needed
4. **Submit a pull request** with clear description of changes

For major changes, please open an issue first to discuss the proposed changes.

---

## License

This project is licensed under the MIT License - see the LICENSE file for details.
