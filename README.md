# FormaLLM

Research pipeline for automatic TLA+ specification generation from natural language using Large Language Models. Supports OpenAI GPT, Anthropic Claude, and local Ollama models.

## Quick Start

```bash
./run.sh --setup    # Configure LLM backends
python test_llm.py  # Verify setup
./run.sh            # Run pipeline
```

## Project Structure

```
FormaLLM/
├── data/           # Input data (comments, TLA+ specs, configs)
├── outputs/        # Generated specs and evaluation results
├── steps/          # Pipeline components (prompt, parse, evaluate)
├── pipelines/      # ZenML orchestration
├── run.sh          # Setup and execution script
└── docker-compose.yml  # Local services (Ollama, MLflow)
```

## Supported Backends

- **OpenAI**: Commercial GPT models
- **Anthropic**: Claude models  
- **Ollama**: Local open-source models

## Pipeline Steps

1. **Prompt Generation**: LLM generates TLA+ specs from comments
2. **SANY Validation**: Syntax checking with detailed error analysis
3. **TLC Evaluation**: Model checking with comprehensive metrics
4. **Results Analysis**: Statistics and visualization

## Configuration

Copy `.env.template` to `.env` and set your preferences:

```bash
LLM_BACKEND=ollama
LLM_MODEL=llama3.1
OPENAI_API_KEY=sk-...     # If using OpenAI
ANTHROPIC_API_KEY=sk-...  # If using Anthropic
```

## Documentation

- [Setup Guide](doc/SETUP_GUIDE.md)
- [Architecture](doc/ARCHITECTURE.md) 
- [Development](doc/DEVELOPMENT.md)

## License

MIT License

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
   - Runs TLC model checker via Java subprocess.
   - **Enhanced Metrics Collection**: Comprehensive analysis including:
     - Execution status classification (PASS/FAIL/ERROR/SEMANTIC_ERROR/TIMEOUT)
     - Semantic error analysis with detailed categorization
     - State space exploration metrics (states generated, depth, outdegree)
     - Performance data (execution time, memory usage, worker configuration)
     - Temporal properties detection and analysis
   - Exports: `tlc_metrics.csv`, `evaluation_results.csv`, individual `.tlc.log` files

3. **SANY Parsing (`parse_step.py`)**
   - Loads each generated `.tla` file.
   - Runs SANY syntax parser via Java subprocess.
   - **Enhanced Metrics Collection**: Detailed syntax analysis including:
     - Parse success/failure classification with specific error types
     - Error location analysis (early/mid/late line categorization)
     - Character-specific issue detection (backticks, semicolons, Unicode)
     - First error extraction with context and categorization
   - Exports: `sany_metrics.csv`, individual `.sany.log` files

4. **Results Analysis (`graph_results.py` + Enhanced Analytics)**
   - Reads comprehensive metrics from `tlc_metrics.csv` and `sany_metrics.csv`
   - Generates summary statistics and visualizations
   - Provides detailed error pattern analysis and performance insights
   - **📊 For detailed metrics documentation, see [docs/ENHANCED_METRICS.md](docs/ENHANCED_METRICS.md)**
   - Saves artifacts:
     - `evaluation_summary.csv`: Tabular breakdown of results by type
     - `evaluation_summary.png`: Bar chart of model validation outcomes
   - Advanced analysis available via `analyze_tlc_metrics.py`


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
- **Quick Testing**: Multi-backend validation with health checks

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
