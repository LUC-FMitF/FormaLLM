# FormaLLM Setup Guide

Complete setup instructions for running the FormaLLM pipeline.

## Prerequisites

- **Python 3.8+**
- **Git**
- **Java** (for TLA+ tools - SANY and TLC)
- **Docker** (optional, for Ollama backend)

## Quick Start

### 1. Clone and Install

```bash
# Clone the repository
git clone https://github.com/LUC-FMitF/FormaLLM.git
cd FormaLLM

# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install dependencies
pip install -r requirements.txt
```

### 2. Configure LLM Backend

Run the interactive setup script:

```bash
./run.sh --setup
```

This will prompt you to:
1. Select an LLM backend (OpenAI, Anthropic, or Ollama)
2. Enter API keys (if using commercial backends)
3. Configure Ollama (if using local models)

### 3. Test Your Setup

```bash
# Test LLM connectivity
python test_llm.py

# Test all configured backends
python test_llm.py --all
```

### 4. Run the Pipeline

```bash
./run.sh
```

## Backend-Specific Setup

### OpenAI GPT-4

1. Get API key from [OpenAI Platform](https://platform.openai.com/)
2. Set environment variable:
   ```bash
   export OPENAI_API_KEY="sk-your-key-here"
   ```
3. Run setup: `./run.sh --setup` and select option 1

### Anthropic Claude

1. Get API key from [Anthropic Console](https://console.anthropic.com/)
2. Set environment variable:
   ```bash
   export ANTHROPIC_API_KEY="sk-ant-your-key-here"
   ```
3. Run setup: `./run.sh --setup` and select option 2

### Ollama (Local, No API Key Required)

1. Install Ollama from [ollama.ai](https://ollama.ai)
2. Pull a model:
   ```bash
   ollama pull llama3.1
   ```
3. Run setup: `./run.sh --setup` and select option 3
4. Or use Docker Compose:
   ```bash
   docker-compose --profile ollama up -d
   ```

## TLA+ Tools Setup

The pipeline requires TLA+ tools (SANY parser and TLC model checker).

### Automatic Setup

The tools should be at: `/opt/tla/tla2tools.jar`

If not installed:

```bash
# Download TLA+ tools
wget https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O /opt/tla/tla2tools.jar
```

### Set TLA_TOOLS_DIR

If your TLA+ tools are in a different location:

```bash
export TLA_TOOLS_DIR="/path/to/tla/directory"
```

## Environment Configuration

Create a `.env` file in the project root:

```bash
cp .env.template .env
```

Edit `.env` with your settings:

```bash
# LLM Backend Configuration
LLM_BACKEND=ollama              # openai|anthropic|ollama
LLM_MODEL=llama3.1

# OpenAI (if using)
OPENAI_API_KEY=sk-...
OPENAI_MODEL=gpt-4

# Anthropic (if using)
ANTHROPIC_API_KEY=sk-ant-...
ANTHROPIC_MODEL=claude-3-5-sonnet-20241022

# Ollama (if using)
OLLAMA_BASE_URL=http://localhost:11434
OLLAMA_MODEL=llama3.1

# Pipeline Settings
MLFLOW_TRACKING_URI=file://$(pwd)/mlruns
TLA_TOOLS_DIR=/opt/tla
NUM_FEW_SHOTS=3
```

## Docker Compose Setup

For containerized local development:

```bash
# Start Ollama service only
docker-compose --profile ollama up -d

# Start all local services
docker-compose --profile local-llm up -d

# Start with experiment tracking
docker-compose --profile tracking up -d

# Full setup
docker-compose --profile ollama --profile tracking up -d
```

Check service status:

```bash
docker-compose ps
```

View logs:

```bash
docker-compose logs -f ollama
```

## Troubleshooting

### Issue: "OPENAI_API_KEY not set"

**Solution**: Set your API key:
```bash
export OPENAI_API_KEY="your-key-here"
```

### Issue: "TLC not found"

**Solution**: Verify TLA+ tools location:
```bash
ls /opt/tla/tla2tools.jar
# Or set custom path:
export TLA_TOOLS_DIR="/your/path/to/tla"
```

### Issue: "Ollama connection refused"

**Solution**: Start Ollama service:
```bash
# If installed locally
ollama serve

# Or via Docker
docker-compose --profile ollama up -d
```

### Issue: "No module named 'zenml'"

**Solution**: Install dependencies:
```bash
pip install -r requirements.txt
```

## Verifying Installation

Run the verification script:

```bash
python test_llm.py --all
```

Expected output shows connectivity status for all configured backends:
- ✓ OpenAI: Connected (if configured)
- ✓ Anthropic: Connected (if configured)
- ✓ Ollama: Connected (if running)

## Next Steps

Once setup is complete:

1. Read [Architecture](ARCHITECTURE.md) for pipeline overview
2. Read [Development](DEVELOPMENT.md) for modifying components
3. Run `./run.sh` to start the pipeline
4. Check `outputs/` directory for results

## Getting Help

- Check log files in `outputs/`
- Review environment configuration: `cat .env`
- Test backend connectivity: `python test_llm.py`
- See project README for additional resources
