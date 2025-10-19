# FormaLLM - Quick Setup Guide

This guide will help you get FormaLLM running on your machine quickly.

## Prerequisites

- **Python 3.9+** (already installed ✓)
- **Java 8+** (already installed ✓)
- **Git** (already installed ✓)

## Quick Setup (5 minutes)

### 1. Run the Setup Script

```bash
cd /Users/eric/GitHub/FormaLLM
./setup.sh --full
```

This will:
- ✓ Create Python virtual environment
- ✓ Install all dependencies
- ✓ Download TLA+ tools
- ✓ Configure environment variables
- ✓ Create necessary directories
- ✓ Run verification tests

### 2. Activate Virtual Environment

```bash
source venv/bin/activate
```

### 3. Configure API Keys (Optional)

If you want to use OpenAI or Anthropic instead of Ollama:

```bash
./setup.sh --api-keys
```

Or manually edit `.env`:

```bash
# For OpenAI
OPENAI_API_KEY=your-key-here
LLM_BACKEND=openai
LLM_MODEL=gpt-4

# For Anthropic
ANTHROPIC_API_KEY=your-key-here
LLM_BACKEND=anthropic
LLM_MODEL=claude-3-opus-20240229
```

### 4. Verify Setup

```bash
# Run tests to verify everything works
pytest tests/unit/test_utils.py -v

# Check TLA+ tools
java -jar /opt/tla/tla2tools.jar -help
```

## Running the Pipeline

### With Ollama (Default - No API Key Required)

```bash
# Start Ollama (in a separate terminal)
ollama serve

# Pull the model if you haven't
ollama pull llama3.1

# Run the pipeline
python run_pipeline.py --backend ollama --model llama3.1
```

### With OpenAI

```bash
python run_pipeline.py --backend openai --model gpt-4
```

### With Anthropic

```bash
python run_pipeline.py --backend anthropic --model claude-3-opus-20240229
```

## Running Tests

```bash
# Run all tests
pytest tests/ -v

# Run only fast tests
pytest tests/ -m "not slow"

# Run with coverage
pytest tests/ --cov=steps --cov=pipelines --cov-report=html
open htmlcov/index.html
```

## Project Structure

```
FormaLLM/
├── pipelines/          # ZenML pipeline definitions
│   └── tla_pipeline.py
├── steps/              # Pipeline steps
│   ├── prompt_step.py       # LLM prompting
│   ├── parse_step.py        # SANY validation
│   ├── evaluate_generated_step.py  # TLC checking
│   └── graph_results.py
├── tests/              # Test suite
│   ├── unit/          # Unit tests
│   └── integration/   # Integration tests
├── data/              # TLA+ models and comments
├── outputs/           # Generated specs and results
└── mlruns/           # MLflow tracking data
```

## Common Commands

```bash
# Activate virtual environment
source venv/bin/activate

# Run pipeline with default settings
python run_pipeline.py

# Run specific tests
pytest tests/unit/test_parse_step.py -v

# View MLflow UI
mlflow ui --backend-store-uri file://$(pwd)/mlruns

# Check environment
python -c "import langchain; import zenml; print('✓ All imports work')"
```

## Next Steps

1. **Read the documentation**:
   - `README.md` - Project overview
   - `TESTING.md` - Testing guide
   - `.github/copilot-instructions.md` - Architecture details

2. **Explore the data**:
   ```bash
   ls data/  # See available models
   cat data/Paxos/txt/Paxos_comments.txt  # Example comments
   cat data/Paxos/tla/Paxos.tla  # Example TLA+ spec
   ```

3. **Run your first experiment**:
   ```bash
   # Generate specs for validation set
   python run_pipeline.py
   
   # Check results
   ls outputs/generated/
   ls outputs/evaluations/
   ```

4. **View results in MLflow**:
   ```bash
   mlflow ui
   # Open http://localhost:5000 in browser
   ```

## Troubleshooting

### Virtual environment not activating
```bash
# Make sure you're in the project directory
cd /Users/eric/GitHub/FormaLLM
source venv/bin/activate
```

### TLA+ tools not found
```bash
# Check installation
ls -la /opt/tla/tla2tools.jar

# If missing, download manually
sudo mkdir -p /opt/tla
sudo curl -L https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -o /opt/tla/tla2tools.jar
```

### Ollama not working
```bash
# Install Ollama (if not installed)
brew install ollama  # macOS

# Start Ollama server
ollama serve

# Pull model
ollama pull llama3.1

# Test it
ollama run llama3.1 "Hello!"
```

### Import errors
```bash
# Reinstall dependencies
pip install -r requirements.txt --force-reinstall
```

### Tests failing
```bash
# Update environment paths in .env
# Make sure MLFLOW_TRACKING_URI and TLA_TOOLS_DIR are correct
cat .env
```

## Getting Help

- **Documentation**: See `README.md` and `TESTING.md`
- **Issues**: Check GitHub issues
- **Code**: Copilot instructions in `.github/copilot-instructions.md`

## Quick Reference

### Environment Variables (.env)
```bash
LLM_BACKEND=ollama|openai|anthropic
LLM_MODEL=llama3.1|gpt-4|claude-3-opus-20240229
TLA_TOOLS_DIR=/opt/tla
MLFLOW_TRACKING_URI=file:///path/to/mlruns
NUM_FEW_SHOTS=3
```

### Test Markers
```bash
-m unit           # Unit tests only
-m integration    # Integration tests only
-m "not slow"     # Skip slow tests
-m "not requires_tla"  # Skip TLA+ tool tests
```

### Pipeline Commands
```bash
./setup.sh --full         # Full setup
./setup.sh --venv-only    # Just venv
./setup.sh --test         # Setup + tests
./setup.sh --api-keys     # Configure API keys
```

You're all set! 🚀
