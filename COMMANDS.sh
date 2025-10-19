#!/bin/bash
# Quick reference commands for FormaLLM development

# SETUP COMMANDS
# =============================================================================

# Full setup (first time only)
./setup.sh --full

# Just virtual environment
./setup.sh --venv-only

# Setup and run verification tests
./setup.sh --test

# Configure API keys interactively
./setup.sh --api-keys

# Activate virtual environment (run this in each new terminal)
source venv/bin/activate

# Check setup status
python3 --version
java -version
pip list | grep -E "pytest|langchain|zenml|mlflow"


# TESTING COMMANDS
# =============================================================================

# Run all tests
pytest tests/ -v

# Run unit tests only
pytest tests/unit/ -v

# Run integration tests only
pytest tests/integration/ -v

# Run tests with coverage
pytest tests/ --cov=steps --cov=pipelines --cov-report=html
open htmlcov/index.html  # macOS

# Run fast tests (skip slow ones)
pytest tests/ -m "not slow"

# Run specific test file
pytest tests/unit/test_parse_step.py -v

# Run specific test class
pytest tests/unit/test_parse_step.py::TestSanityCheckSANY -v

# Run specific test method
pytest tests/unit/test_parse_step.py::TestSanityCheckSANY::test_successful_parse -v

# Run with debug output
pytest tests/ -vv -s

# Run with debugger on failure
pytest tests/ --pdb

# Show test durations
pytest tests/ --durations=10


# PIPELINE COMMANDS
# =============================================================================

# Run with Ollama (default, no API key required)
python run_pipeline.py --backend ollama --model llama3.1

# Run with OpenAI
python run_pipeline.py --backend openai --model gpt-4

# Run with Anthropic
python run_pipeline.py --backend anthropic --model claude-3-opus-20240229


# OLLAMA SETUP (if using local LLM)
# =============================================================================

# Install Ollama (macOS)
brew install ollama

# Start Ollama server (run in separate terminal)
ollama serve

# Pull model
ollama pull llama3.1

# Test Ollama
ollama run llama3.1 "Write a simple TLA+ spec"


# MLFLOW COMMANDS
# =============================================================================

# Start MLflow UI
mlflow ui --backend-store-uri file://$(pwd)/mlruns
# Then open http://localhost:5000

# Start MLflow UI on different port
mlflow ui --backend-store-uri file://$(pwd)/mlruns --port 5001


# DEVELOPMENT COMMANDS
# =============================================================================

# Check for errors in specific file
python -c "import steps.parse_step; print('✓ parse_step imports successfully')"
python -c "import steps.prompt_step; print('✓ prompt_step imports successfully')"
python -c "import steps.evaluate_generated_step; print('✓ evaluate_generated_step imports successfully')"

# Validate TLA+ tools installation
ls -la /opt/tla/tla2tools.jar
java -jar /opt/tla/tla2tools.jar -help

# Check environment variables
cat .env
env | grep -E "LLM_|TLA_|MLFLOW_"

# List available models
ls data/ | grep -v "all_models.json"

# View example model
cat data/Paxos/txt/Paxos_comments.txt
cat data/Paxos/tla/Paxos.tla

# Check outputs
ls -la outputs/generated/
ls -la outputs/evaluations/


# DATA EXPLORATION
# =============================================================================

# Count total models
jq '.data | length' data/all_models.json

# List train/val/test splits
jq 'length' outputs/train.json
jq 'length' outputs/val.json
jq 'length' outputs/test.json

# Show first model in train set
jq '.[0]' outputs/train.json

# Find models with TLC configs
jq -r '.data[] | select(.cfg != null) | .model' data/all_models.json | head -10


# GIT COMMANDS
# =============================================================================

# Status
git status

# Add new tests
git add tests/

# Commit
git commit -m "Add comprehensive test suite"

# Push
git push origin main


# CLEANUP COMMANDS
# =============================================================================

# Remove generated files
rm -rf outputs/generated/*
rm -rf outputs/evaluations/*

# Remove MLflow runs
rm -rf mlruns/*

# Clean Python cache
find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null
find . -type f -name "*.pyc" -delete

# Remove virtual environment (to start fresh)
rm -rf venv/


# DEBUGGING COMMANDS
# =============================================================================

# Check if module can be imported
python -c "import sys; sys.path.insert(0, '.'); import steps.parse_step"

# Run single step manually
python -c "
from pathlib import Path
import sys
sys.path.insert(0, '.')
from dotenv import load_dotenv
load_dotenv()
# Test imports
print('✓ All imports successful')
"

# Test TLA+ tools
echo '---- MODULE Test ----\nVARIABLE x\nInit == x = 0\n====' > /tmp/test.tla
java -cp /opt/tla/tla2tools.jar tla2sany.SANY /tmp/test.tla


# QUICK VERIFICATION
# =============================================================================

# Verify setup is complete
./setup.sh --test

# Quick smoke test
pytest tests/unit/test_utils.py::TestJSONUtilities::test_json_serialization -v

# Check all systems
python3 -c "
import sys
print(f'Python: {sys.version}')
"
java -version 2>&1 | head -1
echo "TLA+ tools: $([ -f /opt/tla/tla2tools.jar ] && echo '✓ installed' || echo '✗ missing')"
echo "Virtual env: $([ -d venv ] && echo '✓ exists' || echo '✗ missing')"


# USEFUL ALIASES (add to ~/.zshrc)
# =============================================================================

# alias formal-activate="cd ~/GitHub/FormaLLM && source venv/bin/activate"
# alias formal-test="cd ~/GitHub/FormaLLM && source venv/bin/activate && pytest tests/"
# alias formal-run="cd ~/GitHub/FormaLLM && source venv/bin/activate && python run_pipeline.py"
# alias formal-mlflow="cd ~/GitHub/FormaLLM && mlflow ui --backend-store-uri file://$(pwd)/mlruns"
