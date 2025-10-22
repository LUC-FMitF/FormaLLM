#!/bin/bash
################################################################################
# FormaLLM Development Environment Setup Script
# 
# This script sets up your local development environment for FormaLLM including:
# - Python virtual environment with all dependencies
# - TLA+ tools installation
# - Environment configuration
# - MLflow tracking setup
# - Testing framework setup
#
# Usage: ./setup.sh [OPTIONS]
# Options:
#   --full         Full setup including TLA+ tools download
#   --venv-only    Only create/update virtual environment
#   --test         Setup for testing only
#   --api-keys     Configure API keys interactively
#   --help         Show this help message
################################################################################

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Default options
FULL_SETUP=false
VENV_ONLY=false
TEST_ONLY=false
API_KEYS=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --full)
            FULL_SETUP=true
            shift
            ;;
        --venv-only)
            VENV_ONLY=true
            shift
            ;;
        --test)
            TEST_ONLY=true
            shift
            ;;
        --api-keys)
            API_KEYS=true
            shift
            ;;
        --help)
            head -n 20 "$0" | tail -n +2 | sed 's/^# //'
            exit 0
            ;;
        *)
            log_error "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

echo "================================"
echo "  FormaLLM Environment Setup"
echo "================================"
echo ""

# Check system requirements
log_info "Checking system requirements..."

# Check Python
if ! command -v python3 &> /dev/null; then
    log_error "Python 3 is not installed. Please install Python 3.9 or higher."
    exit 1
fi

PYTHON_VERSION=$(python3 --version | cut -d' ' -f2)
log_success "Python $PYTHON_VERSION found"

# Check Java (required for TLA+ tools)
if ! command -v java &> /dev/null; then
    log_warning "Java is not installed. TLA+ tools require Java 8 or higher."
    log_info "Install Java with: brew install openjdk@11"
else
    JAVA_VERSION=$(java -version 2>&1 | head -n 1)
    log_success "Java found: $JAVA_VERSION"
fi

# Check Git
if ! command -v git &> /dev/null; then
    log_error "Git is not installed. Please install Git."
    exit 1
fi
log_success "Git found"

echo ""
log_info "Setting up Python virtual environment..."

# Create or activate virtual environment
if [ ! -d "venv" ]; then
    log_info "Creating new virtual environment..."
    python3 -m venv venv
    log_success "Virtual environment created"
else
    log_info "Virtual environment already exists"
fi

# Activate virtual environment
source venv/bin/activate
log_success "Virtual environment activated"

# Upgrade pip
log_info "Upgrading pip..."
pip install --upgrade pip setuptools wheel --quiet
log_success "pip upgraded"

# Install dependencies
log_info "Installing Python dependencies..."
pip install -r requirements.txt --quiet
log_success "Dependencies installed"

if [ "$VENV_ONLY" = true ]; then
    log_success "Virtual environment setup complete!"
    echo ""
    echo "To activate the virtual environment, run:"
    echo "  source venv/bin/activate"
    exit 0
fi

echo ""
log_info "Setting up environment configuration..."

# Create .env file if it doesn't exist
if [ ! -f ".env" ]; then
    log_info "Creating .env file..."
    cat > .env << 'EOF'
# API Keys and environmental variables

OLLAMA_ENABLED=true
OLLAMA_BASE_URL=http://localhost:11434
OLLAMA_MODEL=llama3.1
MLFLOW_TRACKING_URI=file:///Users/$USER/GitHub/FormaLLM/mlruns
TLA_TOOLS_DIR=/opt/tla

LLM_BACKEND=ollama
LLM_MODEL=llama3.1

# Uncomment and add your API keys if using cloud LLMs
# OPENAI_API_KEY=your-key-here
# ANTHROPIC_API_KEY=your-key-here

NUM_FEW_SHOTS=3
EOF
    log_success ".env file created"
else
    log_info ".env file already exists"
fi

# Update .env with correct paths
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS
    sed -i '' "s|file:///workspaces/FormaLLM|file://$(pwd)|g" .env
else
    # Linux
    sed -i "s|file:///workspaces/FormaLLM|file://$(pwd)|g" .env
fi

if [ "$API_KEYS" = true ]; then
    echo ""
    log_info "API Key Configuration"
    echo ""
    
    read -p "Do you want to configure OpenAI API key? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        read -p "Enter your OpenAI API key: " OPENAI_KEY
        if [[ "$OSTYPE" == "darwin"* ]]; then
            sed -i '' "s|# OPENAI_API_KEY=.*|OPENAI_API_KEY=$OPENAI_KEY|g" .env
        else
            sed -i "s|# OPENAI_API_KEY=.*|OPENAI_API_KEY=$OPENAI_KEY|g" .env
        fi
        log_success "OpenAI API key configured"
    fi
    
    echo ""
    read -p "Do you want to configure Anthropic API key? (y/n) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        read -p "Enter your Anthropic API key: " ANTHROPIC_KEY
        if [[ "$OSTYPE" == "darwin"* ]]; then
            sed -i '' "s|# ANTHROPIC_API_KEY=.*|ANTHROPIC_API_KEY=$ANTHROPIC_KEY|g" .env
        else
            sed -i "s|# ANTHROPIC_API_KEY=.*|ANTHROPIC_API_KEY=$ANTHROPIC_KEY|g" .env
        fi
        log_success "Anthropic API key configured"
    fi
fi

echo ""
log_info "Setting up TLA+ tools..."

# Check if TLA+ tools are installed
TLA_DIR="/opt/tla"
TLA_JAR="$TLA_DIR/tla2tools.jar"

if [ -f "$TLA_JAR" ]; then
    log_success "TLA+ tools found at $TLA_JAR"
else
    log_warning "TLA+ tools not found at $TLA_JAR"
    
    if [ "$FULL_SETUP" = true ]; then
        log_info "Downloading TLA+ tools..."
        
        # Create TLA directory
        sudo mkdir -p "$TLA_DIR"
        
        # Download TLA+ tools
        TLA_VERSION="1.8.0"
        TLA_URL="https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar"
        
        log_info "Downloading from $TLA_URL..."
        sudo curl -L "$TLA_URL" -o "$TLA_JAR"
        
        if [ -f "$TLA_JAR" ]; then
            log_success "TLA+ tools installed successfully"
        else
            log_error "Failed to download TLA+ tools"
            log_info "You can manually download from: https://github.com/tlaplus/tlaplus/releases"
        fi
    else
        log_info "To install TLA+ tools, run: ./setup.sh --full"
        log_info "Or manually download from: https://github.com/tlaplus/tlaplus/releases"
    fi
fi

# Create necessary directories
log_info "Creating output directories..."
mkdir -p outputs/generated
mkdir -p outputs/evaluations
mkdir -p mlruns
log_success "Directories created"

# Setup ZenML (optional)
if command -v zenml &> /dev/null; then
    log_info "Initializing ZenML..."
    zenml init 2>/dev/null || log_info "ZenML already initialized"
    log_success "ZenML ready"
fi

# Test setup
if [ "$TEST_ONLY" = true ] || [ "$FULL_SETUP" = true ]; then
    echo ""
    log_info "Running test suite to verify setup..."
    
    # Run a simple test
    python3 -m pytest tests/unit/test_utils.py::TestDataLoading::test_json_serialization -v
    
    if [ $? -eq 0 ]; then
        log_success "Tests passed! Setup verified."
    else
        log_warning "Some tests failed. Check configuration."
    fi
fi

echo ""
echo "================================"
log_success "Setup Complete!"
echo "================================"
echo ""
echo "Next steps:"
echo "  1. Activate virtual environment:"
echo "     $ source venv/bin/activate"
echo ""
echo "  2. Run tests:"
echo "     $ pytest tests/"
echo ""
echo "  3. Run the pipeline:"
echo "     $ python run_pipeline.py"
echo ""
echo "  4. For Ollama backend, ensure Ollama is running:"
echo "     $ ollama serve"
echo ""
echo "For more information, see:"
echo "  - README.md for project overview"
echo "  - TESTING.md for testing guidelines"
echo ""
