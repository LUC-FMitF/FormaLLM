#!/bin/bash
################################################################################
# FormaLLM Multi-LLM Pipeline Setup and Runner
################################################################################
# Enhanced script that:
# - Sets up environment variables for multiple LLM backends
# - Manages Docker Compose services for local LLMs
# - Supports development container post-create initialization
################################################################################

set -e

# Function to update or add environment variable in .env file
update_env_var() {
    local key=$1
    local value=$2
    local env_file=".env"
    
    # Create .env if it doesn't exist
    touch "$env_file"
    
    # Remove existing key if present
    if grep -q "^${key}=" "$env_file" 2>/dev/null; then
        # Use temporary file for cross-platform compatibility
        grep -v "^${key}=" "$env_file" > "${env_file}.tmp" && mv "${env_file}.tmp" "$env_file"
    fi
    
    # Add new value
    echo "${key}=\"${value}\"" >> "$env_file"
}

# Function to clean up old LLM configuration from .env
clean_llm_config() {
    local env_file=".env"
    
    if [ ! -f "$env_file" ]; then
        return
    fi
    
    echo ""
    echo "Cleaning previous LLM configuration..."
    
    # Remove all LLM-related variables (including old deprecated ones)
    local vars_to_remove=("LLM_BACKEND" "LLM_MODEL" "OLLAMA_DEPLOYMENT" "OLLAMA_BASE_URL" "OLLAMA_ENABLED" "OLLAMA_MODEL")
    
    for var in "${vars_to_remove[@]}"; do
        # Match both with and without quotes
        if grep -q "^${var}=" "$env_file" 2>/dev/null; then
            grep -v "^${var}=" "$env_file" > "${env_file}.tmp" && mv "${env_file}.tmp" "$env_file"
        fi
    done
    
    echo "Previous configuration cleared."
}

echo "============================================="
echo "   ZenML TLA+ Pipeline - LLM Selection"
echo "============================================="

# Check if this is a fresh setup or reconfiguration
if [ -f ".env" ] && grep -q "^LLM_BACKEND=" ".env" 2>/dev/null; then
    echo ""
    echo "Existing LLM configuration detected."
    current_backend=$(grep "^LLM_BACKEND=" ".env" | cut -d'=' -f2 | tr -d '"')
    current_model=$(grep "^LLM_MODEL=" ".env" | cut -d'=' -f2 | tr -d '"')
    echo "Current: Backend=$current_backend, Model=$current_model"
    echo ""
    read -p "Would you like to reconfigure? (y/n) [y]: " reconfigure
    reconfigure=${reconfigure:-y}
    
    if [[ ! "$reconfigure" =~ ^[Yy]$ ]]; then
        echo "Using existing configuration."
        echo ""
        echo "To run pipeline with current settings:"
        echo "  python run_pipeline.py --backend $current_backend --model $current_model"
        echo "or"
        echo "  python run_standalone.py --backend $current_backend --model $current_model"
        exit 0
    fi
    
    # Clean old configuration
    clean_llm_config
fi

echo ""
echo "Available LLM backends:"
echo "  1) GPT-4 (OpenAI)"
echo "  2) Claude (Anthropic)"
echo "  3) Ollama (Local)"
echo ""
read -p "Select LLM backend (1-3): " backend_choice

case $backend_choice in
    1)
        update_env_var "LLM_BACKEND" "openai"
        update_env_var "LLM_MODEL" "gpt-4"
        echo ""
        echo "Selected: GPT-4 (OpenAI)"

        if [ -z "$OPENAI_API_KEY" ]; then
            echo ""
            read -sp "Enter your OpenAI API key: " api_key
            echo ""
            update_env_var "OPENAI_API_KEY" "$api_key"
        else
            echo "Using existing OPENAI_API_KEY from environment"
        fi
        ;;
    2)
        update_env_var "LLM_BACKEND" "anthropic"
        update_env_var "LLM_MODEL" "claude-3-5-sonnet-20241022"
        echo ""
        echo "Selected: Claude (Anthropic)"

        if [ -z "$ANTHROPIC_API_KEY" ]; then
            echo ""
            read -sp "Enter your Anthropic API key: " api_key
            echo ""
            update_env_var "ANTHROPIC_API_KEY" "$api_key"
        else
            echo "Using existing ANTHROPIC_API_KEY from environment"
        fi
        ;;
    3)
        echo LLM_BACKEND="ollama" >> .env
        echo ""
        echo "Selected: Ollama"
        echo ""
        echo "Choose Ollama deployment option:"
        echo "  1) Native Ollama (installed on host system) - DEFAULT"
        echo "  2) Docker Compose Ollama (containerized service)"
        echo "  3) External Ollama (remote server or custom URL)"
        echo ""
        read -p "Select deployment (1-3) [1]: " ollama_deployment
        ollama_deployment=${ollama_deployment:-1}

        case $ollama_deployment in
            1)
                # Native Ollama installation
                echo ""
                echo "Using native Ollama installation"
                update_env_var "LLM_BACKEND" "ollama"
                update_env_var "OLLAMA_BASE_URL" "http://localhost:11434"

                if ! command -v ollama &> /dev/null; then
                    echo "Error: Ollama CLI not found. Please install Ollama first."
                    echo "Visit: https://ollama.ai/download"
                    exit 1
                fi

                echo "Available Ollama models on your system:"
                models=($(ollama list 2>/dev/null | tail -n +2 | awk '{print $1}'))

                if [ ${#models[@]} -eq 0 ]; then
                    echo "  No models installed."
                    echo ""
                    echo "Popular models for code generation:"
                    echo "  - llama3.1        (8B, 4.7GB)  - Good all-around"
                    echo "  - codellama       (7B, 3.8GB)  - Code specialized"
                    echo "  - deepseek-r1     (7B, 4.7GB)  - Reasoning model"
                    echo "  - qwq             (32B, 20GB)  - Advanced reasoning"
                    echo "  - phi4            (14B, 9.1GB) - Microsoft model"
                    echo "  - mistral         (7B, 4.1GB)  - Fast & capable"
                    echo "  - gemma3          (4B, 3.3GB)  - Google model"
                    echo ""
                    read -p "Enter model name to pull and use: " model_name
                    if [ -z "$model_name" ]; then
                        echo "No model specified. Exiting."
                        exit 1
                    fi
                    echo "Pulling model '$model_name'..."
                    ollama pull "$model_name"
                    if [ $? -ne 0 ]; then
                        echo "Failed to pull model. Exiting."
                        exit 1
                    fi
                    update_env_var "LLM_MODEL" "$model_name"
                else
                    for i in "${!models[@]}"; do
                        echo "  $((i+1))) ${models[$i]}"
                    done

                    echo ""
                    echo "Popular models (if not installed above):"
                    echo "  llama3.1, codellama, deepseek-r1, qwq, phi4, mistral, gemma3"
                    echo ""
                    read -p "Select model by number or enter model name [1]: " selection

                    selection=${selection:-1}

                    if [[ "$selection" =~ ^[0-9]+$ ]] && [ "$selection" -ge 1 ] && [ "$selection" -le "${#models[@]}" ]; then
                        update_env_var "LLM_MODEL" "${models[$((selection-1))]}"
                    else
                        update_env_var "LLM_MODEL" "$selection"

                        if ! ollama list 2>/dev/null | grep -q "^$selection"; then
                            echo ""
                            echo "Model '$selection' not found locally."
                            read -p "Do you want to pull it now? (y/n) [y]: " pull_model
                            pull_model=${pull_model:-y}

                            if [[ "$pull_model" =~ ^[Yy]$ ]]; then
                                echo "Pulling model '$selection'..."
                                ollama pull "$selection"
                                if [ $? -ne 0 ]; then
                                    echo "Failed to pull model. Exiting."
                                    exit 1
                                fi
                            else
                                echo "Cannot proceed without the model. Exiting."
                                exit 1
                            fi
                        fi
                    fi
                fi
                ;;

            2)
                # Docker Compose Ollama
                echo ""
                echo "Using Docker Compose Ollama service"
                update_env_var "LLM_BACKEND" "ollama"
                update_env_var "OLLAMA_BASE_URL" "http://localhost:11435"

                echo ""
                echo "Popular models for code generation:"
                echo "  - llama3.1        (8B, 4.7GB)  - Good all-around"
                echo "  - codellama       (7B, 3.8GB)  - Code specialized"
                echo "  - deepseek-r1     (7B, 4.7GB)  - Reasoning model"
                echo "  - qwq             (32B, 20GB)  - Advanced reasoning"
                echo "  - phi4            (14B, 9.1GB) - Microsoft model"
                echo "  - mistral         (7B, 4.1GB)  - Fast & capable"
                echo "  - gemma3          (4B, 3.3GB)  - Google model"
                echo ""
                read -p "Enter model name to use [llama3.1]: " ollama_model
                ollama_model=${ollama_model:-llama3.1}
                update_env_var "LLM_MODEL" "$ollama_model"

                echo ""
                echo "Starting Ollama Docker service..."
                
                # Check if Ollama is already running
                if docker compose ps ollama 2>/dev/null | grep -q "Up"; then
                    echo "Ollama service already running"
                elif docker compose ps ollama 2>/dev/null | grep -q "ollama"; then
                    echo "Restarting existing Ollama service..."
                    docker compose restart ollama
                else
                    echo "Creating new Ollama service..."
                    if ! docker compose up -d ollama; then
                        echo "Failed to start Ollama service"
                        echo "Try: docker compose down && docker compose up -d ollama"
                        exit 1
                    fi
                fi
                
                echo "Waiting for Ollama to be ready..."
                sleep 15
                
                # Test if Ollama is accessible
                echo "Testing Ollama connection..."
                if docker compose exec ollama curl -s http://localhost:11434/api/health >/dev/null 2>&1; then
                    echo "Ollama service is running"
                    
                    echo "Pulling model: $ollama_model"
                    if docker compose exec ollama ollama pull "$ollama_model"; then
                        echo "Model $ollama_model ready"
                    else
                        echo "Model pull failed - you can try manually later"
                    fi
                else
                    echo "Ollama may still be starting up"
                fi
                
                echo "Ollama Docker service configured"
                ;;

            3)
                # External Ollama server
                echo ""
                echo "Using external Ollama server"
                update_env_var "LLM_BACKEND" "ollama"
                
                read -p "Enter Ollama server URL [http://localhost:11434]: " ollama_url
                ollama_url=${ollama_url:-http://localhost:11434}
                update_env_var "OLLAMA_BASE_URL" "$ollama_url"

                read -p "Enter model name to use [llama3.1]: " ollama_model
                ollama_model=${ollama_model:-llama3.1}
                update_env_var "LLM_MODEL" "$ollama_model"

                echo "External Ollama configured at: $ollama_url"
                echo "Model: $ollama_model"
                ;;

            *)
                echo "Invalid selection. Defaulting to native Ollama."
                update_env_var "LLM_BACKEND" "ollama"
                update_env_var "OLLAMA_BASE_URL" "http://localhost:11434"
                update_env_var "LLM_MODEL" "llama3.1"
                ;;
        esac

        echo ""
        echo "Ollama configuration complete"
        ;;
    *)
        echo "Invalid selection. Exiting."
        exit 1
        ;;
esac

# Load the environment variables from .env file into current shell
if [ -f ".env" ]; then
    # Export only the LLM_BACKEND and LLM_MODEL variables
    export $(grep -E "^(LLM_BACKEND|LLM_MODEL)=" .env | xargs)
fi

echo ""
echo "============================================="
echo "Running pipeline with:"
echo "  Backend: ${LLM_BACKEND//\"/}"
echo "  Model: ${LLM_MODEL//\"/}"
echo "============================================="
echo ""

# Check for optional tracking services
check_tracking_services() {
    echo ""
    echo "Checking for tracking services..."
    
    # Check if MLflow is running on port 5001 (Docker) or 5000 (native)
    mlflow_running=false
    if curl -s http://localhost:5001/health >/dev/null 2>&1; then
        echo "MLflow server detected on port 5001 (Docker)"
        mlflow_running=true
    elif curl -s http://localhost:5000/health >/dev/null 2>&1; then
        echo "MLflow server detected on port 5000 (native)"
        mlflow_running=true
    elif lsof -Pi :5001 -sTCP:LISTEN -t >/dev/null 2>&1; then
        echo "Service detected on MLflow Docker port 5001"
        mlflow_running=true
    elif lsof -Pi :5000 -sTCP:LISTEN -t >/dev/null 2>&1; then
        echo "Service detected on MLflow native port 5000"
        mlflow_running=true
    fi
    
    # Check if ZenML server is running (port 8237)
    zenml_running=false
    
    # Try multiple methods to detect port 8237
    if ss -tlnp 2>/dev/null | grep -q ":8237"; then
        echo "ZenML server detected on port 8237 (via ss)"
        zenml_running=true
    elif netstat -tlnp 2>/dev/null | grep -q ":8237"; then
        echo "ZenML server detected on port 8237 (via netstat)"
        zenml_running=true
    elif lsof -Pi :8237 -sTCP:LISTEN -t >/dev/null 2>&1; then
        echo "ZenML server detected on port 8237 (via lsof)"
        zenml_running=true
    elif command -v zenml &> /dev/null && zenml status 2>/dev/null | grep -q "Running"; then
        echo "ZenML server is running (via zenml status)"
        zenml_running=true
    elif nc -z localhost 8237 2>/dev/null; then
        echo "ZenML server detected on port 8237 (via nc)"
        zenml_running=true
    fi
    
    # Offer to start services if not running
    if [ "$mlflow_running" = false ] || [ "$zenml_running" = false ]; then
        echo ""
        echo "Optional tracking services status:"
        [ "$mlflow_running" = true ] && echo "  MLflow: Running" || echo "  MLflow: Not running"
        [ "$zenml_running" = true ] && echo "  ZenML: Running" || echo "  ZenML: Not running"
        echo ""
        echo "These services are optional. The pipeline will work without them."
        read -p "Would you like to start missing services? (y/n) [n]: " start_services
        start_services=${start_services:-n}
        
        if [[ "$start_services" =~ ^[Yy]$ ]]; then
            # Start MLflow if not running
            if [ "$mlflow_running" = false ]; then
                echo ""
                echo "Starting MLflow..."
                echo "Choose MLflow deployment:"
                echo "  1) Docker Compose (port 5001)"
                echo "  2) Native Python (port 5000)"
                echo "  3) Skip MLflow"
                read -p "Select option (1-3) [1]: " mlflow_choice
                mlflow_choice=${mlflow_choice:-1}
                
                case $mlflow_choice in
                    1)
                        if docker compose ps mlflow 2>/dev/null | grep -q "Up"; then
                            echo "MLflow Docker service already running"
                        else
                            echo "Starting MLflow via Docker Compose..."
                            if docker compose --profile mlflow up -d mlflow; then
                                echo "MLflow started on http://localhost:5001"
                                sleep 3
                            else
                                echo "Warning: Failed to start MLflow Docker service"
                            fi
                        fi
                        ;;
                    2)
                        if lsof -Pi :5000 -sTCP:LISTEN -t >/dev/null 2>&1; then
                            echo "Port 5000 already in use. Skipping native MLflow."
                        else
                            echo "Starting MLflow in background..."
                            nohup mlflow server --host 0.0.0.0 --port 5000 > mlflow.log 2>&1 &
                            echo "MLflow started on http://localhost:5000 (logs: mlflow.log)"
                            sleep 3
                        fi
                        ;;
                    3)
                        echo "Skipping MLflow"
                        ;;
                esac
            fi
            
            # Start ZenML if not running
            if [ "$zenml_running" = false ]; then
                echo ""
                if command -v zenml &> /dev/null; then
                    read -p "Start ZenML server? (y/n) [n]: " start_zenml
                    start_zenml=${start_zenml:-n}
                    if [[ "$start_zenml" =~ ^[Yy]$ ]]; then
                        echo "Starting ZenML server..."
                        zenml up
                        sleep 3
                    fi
                else
                    echo "ZenML CLI not found. Skipping."
                fi
            fi
        else
            echo "Continuing without starting additional services."
        fi
    else
        echo "Tracking services already running."
    fi
    echo ""
}

# Check and optionally start tracking services
check_tracking_services

echo "Choose execution mode:"
echo "  1) ZenML orchestrated pipeline (full pipeline with tracking)"
echo "  2) Standalone mode (recommended - avoids ZenML/numba conflicts)"
echo ""
echo "Note: Configuration will be loaded from .env file"
read -p "Select mode (1-2) [default: 2]: " exec_mode
exec_mode=${exec_mode:-2}

case $exec_mode in
    1)
        echo ""
        echo "Starting ZenML pipeline..."
        if ! python run_pipeline.py; then
            echo ""
            echo "ZenML pipeline failed. This might be due to:"
            echo "  - ZenML configuration issues"
            echo "  - Missing ZenML initialization"
            echo ""
            echo "Try running standalone mode instead (option 2)"
            echo "Or reinitialize ZenML: zenml init"
            exit 1
        fi
        ;;
    2)
        echo ""
        echo "Starting standalone pipeline..."
        python run_standalone.py
        ;;
    *)
        echo "Invalid selection. Using standalone mode."
        echo ""
        python run_standalone.py
        ;;
esac

echo ""
echo "============================================="
echo "Pipeline execution completed!"
echo "============================================="

# Run regression tests if baseline exists
if [ -f "outputs/baseline_results.csv" ]; then
    echo ""
    echo "Running regression tests..."
    if python test_regression.py; then
        echo "✅ Regression tests passed!"
    else
        echo "❌ Regression tests failed!"
        echo ""
        read -p "Would you like to update the baseline? (y/n) [n]: " update_baseline
        update_baseline=${update_baseline:-n}
        if [[ "$update_baseline" =~ ^[Yy]$ ]]; then
            python test_regression.py --save-baseline
            echo "Baseline updated."
        fi
    fi
else
    echo ""
    echo "No baseline found. Creating initial baseline..."
    python test_regression.py --save-baseline
fi
