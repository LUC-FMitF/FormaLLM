#!/bin/bash
################################################################################
# ZenML Pipeline Runner with LLM Backend Selection
################################################################################
# This script allows you to choose the LLM backend and handles API key setup
# for paid services (OpenAI, Anthropic).
################################################################################

set -e

echo "============================================="
echo "   ZenML TLA+ Pipeline - LLM Selection"
echo "============================================="
echo ""
echo "Available LLM backends:"
echo "  1) GPT-4 (OpenAI)"
echo "  2) Claude (Anthropic)"
echo "  3) Ollama (Local)"
echo ""
read -p "Select LLM backend (1-3): " backend_choice

case $backend_choice in
    1)
        export LLM_BACKEND="openai"
        export LLM_MODEL="gpt-4"
        echo ""
        echo "Selected: GPT-4 (OpenAI)"

        if [ -z "$OPENAI_API_KEY" ]; then
            echo ""
            read -sp "Enter your OpenAI API key: " api_key
            echo ""
            export OPENAI_API_KEY="$api_key"
        else
            echo "Using existing OPENAI_API_KEY from environment"
        fi
        ;;
    2)
        export LLM_BACKEND="anthropic"
        export LLM_MODEL="claude-3-5-sonnet-20241022"
        echo ""
        echo "Selected: Claude (Anthropic)"

        if [ -z "$ANTHROPIC_API_KEY" ]; then
            echo ""
            read -sp "Enter your Anthropic API key: " api_key
            echo ""
            export ANTHROPIC_API_KEY="$api_key"
        else
            echo "Using existing ANTHROPIC_API_KEY from environment"
        fi
        ;;
    3)
        export LLM_BACKEND="ollama"
        echo ""
        echo "Selected: Ollama"
        echo ""

        if ! command -v ollama &> /dev/null; then
            echo "Error: Ollama CLI not found. Please install Ollama first."
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
            export LLM_MODEL="$model_name"
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
                export LLM_MODEL="${models[$((selection-1))]}"
            else
                export LLM_MODEL="$selection"

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

        echo ""
        echo "Using model: $LLM_MODEL"
        ;;
    *)
        echo "Invalid selection. Exiting."
        exit 1
        ;;
esac

echo ""
echo "============================================="
echo "Running pipeline with:"
echo "  Backend: $LLM_BACKEND"
echo "  Model: $LLM_MODEL"
echo "============================================="
echo ""

echo "Choose execution mode:"
echo "  1) ZenML orchestrated pipeline (full pipeline with tracking)"
echo "  2) Standalone mode (recommended - avoids ZenML/numba conflicts)"
echo ""
read -p "Select mode (1-2) [default: 2]: " exec_mode
exec_mode=${exec_mode:-2}

case $exec_mode in
    1)
        python run_pipeline.py --backend "$LLM_BACKEND" --model "$LLM_MODEL"
        ;;
    2)
        python run_standalone.py --backend "$LLM_BACKEND" --model "$LLM_MODEL"
        ;;
    *)
        echo "Invalid selection. Using standalone mode."
        python run_standalone.py --backend "$LLM_BACKEND" --model "$LLM_MODEL"
        ;;
esac

echo ""
echo "============================================="
echo "Pipeline execution completed!"
echo "============================================="
