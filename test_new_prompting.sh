#!/bin/bash
set -e

VENV_PATH="/home/arslanbisharat/Documents/AI4SE/FormaLLM/venv"
if [ -d "$VENV_PATH" ]; then
    source "$VENV_PATH/bin/activate"
else
    echo "Error: Virtual environment not found at $VENV_PATH"
    exit 1
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_BASE="outputs_parameters/new_prompting_${TIMESTAMP}"

mkdir -p "$OUTPUT_BASE"

MODELS=(
    "codellama:latest"
    "deepseek-coder:6.7b"
    "deepseek-coder:latest"
    "deepseek-r1:1.5b"
    "deepseek-r1:7b"
    "deepseek-r1:8b"
    "deepseek-r1:14b"
    "deepseek-r1:32b"
    "deepseek-r1:70b"
    "deepseek-r1:671b"
    "gemma:2b"
    "gpt-oss:20b"
    "gpt-oss:120b"
    "granite3.3:latest"
    "llama3:latest"
    "llama3.1:8b"
    "llama3.2:1b"
    "llama3.3:70b"
    "llama3.3:latest"
    "mistral:latest"
    "phi4-mini:latest"
    "qwen3:4b-thinking"
    "qwen3:30b-thinking"
    "qwen3:235b-thinking"
    "qwq:latest"
    "starling-lm:latest"
)

REPEAT_PENALTIES=(1.0 1.1 1.2 1.3 1.4 1.5)
TEMPERATURES=(0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8)

SUMMARY_FILE="$OUTPUT_BASE/prompting_summary.csv"
echo "Model,Temperature,Repeat_Penalty,PASS,FAIL,ERROR,Total,Success_Rate(%)" > "$SUMMARY_FILE"

run_test() {
    local model=$1
    local penalty=$2
    local temperature=$3
    local output_dir="$OUTPUT_BASE/${model}_temp_${temperature}_penalty_${penalty}"

    mkdir -p "$output_dir"

    export LLM_BACKEND="ollama"
    export LLM_MODEL="$model"
    export OLLAMA_TEMPERATURE="$temperature"
    export OLLAMA_REPEAT_PENALTY="$penalty"
    export OLLAMA_BASE_URL="http://localhost:11434"

    cat > "$output_dir/config.txt" <<EOF
Model: $model
Temperature: $temperature
Repeat Penalty: $penalty
Timestamp: $(date)
Prompting: Progressive instructions (new)
EOF

    if [ -f "run_pipeline.py" ]; then
        timeout 600 python run_pipeline.py \
            --backend ollama \
            --model "$model" \
            2>&1 | tee "$output_dir/run.log"

        exit_code=$?
        if [ $exit_code -eq 124 ]; then
            echo "TIMEOUT: Pipeline exceeded 10 minutes" >> "$output_dir/run.log"
        elif [ $exit_code -ne 0 ]; then
            echo "ERROR: Pipeline failed with exit code $exit_code" >> "$output_dir/run.log"
        fi
    else
        echo "Error: run_pipeline.py not found"
        return 1
    fi

    source_dir="outputs/ollama_${model}"
    if [ -d "$source_dir" ]; then
        cp -r "$source_dir"/* "$output_dir/" 2>/dev/null || true
    fi

    if [ -f "$output_dir/evaluations/evaluation_results.csv" ]; then
        total=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | wc -l)
        pass=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,PASS" || true)
        fail=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,FAIL" || true)
        error=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,ERROR" || true)

        if [ $total -gt 0 ]; then
            rate=$(awk "BEGIN {printf \"%.2f\", ($pass/$total)*100}")
            echo "$model,$temperature,$penalty,$pass,$fail,$error,$total,$rate" >> "$SUMMARY_FILE"
        else
            echo "$model,$temperature,$penalty,0,0,0,0,0.00" >> "$SUMMARY_FILE"
        fi
    else
        echo "$model,$temperature,$penalty,0,0,0,0,0.00" >> "$SUMMARY_FILE"
    fi
}

total_tests=$((${#MODELS[@]} * ${#REPEAT_PENALTIES[@]} * ${#TEMPERATURES[@]}))
current=0

for model in "${MODELS[@]}"; do
    for temperature in "${TEMPERATURES[@]}"; do
        for penalty in "${REPEAT_PENALTIES[@]}"; do
            current=$((current + 1))
            percent=$((current * 100 / total_tests))
            bar_length=50
            filled=$((percent * bar_length / 100))
            empty=$((bar_length - filled))

            printf "\r["
            printf "%${filled}s" | tr ' ' '='
            printf "%${empty}s" | tr ' ' '-'
            printf "] %d%% (%d/%d) Model: %-30s Temp: %.1f Penalty: %.1f" \
                "$percent" "$current" "$total_tests" "$model" "$temperature" "$penalty"

            run_test "$model" "$penalty" "$temperature" > /dev/null 2>&1
        done
    done
done
echo ""

echo "All tests completed!"
echo "Results saved to: $OUTPUT_BASE"
