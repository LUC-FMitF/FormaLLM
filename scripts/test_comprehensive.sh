#!/bin/bash
# Comprehensive test: Temperature × Repeat_Penalty × New Prompting
# Usage: ./test_comprehensive.sh

set -e

VENV_PATH="/home/arslanbisharat/Documents/AI4SE/FormaLLM/venv"
if [ -d "$VENV_PATH" ]; then
    echo "Activating virtual environment..."
    source "$VENV_PATH/bin/activate"
else
    echo "Error: Virtual environment not found at $VENV_PATH"
    exit 1
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_BASE="outputs_parameters/comprehensive_${TIMESTAMP}"

echo "========================================"
echo "Comprehensive Parameter Test"
echo "Temperature × Repeat_Penalty × New Prompting"
echo "========================================"
echo "Output directory: $OUTPUT_BASE"
echo ""

mkdir -p "$OUTPUT_BASE"

# All 26 models
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

# Temperature values
TEMPERATURES=(0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8)

# Repeat penalty values
REPEAT_PENALTIES=(1.0 1.1 1.2 1.3 1.4 1.5)

SUMMARY_FILE="$OUTPUT_BASE/comprehensive_summary.csv"
echo "Model,Temperature,Repeat_Penalty,PASS,FAIL,ERROR,Total,Success_Rate(%)" > "$SUMMARY_FILE"

run_test() {
    local model=$1
    local temp=$2
    local penalty=$3
    local output_dir="$OUTPUT_BASE/${model}_temp_${temp}_penalty_${penalty}"

    echo "----------------------------------------"
    echo "Model: $model"
    echo "Temperature: $temp"
    echo "Repeat Penalty: $penalty"
    echo "----------------------------------------"

    export LLM_BACKEND="ollama"
    export LLM_MODEL="$model"
    export OLLAMA_TEMPERATURE="$temp"
    export OLLAMA_REPEAT_PENALTY="$penalty"
    export OLLAMA_BASE_URL="http://localhost:11434"

    mkdir -p "$output_dir"

    cat > "$output_dir/config.txt" <<EOF
Model: $model
Temperature: $temp
Repeat Penalty: $penalty
Timestamp: $(date)
Prompting: Progressive instructions (new technique)
EOF

    echo "Running pipeline..."
    if [ -f "run_pipeline.py" ]; then
        python run_pipeline.py \
            --backend ollama \
            --model "$model" \
            2>&1 | tee "$output_dir/run.log"
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
            echo "Results: PASS=$pass, FAIL=$fail, ERROR=$error, Total=$total, Success=${rate}%"
            echo "$model,$temp,$penalty,$pass,$fail,$error,$total,$rate" >> "$SUMMARY_FILE"
        else
            echo "$model,$temp,$penalty,0,0,0,0,0.00" >> "$SUMMARY_FILE"
        fi
    else
        echo "$model,$temp,$penalty,0,0,0,0,0.00" >> "$SUMMARY_FILE"
    fi

    echo ""
}

total_tests=$((${#MODELS[@]} * ${#TEMPERATURES[@]} * ${#REPEAT_PENALTIES[@]}))
current=0

echo "Total configurations to test: $total_tests"
echo "This will take a long time..."
echo ""

for model in "${MODELS[@]}"; do
    for temp in "${TEMPERATURES[@]}"; do
        for penalty in "${REPEAT_PENALTIES[@]}"; do
            current=$((current + 1))
            echo "=== Progress: $current / $total_tests ==="
            run_test "$model" "$temp" "$penalty"
        done
    done
done

echo "========================================"
echo "All tests completed!"
echo "========================================"
echo ""
echo "Generating analysis..."

# Create per-model summary
cat > "$OUTPUT_BASE/analysis.txt" <<EOF
Comprehensive Test Results
==========================

Test Parameters:
- Models: ${#MODELS[@]}
- Temperatures: ${#TEMPERATURES[@]} (${TEMPERATURES[@]})
- Repeat Penalties: ${#REPEAT_PENALTIES[@]} (${REPEAT_PENALTIES[@]})
- Total Configurations: $total_tests

New Prompting Technique:
- Progressive instructions (3 levels)
- Context building across examples
- Final instruction before target

Results saved to: $OUTPUT_BASE

Summary file: comprehensive_summary.csv
EOF

cat "$OUTPUT_BASE/analysis.txt"
echo ""
echo "Top 10 best configurations:"
echo "Model,Temperature,Repeat_Penalty,Success_Rate(%)"
tail -n +2 "$SUMMARY_FILE" | sort -t',' -k8 -rn | head -10 | cut -d',' -f1,2,3,8

echo ""
echo "Full results:"
echo "  cat $OUTPUT_BASE/comprehensive_summary.csv | column -t -s','"
