#!/bin/bash
# Re-run failed models (Total=0) from temperature test
# Usage: ./rerun_failed_models.sh

set -e

# Activate virtual environment
VENV_PATH="/home/arslanbisharat/Documents/AI4SE/FormaLLM/venv"
if [ -d "$VENV_PATH" ]; then
    echo "Activating virtual environment..."
    source "$VENV_PATH/bin/activate"
else
    echo "Error: Virtual environment not found at $VENV_PATH"
    exit 1
fi

# Use the existing test directory
OUTPUT_BASE="outputs_parameters/temperature_test_20251111_091135"
SUMMARY_FILE="$OUTPUT_BASE/temperature_summary.csv"

echo "========================================"
echo "Re-running Failed Models"
echo "========================================"
echo "Directory: $OUTPUT_BASE"
echo ""

# Models that failed (Total=0 in summary)
FAILED_MODELS=(
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
    "granite3.3:latest"
    "llama3:latest"
    "llama3.3:latest"
    "qwen3:4b-thinking"
    "qwen3:30b-thinking"
    "qwen3:235b-thinking"
    "starling-lm:latest"
)

# Temperature values to test
TEMPERATURES=(0.0 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8)

# Function to run a single test
run_test() {
    local model=$1
    local temp=$2
    local output_dir="$OUTPUT_BASE/${model}_temp_${temp}"

    echo "----------------------------------------"
    echo "Re-running: $model with temperature=$temp"
    echo "----------------------------------------"

    # Set environment variables
    export LLM_BACKEND="ollama"
    export LLM_MODEL="$model"
    export OLLAMA_TEMPERATURE="$temp"
    export OLLAMA_BASE_URL="http://localhost:11434"

    # Remove old failed directory
    if [ -d "$output_dir" ]; then
        echo "Removing old failed test directory..."
        rm -rf "$output_dir"
    fi

    # Create output directory
    mkdir -p "$output_dir"

    # Save configuration
    cat > "$output_dir/config.txt" <<EOF
Model: $model
Temperature: $temp
Timestamp: $(date)
Rerun: Yes (fixing NameError bug)
EOF

    # Run the pipeline
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

    # The pipeline outputs to a model-specific directory, so we need to find and copy results
    # ZenML outputs to outputs/ollama_<model>/ directory
    source_dir="outputs/ollama_${model}"
    if [ -d "$source_dir" ]; then
        echo "Copying results from $source_dir to $output_dir..."
        cp -r "$source_dir"/* "$output_dir/" 2>/dev/null || true
    fi

    # Calculate success rate
    if [ -f "$output_dir/evaluations/evaluation_results.csv" ]; then
        total=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | wc -l)
        pass=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,PASS" || true)
        fail=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,FAIL" || true)
        error=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,ERROR" || true)

        if [ $total -gt 0 ]; then
            rate=$(awk "BEGIN {printf \"%.2f\", ($pass/$total)*100}")
            echo "Results: PASS=$pass, FAIL=$fail, ERROR=$error, Total=$total, Success Rate=${rate}%"

            # Update the summary file by removing old line and adding new one
            grep -v "^${model},${temp}," "$SUMMARY_FILE" > "$SUMMARY_FILE.tmp" || true
            echo "$model,$temp,$pass,$fail,$error,$total,$rate" >> "$SUMMARY_FILE.tmp"
            mv "$SUMMARY_FILE.tmp" "$SUMMARY_FILE"
        else
            echo "No results found"
            grep -v "^${model},${temp}," "$SUMMARY_FILE" > "$SUMMARY_FILE.tmp" || true
            echo "$model,$temp,0,0,0,0,0.00" >> "$SUMMARY_FILE.tmp"
            mv "$SUMMARY_FILE.tmp" "$SUMMARY_FILE"
        fi
    else
        echo "No evaluation results found"
        grep -v "^${model},${temp}," "$SUMMARY_FILE" > "$SUMMARY_FILE.tmp" || true
        echo "$model,$temp,0,0,0,0,0.00" >> "$SUMMARY_FILE.tmp"
        mv "$SUMMARY_FILE.tmp" "$SUMMARY_FILE"
    fi

    echo ""
}

# Run tests for all failed model combinations
total_tests=$((${#FAILED_MODELS[@]} * ${#TEMPERATURES[@]}))
current=0

for model in "${FAILED_MODELS[@]}"; do
    for temp in "${TEMPERATURES[@]}"; do
        current=$((current + 1))
        echo "Progress: $current / $total_tests"
        run_test "$model" "$temp"
    done
done

# Sort the summary file by model and temperature
echo "Sorting summary file..."
(head -n 1 "$SUMMARY_FILE" && tail -n +2 "$SUMMARY_FILE" | sort -t',' -k1,1 -k2,2n) > "$SUMMARY_FILE.tmp"
mv "$SUMMARY_FILE.tmp" "$SUMMARY_FILE"

echo "========================================"
echo "Re-run completed!"
echo "========================================"
echo "Updated summary: $SUMMARY_FILE"
echo ""
echo "To view results:"
echo "  cat $SUMMARY_FILE | column -t -s','"
echo ""
echo "Failed models that were re-run: ${#FAILED_MODELS[@]}"
echo "Total tests executed: $total_tests"
