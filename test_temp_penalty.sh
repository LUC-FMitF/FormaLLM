#!/bin/bash
set -e

VENV_PATH="/home/arslanbisharat/Documents/AI4SE/FormaLLM - Single Prompt/venv"
if [ -d "$VENV_PATH" ]; then
    source "$VENV_PATH/bin/activate"
else
    echo "Error: Virtual environment not found at $VENV_PATH"
    exit 1
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_BASE="outputs_parameters/old_prompting_${TIMESTAMP}"

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

REPEAT_PENALTIES=(1.0 1.1 1.2 1.3 1.4 1.5 1.6 1.7 1.8 1.9 2.0)
TEMPERATURES=(0.0 0.3 0.5 0.7 1.0)

COPY_OLD_RESULTS=false
MIN_DISK_SPACE_GB=10
SKIP_SUCCESSFUL=true
PREVIOUS_RUN="outputs_parameters/old_prompting_20251205_144000"

export OLLAMA_NUM_PREDICT=8192

SMALL_MODEL_TIMEOUT=600
MEDIUM_MODEL_TIMEOUT=1200
LARGE_MODEL_TIMEOUT=1800

SUMMARY_FILE="prompting_summary.csv"
echo "Model,Temperature,Repeat_Penalty,PASS,FAIL,ERROR,Total,Success_Rate(%),Exit_Status,Duration_Minutes" > "$SUMMARY_FILE"

ERROR_LOG="error_summary.log"
echo "Experiment Error Log - $(date)" > "$ERROR_LOG"
echo "======================================" >> "$ERROR_LOG"

SUMMARY_FILE_BACKUP="$OUTPUT_BASE/prompting_summary.csv"
ERROR_LOG_BACKUP="$OUTPUT_BASE/error_summary.log"

check_disk_space() {
    local available_gb=$(df -BG . | tail -1 | awk '{print $4}' | sed 's/G//')
    if [ "$available_gb" -lt "$MIN_DISK_SPACE_GB" ]; then
        echo "ERROR: Low disk space! Only ${available_gb}GB available (minimum: ${MIN_DISK_SPACE_GB}GB)"
        return 1
    fi
    return 0
}

get_timeout_for_model() {
    local model=$1
    if [[ $model =~ ([0-9]+)b ]]; then
        local size=${BASH_REMATCH[1]}
        if [ "$size" -ge 50 ]; then
            echo $LARGE_MODEL_TIMEOUT
        elif [ "$size" -ge 10 ]; then
            echo $MEDIUM_MODEL_TIMEOUT
        else
            echo $SMALL_MODEL_TIMEOUT
        fi
    else
        echo $SMALL_MODEL_TIMEOUT
    fi
}

categorize_error() {
    local log_file=$1

    if grep -q "Received signal shutdown 15" "$log_file"; then
        echo "TIMEOUT"
    elif grep -q "llama runner process has terminated" "$log_file"; then
        echo "RUNNER_CRASH"
    elif grep -q "timed out waiting for llama runner to start" "$log_file"; then
        echo "RUNNER_TIMEOUT"
    elif grep -q "No space left on device" "$log_file"; then
        echo "DISK_FULL"
    elif grep -q "HTTP/1.1 500" "$log_file"; then
        echo "HTTP_500"
    elif grep -q "Pipeline run has failed" "$log_file"; then
        echo "PIPELINE_FAILED"
    else
        echo "SUCCESS"
    fi
}

already_succeeded() {
    local model=$1
    local temperature=$2
    local penalty=$3

    if [ "$SKIP_SUCCESSFUL" = false ] || [ -z "$PREVIOUS_RUN" ]; then
        return 1
    fi

    if [ ! -d "$PREVIOUS_RUN" ]; then
        return 1
    fi

    local prev_dir="$PREVIOUS_RUN/${model}_temp_${temperature}_penalty_${penalty}"

    if [ -f "$prev_dir/evaluations/evaluation_results.csv" ]; then
        local total=$(tail -n +2 "$prev_dir/evaluations/evaluation_results.csv" 2>/dev/null | wc -l)
        if [ "$total" -gt 0 ]; then
            local status=$(categorize_error "$prev_dir/run.log" 2>/dev/null)
            if [ "$status" = "SUCCESS" ] || [ "$status" = "PIPELINE_FAILED" ]; then
                local new_dir="$OUTPUT_BASE/${model}_temp_${temperature}_penalty_${penalty}"
                mkdir -p "$new_dir"
                cp -r "$prev_dir"/* "$new_dir/" 2>/dev/null || true
                return 0
            fi
        fi
    fi

    return 1
}

run_test() {
    local model=$1
    local penalty=$2
    local temperature=$3
    local output_dir="$OUTPUT_BASE/${model}_temp_${temperature}_penalty_${penalty}"

    if already_succeeded "$model" "$temperature" "$penalty"; then
        local error_status=$(categorize_error "$output_dir/run.log")
        if [ -f "$output_dir/evaluations/evaluation_results.csv" ]; then
            total=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | wc -l)
            pass=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,PASS" || true)
            fail=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,FAIL" || true)
            error=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,ERROR" || true)
            rate=$(awk "BEGIN {printf \"%.2f\", ($pass/$total)*100}")
            echo "$model,$temperature,$penalty,$pass,$fail,$error,$total,$rate,SKIPPED_${error_status},0.00" >> "$SUMMARY_FILE"
        fi
        return 0
    fi

    if ! check_disk_space; then
        echo "$model,$temperature,$penalty,0,0,0,0,0.00,DISK_FULL,0.00" >> "$SUMMARY_FILE"
        echo "[$(date)] $model (temp=$temperature, penalty=$penalty): DISK_FULL" >> "$ERROR_LOG"
        return 1
    fi

    mkdir -p "$output_dir"
    local timeout_seconds=$(get_timeout_for_model "$model")
    local start_time=$(date +%s)

    export CUDA_VISIBLE_DEVICES=0
    export LLM_BACKEND="ollama"
    export LLM_MODEL="$model"
    export OLLAMA_TEMPERATURE="$temperature"
    export OLLAMA_REPEAT_PENALTY="$penalty"
    export OLLAMA_BASE_URL="http://localhost:11434"
    export CUSTOM_OUTPUT_DIR="$output_dir"

    cat > "$output_dir/config.txt" <<EOF
Model: $model
Temperature: $temperature
Repeat Penalty: $penalty
Timeout: ${timeout_seconds}s
Timestamp: $(date)
Prompting: Single prompting
EOF

    if [ -f "run_pipeline.py" ]; then
        python run_pipeline.py \
            --backend ollama \
            --model "$model" \
            2>&1 | tee "$output_dir/run.log"

        exit_code=$?
        if [ $exit_code -ne 0 ]; then
            echo "ERROR: Pipeline failed with exit code $exit_code" >> "$output_dir/run.log"
        fi
    else
        echo "Error: run_pipeline.py not found"
        return 1
    fi

    # Check if module timing file was created (now directly in output_dir)
    if [ -f "$output_dir/module_timings.csv" ]; then
        echo "  Module timings saved to: $output_dir/module_timings.csv"
    fi

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    local duration_minutes=$(awk "BEGIN {printf \"%.2f\", ($duration/60)}")

    local error_status=$(categorize_error "$output_dir/run.log")

    if [ -f "$output_dir/evaluations/evaluation_results.csv" ]; then
        total=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | wc -l)
        pass=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,PASS" || true)
        fail=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,FAIL" || true)
        error=$(tail -n +2 "$output_dir/evaluations/evaluation_results.csv" | grep -c "^[^,]*,ERROR" || true)

        if [ $total -gt 0 ]; then
            rate=$(awk "BEGIN {printf \"%.2f\", ($pass/$total)*100}")
            echo "$model,$temperature,$penalty,$pass,$fail,$error,$total,$rate,$error_status,$duration_minutes" >> "$SUMMARY_FILE"
        else
            echo "$model,$temperature,$penalty,0,0,0,0,0.00,$error_status,$duration_minutes" >> "$SUMMARY_FILE"
        fi
    else
        echo "$model,$temperature,$penalty,0,0,0,0,0.00,$error_status,$duration_minutes" >> "$SUMMARY_FILE"
    fi

    if [ "$error_status" != "SUCCESS" ]; then
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] $model (temp=$temperature, penalty=$penalty, duration=${duration_minutes}min): $error_status" >> "$ERROR_LOG"
    else
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] $model (temp=$temperature, penalty=$penalty, duration=${duration_minutes}min): SUCCESS" >> "$ERROR_LOG"
    fi
}

total_tests=$((${#MODELS[@]} * ${#REPEAT_PENALTIES[@]} * ${#TEMPERATURES[@]}))
current=0
skipped_count=0

echo "Configuration:"
echo "  Skip successful: $SKIP_SUCCESSFUL"
if [ -n "$PREVIOUS_RUN" ] && [ "$SKIP_SUCCESSFUL" = true ]; then
    echo "  Previous run: $PREVIOUS_RUN"
fi
echo ""

for model in "${MODELS[@]}"; do
    for temperature in "${TEMPERATURES[@]}"; do
        for penalty in "${REPEAT_PENALTIES[@]}"; do
            current=$((current + 1))
            percent=$((current * 100 / total_tests))
            bar_length=50
            filled=$((percent * bar_length / 100))
            empty=$((bar_length - filled))

            skip_marker=""
            if already_succeeded "$model" "$temperature" "$penalty" 2>/dev/null; then
                skip_marker=" [SKIP]"
                skipped_count=$((skipped_count + 1))
            fi

            printf "\r["
            printf "%${filled}s" | tr ' ' '='
            printf "%${empty}s" | tr ' ' '-'
            printf "] %d%% (%d/%d) Model: %-30s Temp: %.1f Penalty: %.1f%s" \
                "$percent" "$current" "$total_tests" "$model" "$temperature" "$penalty" "$skip_marker"

            run_test "$model" "$penalty" "$temperature" > /dev/null 2>&1
        done
    done
done
echo ""

cp "$SUMMARY_FILE" "$SUMMARY_FILE_BACKUP"
cp "$ERROR_LOG" "$ERROR_LOG_BACKUP"

# Generate combined module timings report
COMBINED_TIMINGS="$OUTPUT_BASE/combined_module_timings.csv"
echo "Model,Temperature,Repeat_Penalty,Module,Duration_Seconds,Duration_Minutes" > "$COMBINED_TIMINGS"

for model in "${MODELS[@]}"; do
    for temperature in "${TEMPERATURES[@]}"; do
        for penalty in "${REPEAT_PENALTIES[@]}"; do
            timing_file="$OUTPUT_BASE/${model}_temp_${temperature}_penalty_${penalty}/module_timings.csv"
            if [ -f "$timing_file" ]; then
                tail -n +2 "$timing_file" | while IFS=, read -r module duration_sec duration_min; do
                    echo "$model,$temperature,$penalty,$module,$duration_sec,$duration_min" >> "$COMBINED_TIMINGS"
                done
            fi
        done
    done
done

echo "All tests completed!"
echo "Results saved to: $OUTPUT_BASE"
echo "Summary CSV: $SUMMARY_FILE"
echo "Combined module timings: $COMBINED_TIMINGS"
echo "Error log: $ERROR_LOG"
echo ""
echo "Summary Statistics:"
echo "==================="

if [ -f "$SUMMARY_FILE" ]; then
    total_experiments=$(tail -n +2 "$SUMMARY_FILE" | wc -l)
    successful=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",SUCCESS$" || true)
    skipped=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",SKIPPED_" || true)
    timeouts=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",TIMEOUT$" || true)
    runner_crashes=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",RUNNER_CRASH$" || true)
    runner_timeouts=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",RUNNER_TIMEOUT$" || true)
    disk_full=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",DISK_FULL$" || true)
    http_500=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",HTTP_500$" || true)
    pipeline_failed=$(tail -n +2 "$SUMMARY_FILE" | grep -c ",PIPELINE_FAILED$" || true)

    echo "Total experiments: $total_experiments"
    echo "Successful (new): $successful"
    if [ "$skipped" -gt 0 ]; then
        echo "Skipped (from previous run): $skipped"
    fi
    echo "Failed breakdown:"
    echo "  - Timeouts: $timeouts"
    echo "  - Runner crashes: $runner_crashes"
    echo "  - Runner timeouts: $runner_timeouts"
    echo "  - Disk full: $disk_full"
    echo "  - HTTP 500 errors: $http_500"
    echo "  - Pipeline failures: $pipeline_failed"
    echo ""

    actually_run=$((total_experiments - skipped))
    new_successful=$successful
    echo "Experiments actually run: $actually_run"
    if [ "$actually_run" -gt 0 ]; then
        echo "Success rate (new runs): $(awk "BEGIN {printf \"%.2f%%\", ($new_successful/$actually_run)*100}")"
    fi
    echo "Overall success rate: $(awk "BEGIN {printf \"%.2f%%\", (($successful+$skipped)/$total_experiments)*100}")"
fi

echo ""
echo "Detailed error log: $ERROR_LOG"
