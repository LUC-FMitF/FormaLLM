# Regression Testing Suite

## Overview

The FormaLLM regression testing suite ensures that changes to the pipeline don't introduce regressions and helps track improvements over time.

## Quick Start

### Automatic Testing (Integrated with `run.sh`)

The regression tests run automatically after each pipeline execution:

```bash
./run.sh
```

After the pipeline completes, the regression test will:
1. Compare current results against the baseline
2. Report any regressions (tests that passed before but now fail)
3. Report improvements (tests that failed before but now pass)
4. Offer to update the baseline if there are regressions

### Manual Testing

You can also run regression tests manually:

```bash
# Compare against baseline
python test_regression.py

# Show all tests, not just changes
python test_regression.py --verbose

# Update the baseline after verifying improvements
python test_regression.py --save-baseline

# Compare specific files
python test_regression.py --baseline path/to/old.csv --current path/to/new.csv
```

## Understanding Results

### Result Types

- **PASS**: The TLA+ spec was generated correctly and passed TLC validation
- **FAIL**: The spec was generated but failed TLC validation
- **ERROR**: An error occurred during TLC execution
- **SKIPPED**: The test was skipped (e.g., missing config file)

### Regression Categories

When comparing results, tests fall into these categories:

- **✅ NO REGRESSIONS**: No tests that were passing are now failing
- **❌ REGRESSIONS**: Tests that passed in baseline but fail now (THIS IS BAD!)
- **🎉 IMPROVEMENTS**: Tests that failed in baseline but pass now (THIS IS GOOD!)
- **➕ NEW TESTS**: Tests added since the baseline
- **➖ REMOVED TESTS**: Tests removed since the baseline
- **UNCHANGED**: Tests with the same result in both runs

## Workflow

### Initial Setup

1. Run the pipeline for the first time:
   ```bash
   ./run.sh
   ```

2. The script will create an initial baseline automatically

### Regular Development

1. Make changes to the pipeline (prompts, models, etc.)

2. Run the pipeline:
   ```bash
   ./run.sh
   ```

3. Review regression test results:
   - If there are **regressions**: investigate and fix
   - If there are **improvements**: celebrate and update baseline
   - If **unchanged**: your changes didn't affect correctness

4. Update baseline when you have improvements:
   ```bash
   python test_regression.py --save-baseline
   ```

### Example Workflow

```bash
# Day 1: Initial baseline
./run.sh
# Result: 0/26 tests passing, baseline created

# Day 2: Improve prompts
vim steps/prompt_step.py
./run.sh
# Result: 3/26 passing, 3 improvements detected
python test_regression.py --save-baseline  # Save the new baseline

# Day 3: Try a new model
export LLM_MODEL="llama3.2"
./run.sh
# Result: 2/26 passing, 1 regression detected
# Don't save baseline - investigate the regression first!
```

## Baseline Management

### Where is the Baseline Stored?

The baseline is stored at: `outputs/baseline_results.csv`

This file contains the "known good" state of all tests.

### When to Update the Baseline

✅ **DO update** when:
- You've made intentional improvements and verified they're correct
- New tests are added to the suite
- You've fixed bugs that caused false failures

❌ **DON'T update** when:
- There are regressions you haven't investigated
- Tests are failing due to temporary issues
- You're just experimenting

### Baseline Versioning

For important milestones, you can save versioned baselines:

```bash
# Save a milestone baseline
cp outputs/baseline_results.csv outputs/baseline_v1.0.csv

# Compare against a specific version
python test_regression.py --baseline outputs/baseline_v1.0.csv
```

## CI/CD Integration

### GitHub Actions (Example)

```yaml
name: Regression Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Run Pipeline
        run: ./run.sh
      - name: Regression Test
        run: |
          python test_regression.py
          if [ $? -ne 0 ]; then
            echo "::error::Regressions detected!"
            exit 1
          fi
```

### Pre-commit Hook

Create `.git/hooks/pre-commit`:

```bash
#!/bin/bash
# Warn if making changes without testing
if [ -f "outputs/baseline_results.csv" ]; then
    echo "Remember to run regression tests before committing!"
    echo "  ./run.sh"
    echo "  python test_regression.py"
fi
```

## Troubleshooting

### "No current results found"

Run the pipeline first:
```bash
./run.sh
```

### "No baseline found"

Create a baseline:
```bash
python test_regression.py --save-baseline
```

### All Tests Failing

This is expected initially! The LLM needs to generate valid TLA+ specs for tests to pass.

Focus on:
1. Improving prompts in `steps/prompt_step.py`
2. Adding better few-shot examples in `outputs/train.json`
3. Tuning model parameters

### False Regressions

If tests randomly pass/fail (flaky tests), this might indicate:
- Non-deterministic LLM output
- Timeouts in TLC
- Environment issues

Consider:
- Increasing temperature to 0 for more deterministic output
- Setting a random seed
- Increasing TLC timeout values

## Advanced Usage

### Comparing Different Models

```bash
# Test model A
export LLM_MODEL="llama3.1"
./run.sh
python test_regression.py --save-baseline

# Test model B
export LLM_MODEL="llama3.2"
./run.sh
python test_regression.py  # Compare against model A
```

### Custom Baselines per Model

```bash
# Create model-specific baselines
python test_regression.py --baseline outputs/baseline_llama3.1.csv --save-baseline
python test_regression.py --baseline outputs/baseline_llama3.2.csv --save-baseline
```

### Generating Reports

```bash
# Save verbose output to a file
python test_regression.py --verbose > regression_report.txt

# Compare and email results (example)
python test_regression.py --verbose | mail -s "Regression Report" team@example.com
```

## Metrics to Track

As you improve the pipeline, track these metrics over time:

1. **Pass Rate**: `passing_tests / total_tests`
2. **Improvement Rate**: `improvements_per_change`
3. **Regression Rate**: `regressions_per_change` (should be 0!)
4. **Coverage**: Number of TLA+ patterns successfully generated

Example tracking:

| Date | Passing | Total | Pass Rate | Notes |
|------|---------|-------|-----------|-------|
| 2025-10-27 | 0 | 26 | 0% | Initial baseline |
| 2025-10-28 | 3 | 26 | 11.5% | Improved prompts |
| 2025-10-29 | 8 | 26 | 30.8% | Added few-shot examples |

## Future Enhancements

Potential improvements to the regression suite:

- [ ] Track performance metrics (generation time, TLC runtime)
- [ ] Compare spec similarity (not just PASS/FAIL)
- [ ] Generate diff reports between generated specs
- [ ] Integration with MLflow for metric tracking
- [ ] Automated issue creation for regressions
- [ ] Bisection to find regression-introducing commits

## Questions?

See the main README or open an issue!
