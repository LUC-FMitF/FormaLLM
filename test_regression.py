#!/usr/bin/env python3
"""
Regression Test Suite for FormaLLM
-----------------------------------
Compares evaluation results against a baseline to detect regressions.

Usage:
    python test_regression.py [--baseline BASELINE_CSV] [--current CURRENT_CSV]
    
If not specified, uses the default paths for the current model output.

Author: FormaLLM Team
License: MIT
"""

import argparse
import csv
import sys
from pathlib import Path
from typing import Dict, Tuple
import os


class RegressionResult:
    """Results from a regression comparison."""
    def __init__(self):
        self.regressions = []  # Tests that passed in baseline but fail now
        self.improvements = []  # Tests that failed in baseline but pass now
        self.unchanged_pass = []  # Tests that pass in both
        self.unchanged_fail = []  # Tests that fail in both
        self.new_tests = []  # Tests in current but not in baseline
        self.removed_tests = []  # Tests in baseline but not in current


def load_results(csv_path: Path) -> Dict[str, str]:
    """Load evaluation results from a CSV file."""
    results = {}
    if not csv_path.exists():
        print(f"Warning: Results file not found: {csv_path}")
        return results
    
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            results[row['Model']] = row['Result']
    
    return results


def compare_results(baseline: Dict[str, str], current: Dict[str, str]) -> RegressionResult:
    """Compare two sets of evaluation results."""
    result = RegressionResult()
    
    all_models = set(baseline.keys()) | set(current.keys())
    
    for model in sorted(all_models):
        baseline_status = baseline.get(model)
        current_status = current.get(model)
        
        if baseline_status is None:
            result.new_tests.append((model, current_status))
        elif current_status is None:
            result.removed_tests.append((model, baseline_status))
        elif baseline_status == current_status:
            if current_status == "PASS":
                result.unchanged_pass.append(model)
            else:
                result.unchanged_fail.append(model)
        elif baseline_status == "PASS" and current_status != "PASS":
            result.regressions.append((model, baseline_status, current_status))
        elif baseline_status != "PASS" and current_status == "PASS":
            result.improvements.append((model, baseline_status, current_status))
        else:
            # Status changed but neither was PASS (e.g., FAIL -> ERROR)
            result.unchanged_fail.append(model)
    
    return result


def print_results(result: RegressionResult, verbose: bool = False) -> Tuple[int, int]:
    """Print regression results. Returns (pass_count, total_count)."""
    
    print("\n" + "=" * 70)
    print("REGRESSION TEST RESULTS")
    print("=" * 70)
    
    # Print regressions (most important)
    if result.regressions:
        print(f"\n❌ REGRESSIONS ({len(result.regressions)}):")
        for model, old, new in result.regressions:
            print(f"   {model}: {old} → {new}")
    else:
        print("\n✅ NO REGRESSIONS")
    
    # Print improvements
    if result.improvements:
        print(f"\n🎉 IMPROVEMENTS ({len(result.improvements)}):")
        for model, old, new in result.improvements:
            print(f"   {model}: {old} → {new}")
    
    # Print new tests
    if result.new_tests:
        print(f"\n➕ NEW TESTS ({len(result.new_tests)}):")
        for model, status in result.new_tests:
            print(f"   {model}: {status}")
    
    # Print removed tests
    if result.removed_tests:
        print(f"\n➖ REMOVED TESTS ({len(result.removed_tests)}):")
        for model, status in result.removed_tests:
            print(f"   {model}: was {status}")
    
    # Summary
    total_current = len(result.unchanged_pass) + len(result.unchanged_fail) + len(result.improvements) + len(result.regressions)
    pass_count = len(result.unchanged_pass) + len(result.improvements)
    
    print(f"\n" + "-" * 70)
    print(f"SUMMARY:")
    print(f"  Total tests: {total_current}")
    print(f"  Passing: {pass_count} ({100*pass_count/total_current:.1f}% if total_current > 0 else 0)" if total_current > 0 else "  Passing: 0")
    print(f"  Failing: {total_current - pass_count}")
    print(f"  Regressions: {len(result.regressions)}")
    print(f"  Improvements: {len(result.improvements)}")
    print("-" * 70)
    
    if verbose:
        if result.unchanged_pass:
            print(f"\n✓ UNCHANGED PASSING ({len(result.unchanged_pass)}):")
            for model in result.unchanged_pass:
                print(f"   {model}")
        
        if result.unchanged_fail:
            print(f"\n✗ UNCHANGED FAILING ({len(result.unchanged_fail)}):")
            for model in result.unchanged_fail:
                print(f"   {model}")
    
    return pass_count, total_current


def main():
    parser = argparse.ArgumentParser(
        description="Compare evaluation results to detect regressions"
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        help="Path to baseline evaluation_results.csv (default: saved baseline)"
    )
    parser.add_argument(
        "--current",
        type=Path,
        help="Path to current evaluation_results.csv (default: latest model output)"
    )
    parser.add_argument(
        "--save-baseline",
        action="store_true",
        help="Save the current results as the new baseline"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show all test results, not just changes"
    )
    args = parser.parse_args()
    
    # Determine paths
    project_root = Path(__file__).parent
    
    # Get model info from environment or use default
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1:latest")
    model_dir = project_root / "outputs" / f"{backend}_{model}"
    
    baseline_path = args.baseline or (project_root / "outputs" / "baseline_results.csv")
    current_path = args.current or (model_dir / "evaluations" / "evaluation_results.csv")
    
    print(f"Baseline: {baseline_path}")
    print(f"Current:  {current_path}")
    
    # Load results
    baseline_results = load_results(baseline_path)
    current_results = load_results(current_path)
    
    if not current_results:
        print("\n❌ ERROR: No current results found. Run the pipeline first.")
        return 1
    
    # If no baseline exists yet, offer to create one
    if not baseline_results:
        if args.save_baseline:
            print("\n📝 Creating initial baseline...")
            baseline_path.parent.mkdir(parents=True, exist_ok=True)
            import shutil
            shutil.copy(current_path, baseline_path)
            print(f"✅ Baseline saved to {baseline_path}")
            print(f"   Models: {len(current_results)}")
            pass_count = sum(1 for status in current_results.values() if status == "PASS")
            print(f"   Passing: {pass_count}/{len(current_results)}")
            return 0
        else:
            print("\n⚠️  No baseline found. Run with --save-baseline to create one.")
            print(f"\nCurrent results ({len(current_results)} models):")
            pass_count = sum(1 for status in current_results.values() if status == "PASS")
            print(f"  Passing: {pass_count}/{len(current_results)}")
            return 1
    
    # Compare results
    comparison = compare_results(baseline_results, current_results)
    pass_count, total_count = print_results(comparison, verbose=args.verbose)
    
    # Optionally save new baseline
    if args.save_baseline:
        print(f"\n📝 Updating baseline...")
        baseline_path.parent.mkdir(parents=True, exist_ok=True)
        import shutil
        shutil.copy(current_path, baseline_path)
        print(f"✅ Baseline saved to {baseline_path}")
    
    # Exit with error if there are regressions
    if comparison.regressions:
        print("\n❌ REGRESSION TEST FAILED: Found regressions")
        return 1
    
    print("\n✅ REGRESSION TEST PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
