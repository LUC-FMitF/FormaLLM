#!/usr/bin/env python3
"""
Demo script to show how regression testing works.
Creates example scenarios with passing/failing tests.
"""

import csv
from pathlib import Path
import subprocess
import sys

def create_scenario(name: str, results: dict):
    """Create a test scenario with given results."""
    csv_path = Path(f"demo_{name}.csv")
    with open(csv_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(["Model", "Result"])
        for model, result in results.items():
            writer.writerow([model, result])
    return csv_path

def run_regression_test(baseline, current):
    """Run regression test and return output."""
    result = subprocess.run(
        ["python", "test_regression.py", "--baseline", str(baseline), "--current", str(current)],
        capture_output=True,
        text=True
    )
    return result.stdout, result.returncode

def demo_scenario_1():
    """Demo: Initial state vs First improvement."""
    print("\n" + "="*70)
    print("SCENARIO 1: First Improvements")
    print("="*70)
    print("\nInitial state: All tests failing")
    print("After improvement: 3 tests now passing")
    print()
    
    baseline = create_scenario("baseline_v0", {
        "TwoPhase": "FAIL",
        "Paxos": "FAIL",
        "DieHard": "FAIL",
        "Hanoi": "FAIL",
        "Majority": "FAIL",
    })
    
    current = create_scenario("current_v1", {
        "TwoPhase": "PASS",  # ✅ Improvement!
        "Paxos": "FAIL",
        "DieHard": "PASS",   # ✅ Improvement!
        "Hanoi": "PASS",     # ✅ Improvement!
        "Majority": "FAIL",
    })
    
    output, returncode = run_regression_test(baseline, current)
    print(output)
    
    # Cleanup
    baseline.unlink()
    current.unlink()
    
    return returncode == 0

def demo_scenario_2():
    """Demo: Regression detected."""
    print("\n" + "="*70)
    print("SCENARIO 2: Regression Detected")
    print("="*70)
    print("\nBaseline: 3 tests passing")
    print("Current: Only 2 tests passing (1 regression!)")
    print()
    
    baseline = create_scenario("baseline_v1", {
        "TwoPhase": "PASS",
        "Paxos": "FAIL",
        "DieHard": "PASS",
        "Hanoi": "PASS",
        "Majority": "FAIL",
    })
    
    current = create_scenario("current_v2", {
        "TwoPhase": "PASS",
        "Paxos": "FAIL",
        "DieHard": "FAIL",   # ❌ Regression!
        "Hanoi": "PASS",
        "Majority": "FAIL",
    })
    
    output, returncode = run_regression_test(baseline, current)
    print(output)
    
    # Cleanup
    baseline.unlink()
    current.unlink()
    
    return returncode == 1  # Should fail due to regression

def demo_scenario_3():
    """Demo: New tests added."""
    print("\n" + "="*70)
    print("SCENARIO 3: New Tests Added")
    print("="*70)
    print("\nBaseline: 5 tests")
    print("Current: 7 tests (2 new tests added)")
    print()
    
    baseline = create_scenario("baseline_v2", {
        "TwoPhase": "PASS",
        "Paxos": "FAIL",
        "DieHard": "PASS",
        "Hanoi": "PASS",
        "Majority": "FAIL",
    })
    
    current = create_scenario("current_v3", {
        "TwoPhase": "PASS",
        "Paxos": "PASS",     # ✅ Improvement!
        "DieHard": "PASS",
        "Hanoi": "PASS",
        "Majority": "FAIL",
        "Consensus": "PASS",  # ➕ New test (passing!)
        "YoYo": "FAIL",       # ➕ New test (failing)
    })
    
    output, returncode = run_regression_test(baseline, current)
    print(output)
    
    # Cleanup
    baseline.unlink()
    current.unlink()
    
    return returncode == 0

def main():
    print("\n" + "="*70)
    print("REGRESSION TESTING DEMO")
    print("="*70)
    print("\nThis demo shows how the regression testing system works.")
    print("It creates example scenarios to demonstrate different situations.")
    
    # Run scenarios
    scenarios = [
        ("First Improvements", demo_scenario_1),
        ("Regression Detection", demo_scenario_2),
        ("New Tests Added", demo_scenario_3),
    ]
    
    results = []
    for name, scenario_func in scenarios:
        try:
            success = scenario_func()
            results.append((name, "✅ PASS" if success else "❌ FAIL"))
        except Exception as e:
            print(f"\n❌ Error in scenario '{name}': {e}")
            results.append((name, f"❌ ERROR: {e}"))
    
    # Summary
    print("\n" + "="*70)
    print("DEMO SUMMARY")
    print("="*70)
    for name, result in results:
        print(f"{result}: {name}")
    
    print("\n" + "="*70)
    print("Demo complete! The regression testing system is ready to use.")
    print("="*70)
    print("\nNext steps:")
    print("  1. Run your pipeline: ./run.sh")
    print("  2. Make improvements to prompts/models")
    print("  3. Run pipeline again")
    print("  4. Review regression test results")
    print("  5. Update baseline: python test_regression.py --save-baseline")
    print()

if __name__ == "__main__":
    main()
