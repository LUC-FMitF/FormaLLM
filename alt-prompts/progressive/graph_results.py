import pandas as pd
import matplotlib.pyplot as plt
from pathlib import Path
from zenml import step

@step(enable_cache=True)
def graph_results() -> None:
    import os
    project_root = Path(__file__).resolve().parent.parent
    
    # Get model info from environment
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    model_output_dir = project_root / "outputs" / f"{backend}_{model}"
    
    results_path = model_output_dir / "evaluations" / "evaluation_results.csv"
    if not results_path.exists():
        print(f"Evaluation results file not found at: {results_path}")
        return

    df = pd.read_csv(results_path)

    # Print summary table
    print("\nEvaluation Summary:")
    print(df.value_counts("Result").rename_axis("Result").reset_index(name="Count"))

    # Save summary CSV
    summary_path = results_path.with_name("evaluation_summary.csv")
    df.value_counts("Result").rename_axis("Result").reset_index(name="Count").to_csv(summary_path, index=False)

    # Generate and save bar chart
    plt.figure()
    df["Result"].value_counts().plot(kind="bar")
    plt.title("TLA+ Specification Validation Results")
    plt.xlabel("Outcome")
    plt.ylabel("Number of Models")
    plt.xticks(rotation=0)
    plt.tight_layout()

    plot_path = results_path.with_name("evaluation_summary.png")
    plt.savefig(plot_path)
    print(f"\nSaved summary to {plot_path}")