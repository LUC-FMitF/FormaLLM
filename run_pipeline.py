import argparse
import os
from pipelines.tla_pipeline import tla_pipeline

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run TLA+ pipeline with configurable LLM backend")
    parser.add_argument("--backend", type=str, default=os.getenv("LLM_BACKEND", "openai"),
                        choices=["openai", "anthropic", "ollama"],
                        help="LLM backend to use (default: openai)")
    parser.add_argument("--model", type=str, default=os.getenv("LLM_MODEL", "gpt-4"),
                        help="Model name to use (default: gpt-4)")

    args = parser.parse_args()

    # Set environment variables for the pipeline steps to access
    os.environ["LLM_BACKEND"] = args.backend
    os.environ["LLM_MODEL"] = args.model

    print("Initiating a new run for the pipeline: tla_pipeline.")
    print(f"LLM Backend: {args.backend}")
    print(f"Model: {args.model}")

    run = tla_pipeline()
    print(f"Pipeline run ID: {run.id}")