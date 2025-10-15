import argparse
import os
from pathlib import Path
from dotenv import load_dotenv
from pipelines.tla_pipeline import tla_pipeline

# Load environment variables from .env file
env_path = Path(__file__).parent / ".env"
if env_path.exists():
    load_dotenv(env_path)
    print(f"Loaded environment from: {env_path}")
else:
    print("Warning: .env file not found. Using defaults or command-line arguments.")

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
    
    # Verify API key is configured for cloud providers
    if args.backend == "openai":
        api_key = os.getenv("OPENAI_API_KEY", "")
        if not api_key or api_key == "your-openai-key-here":
            print("\nError: OpenAI API key not configured.")
            print("Run './run.sh --setup' to configure your API key.")
            exit(1)
    elif args.backend == "anthropic":
        api_key = os.getenv("ANTHROPIC_API_KEY", "")
        if not api_key or api_key == "your-anthropic-key-here":
            print("\nError: Anthropic API key not configured.")
            print("Run './run.sh --setup' to configure your API key.")
            exit(1)

    run = tla_pipeline()
    print(f"Pipeline run ID: {run.id}")