"""
===============================================================================
TLA+ Model Synthesis from Comments via Few-Shot Prompting
===============================================================================
This script sets up a pipeline for training and evaluating an LLM (via LangChain)
to generate TLA+ specifications from structured comments using few-shot learning.

It loads training examples from train.json and performs inference on one or more
models from val.json. The test set is not used in this script and should be
reserved for final evaluation.

Author: Brian Ortiz
License: MIT
===============================================================================
"""

import json
import os
import warnings
import time
from pathlib import Path
from dotenv import load_dotenv
import mlflow
from langchain_core.prompts import PromptTemplate
from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic
from langchain_ollama import ChatOllama
from zenml import step

# Load environment variables from .env file (critical for ZenML step execution)
project_root_mlflow = Path(__file__).resolve().parent.parent
env_path = project_root_mlflow / ".env"
if env_path.exists():
    load_dotenv(env_path, override=True)


@step(enable_cache=False)
def prompt_llm() -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    split_dir = project_root / "outputs"

    train_path = split_dir / "train.json"
    val_path = split_dir / "val.json"
    NUM_FEW_SHOTS = int(os.getenv("NUM_FEW_SHOTS", "3"))

    def load_json_data(path):
        with open(path) as f:
            return json.load(f)["data"]

    def get_module_base_name(model_meta: dict) -> str:
        fname = model_meta.get("comments_clean")
        if fname:
            try:
                return Path(fname).stem.replace("_comments_clean", "")
            except Exception:
                warnings.warn(f"Could not parse name from comments_clean: {fname}. Falling back to model.")
        return model_meta.get("model", "UnnamedModel")

    def load_text(model_meta: dict, field: str) -> str:
        model_name = model_meta.get("model", "UNKNOWN")
        filename = model_meta.get(field)
        if not filename:
            warnings.warn(f"[{model_name}] Field '{field}' missing.")
            return ""
        ext = Path(filename).suffix
        subfolder = {".txt": "txt", ".tla": "tla", ".cfg": "cfg"}.get(ext, "")
        model_dir = data_dir / model_name
        expected_path = model_dir / subfolder / filename if subfolder else model_dir / filename
        if expected_path.exists():
            return expected_path.read_text().strip()
        for search_dir in [model_dir, data_dir]:
            fallback = list(search_dir.rglob(filename))
            if fallback:
                warnings.warn(f"[{model_name}] Using fallback: {fallback[0]}")
                return fallback[0].read_text().strip()
        warnings.warn(f"[{model_name}] File '{filename}' not found.")
        return ""

    def build_few_shot_prompt(examples: list[dict]) -> str:
        parts = []
        for ex in examples:
            full_tla = load_text(ex, "tla_original")
            if full_tla:
                parts.append(f"# Full TLA+ Specification:\n{full_tla}")
        return "\n".join(parts)

    instruction_header = (
        "You are a helpful assistant trained to write valid TLA+ specifications.\n"
        "Below are several complete and valid TLA+ specifications.\n"
        "At the end, you will be given only a set of user-written comments, "
        "and the target model's .cfg file if available.\n"
        "Your task is to generate a valid TLA+ specification based on those comments "
        "AND its corresponding TLC configuration if none is provided.\n"
        "Use the examples as inspiration for structure and style.\n"
        "Format your answer as a valid TLA+ module, and .cfg if one is not provided like this:\n"
        "---- MODULE MySpec ----\n... your spec ...\n====\n\n# TLC Configuration:\n... config lines ...\n-----END CFG-----\n"
    )

    # Get LLM backend configuration from environment variables
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")
    
    # Create model-specific output directory
    model_output_dir = project_root / "outputs" / f"{backend}_{model}"
    generated_dir = model_output_dir / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)
    
    # Setup model-specific MLflow tracking
    mlflow_dir = model_output_dir / "mlruns"
    mlflow_dir.mkdir(parents=True, exist_ok=True)
    mlflow.set_tracking_uri(f"file://{mlflow_dir}")
    mlflow.set_experiment(f"tla_prompt_{backend}_{model}")
    mlflow.langchain.autolog()
    
    print(f"Initializing LLM: {backend} with model {model}")
    print(f"Output directory: {model_output_dir}")
    print(f"MLflow tracking: {mlflow_dir}")

    # Initialize the appropriate LLM based on backend choice with error handling
    try:
        if backend == "openai":
            api_key = os.getenv("OPENAI_API_KEY")
            if not api_key or api_key == "your-openai-key-here":
                raise ValueError("OpenAI API key not configured. Please set OPENAI_API_KEY environment variable.")
            llm = ChatOpenAI(temperature=0, model=model, api_key=api_key)
            
        elif backend == "anthropic":
            api_key = os.getenv("ANTHROPIC_API_KEY") 
            if not api_key or api_key == "your-anthropic-key-here":
                raise ValueError("Anthropic API key not configured. Please set ANTHROPIC_API_KEY environment variable.")
            llm = ChatAnthropic(temperature=0, model=model, api_key=api_key)
            
        elif backend == "ollama":
            base_url = os.getenv("OLLAMA_BASE_URL", "http://localhost:11434")
            llm = ChatOllama(
                temperature=0, 
                model=model,
                base_url=base_url
            )
            print(f"Ollama endpoint: {base_url}")
            
        else:
            raise ValueError(f"Unsupported LLM backend: {backend}. Supported backends: openai, anthropic, ollama")
            
    except Exception as e:
        print(f"Error initializing {backend} LLM: {str(e)}")
        print("Tip: Run './run.sh --setup' to configure your LLM backend")
        raise

    print(f"Successfully initialized {backend} LLM with model {model}")
    prompt = PromptTemplate.from_template("{input}")
    chain = prompt | llm
    train_data = load_json_data(train_path)
    val_data = load_json_data(val_path)
    results = {}

    for i, target_model in enumerate(val_data):
        module_name = get_module_base_name(target_model)
        few_shot_examples = train_data[:NUM_FEW_SHOTS]
        few_shot_prompt = build_few_shot_prompt(few_shot_examples)
        target_comments = load_text(target_model, "comments_clean")
        target_cfg = load_text(target_model, "cfg")
        cfg_prompt = f"\n\n# TLC Configuration:\n{target_cfg}" if target_cfg else "\n\n# No configuration file provided."

        if not target_comments:
            warnings.warn(f"Skipping model {target_model.get('model', 'UNKNOWN')} due to missing comments.")
            continue

        final_prompt = (
            instruction_header
            + "\n\n"
            + few_shot_prompt
            + cfg_prompt
            + f"\n\n# Comments:\n{target_comments}\n\n"
            + f"# TLA+ Specification:\n---- MODULE {module_name} ----\n"
        )

        print(f"\n--- Generating spec for module: {module_name} ---")
        response = chain.invoke({"input": final_prompt})

        if "# TLC Configuration:" in response:
            tla_part, cfg_part = response.split("# TLC Configuration:", 1)
            cfg_part = cfg_part.replace("-----END CFG-----", "").strip()
        else:
            tla_part = response
            cfg_part = ""

        if hasattr(tla_part, "content"): 
            tla_body = tla_part.content.strip()
        else:
            tla_body = str(tla_part).strip()

        if not tla_body.startswith("---- MODULE"):
            tla_body = f"---- MODULE {module_name} ----\n" + tla_body
        if not tla_body.rstrip().endswith("===="):
            tla_body = tla_body.rstrip() + "\n===="


        output_tla_path = generated_dir / f"{module_name}.tla"
        output_cfg_path = generated_dir / f"{module_name}.cfg"
        output_tla_path.write_text(tla_body)
        output_cfg_path.write_text(cfg_part)

        results[module_name] = tla_body
        time.sleep(10)

    return results