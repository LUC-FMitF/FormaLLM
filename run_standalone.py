#!/usr/bin/env python3
"""
Standalone TLA+ generation script - no ZenML dependencies
This allows testing LLM backends without ZenML orchestration issues
"""
import json
import os
import warnings
import time
import argparse
from pathlib import Path
from langchain.prompts import PromptTemplate
from langchain.chains.llm import LLMChain
from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic
from langchain_ollama import ChatOllama

# Suppress warnings for cleaner output
warnings.filterwarnings('ignore')


def generate_tla_specs(backend="ollama", model="llama3.1"):
    """Run the TLA+ generation without ZenML orchestration"""

    project_root = Path(__file__).resolve().parent
    data_dir = project_root / "data"
    split_dir = project_root / "outputs"
    generated_dir = project_root / "outputs" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)

    train_path = split_dir / "train.json"
    val_path = split_dir / "val.json"
    NUM_FEW_SHOTS = 3

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

    # Initialize the appropriate LLM based on backend choice
    if backend == "openai":
        llm = ChatOpenAI(temperature=0, model=model)
    elif backend == "anthropic":
        llm = ChatAnthropic(temperature=0, model=model)
    elif backend == "ollama":
        llm = ChatOllama(temperature=0, model=model)
    else:
        raise ValueError(f"Unsupported LLM backend: {backend}")

    print(f"[OK] Initialized {backend} with model {model}")
    chain = LLMChain(llm=llm, prompt=PromptTemplate.from_template("{input}"))

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

        print(f"\n--- Generating spec for module: {module_name} ({i+1}/{len(val_data)}) ---")
        response = chain.run(input=final_prompt).strip()

        if "# TLC Configuration:" in response:
            tla_part, cfg_part = response.split("# TLC Configuration:", 1)
            cfg_part = cfg_part.replace("-----END CFG-----", "").strip()
        else:
            tla_part = response
            cfg_part = ""

        # Ensure proper module syntax
        tla_body = tla_part.strip()
        if not tla_body.startswith("---- MODULE"):
            tla_body = f"---- MODULE {module_name} ----\n" + tla_body
        if not tla_body.rstrip().endswith("===="):
            tla_body = tla_body.rstrip() + "\n===="

        output_tla_path = generated_dir / f"{module_name}.tla"
        output_cfg_path = generated_dir / f"{module_name}.cfg"
        output_tla_path.write_text(tla_body)
        output_cfg_path.write_text(cfg_part)

        print(f"  [OK] Saved: {output_tla_path}")
        results[module_name] = tla_body
        time.sleep(10)

    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Standalone TLA+ generation with configurable LLM backend")
    parser.add_argument("--backend", type=str, default=os.getenv("LLM_BACKEND", "ollama"),
                        choices=["openai", "anthropic", "ollama"],
                        help="LLM backend to use (default: ollama)")
    parser.add_argument("--model", type=str, default=os.getenv("LLM_MODEL", "llama3.1"),
                        help="Model name to use (default: llama3.1)")

    args = parser.parse_args()

    print("=" * 70)
    print(" Standalone TLA+ Generation (No ZenML orchestration)")
    print("=" * 70)
    print(f" LLM Backend: {args.backend}")
    print(f" Model: {args.model}")
    print("=" * 70)
    print()

    try:
        results = generate_tla_specs(backend=args.backend, model=args.model)
        print()
        print("=" * 70)
        print(f" [SUCCESS] Generation completed successfully!")
        print(f"   Generated {len(results)} specifications")
        print("=" * 70)
    except Exception as e:
        print(f"\n[ERROR] {e}")
        import traceback
        traceback.print_exc()
        exit(1)
