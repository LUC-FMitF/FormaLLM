#!/usr/bin/env python3
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
import mlflow
from langchain.prompts import PromptTemplate
from langchain.chains.llm import LLMChain
from langchain_openai import ChatOpenAI
#from langchain_ollama.llms import OllamaLLM
from zenml import step

# Explicitly point MLflow to the ZenML tracking directory
mlflow.set_tracking_uri("file:///workspaces/FormaLLM/mlruns")

# Create or switch to a named experiment
mlflow.set_experiment("tla_prompt_generation")

# Enable automatic trace logging for LangChain
mlflow.langchain.autolog()

@step
def prompt_llm() -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    split_dir = project_root / "outputs"

    train_path = split_dir / "train.json"
    val_path = split_dir / "val.json"

    NUM_FEW_SHOTS = 3

    def load_json_data(path):
        with open(path) as f:
            return json.load(f)["data"]

    train_data = load_json_data(train_path)
    val_data = load_json_data(val_path)

    def load_text(model_meta: dict, field: str) -> str:
        model_name = model_meta["model"]
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
            # comments = load_text(ex, "comments_clean")
            # tla = load_text(ex, "tla_clean").replace("----", "--")
            full_tla = load_text(ex, "tla_original")
            if full_tla:
                parts.append(f"# Full TLA+ Specification:\n{full_tla}")
        return "\n".join(parts)
    
    # Instruction header to give context to the LLM
    instruction_header = (
        "You are a helpful assistant trained to write valid TLA+ specifications.\n"
        "Below are several complete and valid TLA+ specifications.\n"
        "At the end, you will be given only a set of user-written comments, "
        "and the target model's .cfg file if available.\n"
        "Your task is to generate a valid TLA+ specification based on those comments"
        "AND its corresponding TLC configuration if none is provided .\n"
        "Use the examples as inspiration for structure and style.\n"
        "Format your answer as a valid TLA+ module, and .cfg if one is not provided like this:\n"
        "---- MODULE MySpec ----\n... your spec ...\n====\n\n# TLC Configuration:\n... config lines ...\n-----END CFG-----\n"
    )
    
    llm = ChatOpenAI(temperature=0, model="gpt-4")
    #llm = OllamaLLM(model="llama3", temperature=0)
    chain = LLMChain(llm=llm, prompt=PromptTemplate.from_template("{input}"))

    generated_dir = project_root / "outputs" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)

    results = {}

    for i, target_model in enumerate(val_data):
        few_shot_examples = train_data[:NUM_FEW_SHOTS]
        few_shot_prompt = build_few_shot_prompt(few_shot_examples)
        target_comments = load_text(target_model, "comments_clean")
        target_cfg = load_text(target_model,"cfg")
        cfg_prompt = f"\n\n# TLC Configuration:\n{target_cfg}" if target_cfg else "\n\n# No configuration file provided."

        if not target_comments:
            warnings.warn(f"Skipping model {target_model ['model']} because comments are missing")
            continue

        final_prompt = (
            instruction_header
            + "\n\n"
            + few_shot_prompt
            + cfg_prompt
            + f"\n\n Comments:\n{target_comments}\n\n TLA+ Specification:\n"
        )
        print(f"\n--- Generating spec for model: {target_model['model']} ---")
        response = chain.run(input=final_prompt).strip()

        # Split TLA and CFG from response
        if "# TLC Configuration:" in response:
            tla_part, cfg_part = response.split("# TLC Configuration:", 1)
            cfg_part = cfg_part.replace ("-----END CFG-----","").strip()
        else:
            tla_part = response
            cfg_part = ""


        output_tla_path = generated_dir / f"{target_model['model']}.generated.tla"
        output_cfg_path = generated_dir / f"{target_model['model']}.cfg"
        output_tla_path.write_text(tla_part.strip())
        output_cfg_path.write_text(cfg_part.strip())

        results[target_model["model"]] = tla_part.strip()
        time.sleep(10)

    return results
