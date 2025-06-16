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
from pathlib import Path
from langchain.prompts import PromptTemplate
from langchain.chains.llm import LLMChain
from langchain_openai import ChatOpenAI
#from langchain_ollama.llms import OllamaLLM
from zenml import step


@step
def prompt_llm() -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    split_dir = project_root / "outputs"

    train_path = split_dir / "train.json"
    val_path = split_dir / "val.json"

    NUM_FEW_SHOTS = 3
    TARGET_MODEL_INDEX = 4

    def load_json_data(path):
        with open(path) as f:
            return json.load(f)["data"]

    train_data = load_json_data(train_path)
    val_data = load_json_data(val_path)
    target_model = val_data[TARGET_MODEL_INDEX]
    few_shot_examples = train_data[:NUM_FEW_SHOTS]

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
            parts.append(f"# Full TLA+ Specification:\n{full_tla}")
        return "\n".join(parts)
    
    # Instruction header to give context to the LLM
    instruction_header = (
        "You are a helpful assistant trained to write valid TLA+ specifications.\n"
        "Below are several complete and valid TLA+ specifications.\n"
        "At the end, you will be given only a set of user-written comments.\n"
        "Your task is to generate a valid TLA+ specification based on those comments.\n"
        "Use the examples as inspiration for structure and style.\n"
        "Format your answer as a valid TLA+ module.\n"
    )

    few_shot_prompt = build_few_shot_prompt(few_shot_examples)
    target_comments = load_text(target_model, "comments_clean")

    final_prompt = (
        instruction_header
        + few_shot_prompt
        + f"\n\n# Comments:\n{target_comments}\n\n# TLA+ Specification:\n"
    )

    llm = ChatOpenAI(temperature=0, model="gpt-4")
    #llm = OllamaLLM(model="llama3", temperature=0)
    chain = LLMChain(llm=llm, prompt=PromptTemplate.from_template("{input}"))
    response = chain.run(input=final_prompt)

    generated_dir = project_root / "outputs" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)
    output_path = generated_dir / f"{target_model['model']}.generated.tla"
    output_path.write_text(response.strip())

    return {target_model['model']: response.strip()}