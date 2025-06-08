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


# --- OpenAI API ---
llm = ChatOpenAI(
    temperature=0,
    model="gpt-4",
    openai_api_key=os.environ.get("OPENAI_API_KEY") 
)

# --- Path setup ---
project_root = Path(__file__).resolve().parent.parent
data_dir = project_root / "data"
split_dir = project_root / "outputs"

train_path = split_dir / "train.json"
val_path = split_dir / "val.json"

# --- Parameters ---
NUM_FEW_SHOTS = 3         # Number of examples to include in prompt
TARGET_MODEL_INDEX = 0    # Index of validation set model to use for inference

# --- Load data ---
def load_json_data(path):
    with open(path) as f:
        return json.load(f)["data"]

train_data = load_json_data(train_path)
val_data = load_json_data(val_path)
target_model = val_data[TARGET_MODEL_INDEX]
few_shot_examples = train_data[:NUM_FEW_SHOTS]

# --- Helpers ---
def load_text(model_meta: dict, field: str) -> str:
    """
    Load a text file given a field in the model metadata, using subfolder heuristics
    and fallback searching if needed.
    """
    model_dir = data_dir / model_meta["model"]
    filename = model_meta.get(field)

    if not filename:
        warnings.warn(f"[{model_meta['model']}] Field '{field}' missing.")
        return ""

    # Determine subfolder by extension
    ext = Path(filename).suffix
    subfolder = {
        ".txt": "txt",
        ".tla": "tla",
        ".cfg": "cfg"
    }.get(ext, "")

    expected_path = model_dir / subfolder / filename if subfolder else model_dir / filename

    if expected_path.exists():
        return expected_path.read_text().strip()

    # Fallback: search recursively in model folder
    fallback_matches = list(model_dir.rglob(filename))
    if fallback_matches:
        return fallback_matches[0].read_text().strip()

    # Log warning and continue
    warnings.warn(f"[{model_meta['model']}] File '{filename}' not found in expected or fallback locations.")
    return ""

def build_few_shot_prompt(examples: list[dict]) -> str:
    """Construct a few-shot prompt with example comments and specs."""
    prompt_parts = []
    for ex in examples:
        comments = load_text(ex, "comments_clean")
        tla = load_text(ex, "tla_clean").replace("----", "--")
        prompt_parts.append(f"""# Comments:
{comments}

# TLA+ Specification:
{tla}
""")
    return "\n".join(prompt_parts)

# --- Build final prompt ---
few_shot_prompt = build_few_shot_prompt(few_shot_examples)
target_comments = load_text(target_model, "comments_clean")

final_prompt = f"""{few_shot_prompt}
# Comments:
{target_comments}

# TLA+ Specification:
"""

# --- Run LangChain LLM ---
llm = ChatOpenAI(temperature=0, model="gpt-4")  # Change model as needed
prompt = PromptTemplate.from_template("{input}")
chain = LLMChain(llm=llm, prompt=prompt)

# --- Inference ---
response = chain.run(input=final_prompt)

# --- Output ---
print("=== Synthesized TLA+ Specification ===\n")
print(response)
