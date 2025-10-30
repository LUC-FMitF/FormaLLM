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
import re
from pathlib import Path
from dotenv import load_dotenv
import mlflow
from langchain_core.prompts import PromptTemplate
from langchain_core.messages import HumanMessage, AIMessage, SystemMessage
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

    def clean_llm_response(response_text: str, module_name: str) -> str:
        if "```" in response_text:
            code_blocks = re.findall(r'```(?:tla|tlaplus)?\n(.*?)\n```', response_text, re.DOTALL)
            if code_blocks:
                response_text = code_blocks[0]
            else:
                response_text = response_text.replace("```tla", "").replace("```", "")
        explanatory_phrases = [
            r'^Here is .*?:[\s\n]*',
            r'^Here\'s .*?:[\s\n]*',
            r'^This is .*?:[\s\n]*',
            r'^Below is .*?:[\s\n]*',
            r'^I\'ve created .*?:[\s\n]*',
            r'^The following .*?:[\s\n]*',
        ]
        for phrase in explanatory_phrases:
            response_text = re.sub(phrase, '', response_text, flags=re.IGNORECASE | re.MULTILINE)
        if "---- MODULE" in response_text:
            module_start = response_text.find("---- MODULE")
            response_text = response_text[module_start:]
        module_match = re.search(r'---- MODULE (\w+) ----', response_text)
        if module_match:
            llm_module_name = module_match.group(1)
            if llm_module_name != module_name:
                response_text = response_text.replace(
                    f"---- MODULE {llm_module_name} ----",
                    f"---- MODULE {module_name} ----",
                    1
                )
                response_text = re.sub(
                    r'-+ MODULE ' + re.escape(llm_module_name) + r' -+',
                    '',
                    response_text
                )
        lines = response_text.split('\n')
        cleaned_lines = []
        seen_module_header = False
        for line in lines:
            if re.match(r'^-+\s*MODULE\s+\w+\s+-+$', line):
                if not seen_module_header:
                    cleaned_lines.append(line)
                    seen_module_header = True
            else:
                cleaned_lines.append(line)
        response_text = '\n'.join(cleaned_lines)
        return response_text.strip()
            
    def build_few_shot_messages(examples: list[dict]) -> list:
        messages = []
        for ex in examples:
            comments = load_text(ex, "comments_clean")
            full_tla = load_text(ex, "tla_original")
            cfg = load_text(ex, "cfg")
            module_name = get_module_base_name(ex)
            if not comments or not full_tla:
                continue
            # Compose the user message (comments + optional cfg)
            user_msg = f"# Comments:\n{comments}"
            if cfg:
                user_msg += f"\n\n# TLC Configuration:\n{cfg}"
            # Compose the assistant message (TLA+ spec)
            ai_msg = f"---- MODULE {module_name} ----\n{full_tla}\n===="
            messages.append(HumanMessage(content=user_msg))
            messages.append(AIMessage(content=ai_msg))
        return messages

    system_message = SystemMessage(
        content="""You are a TLA+ code generator.

You must output ONLY valid TLA+ code that can be parsed by the TLA+ Toolbox.
You must NEVER include markdown fences (```) or explanations.
You must NEVER include reasoning text, English descriptions, or comments.
You must NEVER output placeholders like <ModuleName> or <constant> literally.

Strict formatting rules:
1. Output ONLY the complete TLA+ module.
2. The module must start with exactly this line:
   ---- MODULE ModuleName ----
3. The module must end with exactly this line:
   ====
4. Include only valid TLA+ constructs: EXTENDS, CONSTANTS, VARIABLES, Init, Next, Spec.
5. Always define every symbol before using it.
6. After the module, include a TLC configuration section in the exact format shown below.
7. No blank sections, no undefined names, no ellipses, no placeholders.

## TLA+ Syntax Hints
- A formula [A]_v is called a temporal formula, and is shorthand for the formula A \/ v' = v.  In other words, the formula is true if A is true or if the value of v remains unchanged.  Usually, v is a tuple of the spec's variables.
- The symbol \`#\` is alternative syntax used for inequality in TLA+; the other symbol is \`/=\".

## TLA+ Convention Hints
- The type correctness invariant is typically called TypeOK.
- Users can employ TLA labels as a means to conceptually associate a comment with a sub-formula like a specific disjunct or conjunct of a TLA formula. Even though these labels have no other function, they facilitate referencing particular parts of the formula from a comment.

Required structure (copy exactly; replace bracketed parts with concrete TLA+ code):

---- MODULE ModuleName ----
EXTENDS <standard modules>
CONSTANTS <constants>
VARIABLES <variables>

Init == <initial state predicate>
Next == <next-state relation>
Spec == Init /\ [][Next]_<<variables>>

====
# TLC Configuration:
CONSTANTS
  <constant> = <value>
SPECIFICATION Spec
INVARIANTS <invariant names>
"""
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
    prompt = None  # will be built per target
    train_data = load_json_data(train_path)
    val_data = load_json_data(val_path)
    results = {}

    for i, target_model in enumerate(val_data):
        module_name = get_module_base_name(target_model)
        few_shot_examples = train_data[:NUM_FEW_SHOTS]
        few_shot_msgs = build_few_shot_messages(few_shot_examples)
        target_comments = load_text(target_model, "comments_clean")
        target_cfg = load_text(target_model, "cfg")
        if not target_comments:
            warnings.warn(f"Skipping model {target_model.get('model', 'UNKNOWN')} due to missing comments.")
            continue
        # Compose the user message for the target
        user_msg = f"# Comments:\n{target_comments}"
        if target_cfg:
            user_msg += f"\n\n# TLC Configuration:\n{target_cfg}"
        # Build the full prompt as a list of messages
        all_messages = [system_message] + few_shot_msgs + [HumanMessage(content=user_msg)]
        print(f"\n--- Generating spec for module: {module_name} ---")
        response = llm.invoke(all_messages)

        # Handle response (string or Message)
        if hasattr(response, "content"):
            response_text = response.content.strip()
        else:
            response_text = str(response).strip()

        # Clean the LLM response
        response_text = clean_llm_response(response_text, module_name)

        if "# TLC Configuration:" in response_text:
            tla_part, cfg_part = response_text.split("# TLC Configuration:", 1)
            cfg_part = cfg_part.replace("-----END CFG-----", "").strip()
        else:
            tla_part = response_text
            cfg_part = ""

        tla_body = tla_part.strip()
        if not tla_body.startswith(f"---- MODULE"):
            tla_body = f"---- MODULE {module_name} ----\n" + tla_body
        if not tla_body.rstrip().endswith("===="):
            tla_body = tla_body.rstrip() + "\n===="

        output_tla_path = generated_dir / f"{module_name}.tla"
        output_cfg_path = generated_dir / f"{module_name}.cfg"
        output_tla_path.write_text(tla_body)
        output_cfg_path.write_text(cfg_part)

        results[module_name] = tla_body
        #time.sleep(10)

    return results