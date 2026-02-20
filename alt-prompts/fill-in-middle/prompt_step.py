
import json
import os
import warnings
import time
import re
from pathlib import Path
from dotenv import load_dotenv
import mlflow
from langchain_core.prompts import PromptTemplate
from langchain_core.messages import HumanMessage, SystemMessage
from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic
from langchain_ollama import ChatOllama
from zenml import step

project_root_mlflow = Path(__file__).resolve().parent.parent
env_path = project_root_mlflow / ".env"
if env_path.exists():
    load_dotenv(env_path, override=True)


@step(enable_cache=False)
def prompt_llm() -> dict:
    project_root = Path(__file__).resolve().parent.parent
    data_dir = project_root / "data"
    split_dir = project_root / "Input"

    val_path = split_dir / "val.json"

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

    def load_partial_code(model_meta: dict) -> dict:
        """
        Load prefix and suffix for fill-in-the-middle prompting.
        Returns a dict with:
        - 'prefix': first 30% of code
        - 'suffix': last 30% of code
        - 'middle_ground_truth': actual middle 40% (for evaluation)
        - 'full_code': complete code (for reference)
        """
        model_name = model_meta.get("model", "UNKNOWN")

        # Load the full clean TLA+ file
        full_tla = load_text(model_meta, "tla_clean")
        if not full_tla:
            return {"prefix": "", "suffix": "", "middle_ground_truth": "", "full_code": ""}

        lines = full_tla.split('\n')
        total_lines = len(lines)

        # Calculate split points for 30%-40%-30% split
        # Ensure at least 3 lines in each section
        prefix_lines = max(3, int(total_lines * 0.3))
        suffix_lines = max(3, int(total_lines * 0.3))

        # Adjust if splits would overlap (for very small files)
        if prefix_lines + suffix_lines >= total_lines:
            # For small files, split evenly
            prefix_lines = total_lines // 3
            suffix_lines = total_lines // 3

        middle_start = prefix_lines
        middle_end = total_lines - suffix_lines

        # Extract sections
        prefix = '\n'.join(lines[:prefix_lines])
        middle = '\n'.join(lines[middle_start:middle_end]) if middle_end > middle_start else ""
        suffix = '\n'.join(lines[middle_end:])

        return {
            "prefix": prefix,
            "suffix": suffix,
            "middle_ground_truth": middle,
            "full_code": full_tla,
            "prefix_lines": prefix_lines,
            "middle_lines": middle_end - middle_start,
            "suffix_lines": suffix_lines,
            "total_lines": total_lines
        }

    def clean_llm_response(response_text: str) -> str:
        """Clean the LLM response by removing markdown fences and explanatory text."""
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

        return response_text.strip()

    # System message for fill-in-the-middle approach
    system_message = SystemMessage(
        content="""You are a TLA+ code completion assistant using fill-in-the-middle approach.

                    You will be given:
                    1. Comments describing the TLA+ specification
                    2. Optional TLC configuration
                    3. PREFIX: The beginning portion of the TLA+ code
                    4. SUFFIX: The ending portion of the TLA+ code

                    Your task is to generate ONLY the MIDDLE section that connects the PREFIX and SUFFIX.

                    CRITICAL INSTRUCTIONS:
                    1. Output ONLY the middle section code that fills the gap between PREFIX and SUFFIX
                    2. DO NOT repeat the PREFIX code in your output
                    3. DO NOT repeat the SUFFIX code in your output
                    4. Your output should start immediately after where PREFIX ends
                    5. Your output should end immediately before where SUFFIX begins
                    6. The code must be valid TLA+ that properly connects PREFIX to SUFFIX
                    7. Ensure proper indentation matching the PREFIX/SUFFIX style
                    8. NEVER include markdown fences (```) or explanations
                    9. NEVER include reasoning text or comments
                    10. No placeholders, no ellipses, only valid TLA+ code

                    Example:
                    If PREFIX ends with: VARIABLES x, y
                    And SUFFIX starts with: Next == ...
                    Then output the middle parts like: TypeOK == ..., Init == ..., etc.
                """
    )

    # Get LLM backend configuration from environment variables
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1")

    # Create model-specific output directory
    # Use custom output dir if provided, otherwise use default outputs/
    custom_output_dir = os.getenv("CUSTOM_OUTPUT_DIR")
    if custom_output_dir:
        model_output_dir = Path(custom_output_dir)
    else:
        model_output_dir = project_root / "outputs" / f"{backend}_{model}"

    generated_dir = model_output_dir / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)

    # Setup model-specific MLflow tracking
    mlflow_dir = model_output_dir / "mlruns"
    mlflow_dir.mkdir(parents=True, exist_ok=True)
    # Use absolute path for MLflow URI
    mlflow.set_tracking_uri(f"file://{mlflow_dir.resolve()}")
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
            temperature = float(os.getenv("OLLAMA_TEMPERATURE", "0.0"))
            repeat_penalty = float(os.getenv("OLLAMA_REPEAT_PENALTY", "1.0"))
            num_predict = int(os.getenv("OLLAMA_NUM_PREDICT", "4096"))
            llm = ChatOllama(
                temperature=temperature,
                repeat_penalty=repeat_penalty,
                model=model,
                base_url=base_url,
                num_predict=num_predict
            )

            print(f"Ollama endpoint: {base_url}")
            print(f"Max output tokens: {num_predict}")
            
        else:
            raise ValueError(f"Unsupported LLM backend: {backend}. Supported backends: openai, anthropic, ollama")
            
    except Exception as e:
        print(f"Error initializing {backend} LLM: {str(e)}")
        print("Tip: Run './run.sh --setup' to configure your LLM backend")
        raise

    print(f"Successfully initialized {backend} LLM with model {model}")
    val_data = load_json_data(val_path)
    results = {}
    module_timings = []

    for target_model in val_data:
        module_name = get_module_base_name(target_model)
        target_comments = load_text(target_model, "comments_clean")
        target_cfg = load_text(target_model, "cfg")
        if not target_comments:
            warnings.warn(f"Skipping model {target_model.get('model', 'UNKNOWN')} due to missing comments.")
            continue

        # Load prefix/suffix for fill-in-the-middle
        partial_data = load_partial_code(target_model)

        if not partial_data or not partial_data["prefix"] or not partial_data["suffix"]:
            warnings.warn(f"Skipping model {target_model.get('model', 'UNKNOWN')} - unable to create PREFIX/SUFFIX split.")
            continue

        # Build the FIM prompt
        user_msg = f"# Comments:\n{target_comments}"
        if target_cfg:
            user_msg += f"\n\n# TLC Configuration:\n{target_cfg}"

        user_msg += f"\n\n# PREFIX (first 30% of code):\n{partial_data['prefix']}"
        user_msg += f"\n\n# SUFFIX (last 30% of code):\n{partial_data['suffix']}"
        user_msg += f"\n\n# YOUR TASK: Generate ONLY the MIDDLE section that connects PREFIX and SUFFIX."
        user_msg += f"\n# DO NOT include PREFIX or SUFFIX in your output!"

        # No few-shot examples for FIM - the PREFIX/SUFFIX provide the context
        all_messages = [system_message, HumanMessage(content=user_msg)]
        print(f"\n--- Generating spec for module: {module_name} ---")
        module_start_time = time.time()
        response = llm.invoke(all_messages)
        module_end_time = time.time()
        module_duration = module_end_time - module_start_time
        module_timings.append((module_name, module_duration))
        print(f"Module {module_name} completed in {module_duration:.2f} seconds")

        # Handle response (string or Message)
        if hasattr(response, "content"):
            response_text = response.content.strip()
        else:
            response_text = str(response).strip()

        # Clean the LLM response
        response_text = clean_llm_response(response_text)

        # The response is just the middle section
        # We need to reconstruct the full file: PREFIX + MIDDLE + SUFFIX
        generated_middle = response_text.strip()

        # Reconstruct the complete TLA+ file
        tla_body = partial_data["prefix"] + "\n" + generated_middle + "\n" + partial_data["suffix"]

        # Save the generated middle section separately for evaluation
        middle_output_path = generated_dir / f"{module_name}_middle_generated.txt"
        middle_output_path.write_text(generated_middle)

        # Save the ground truth middle section for comparison
        ground_truth_middle_path = generated_dir / f"{module_name}_middle_ground_truth.txt"
        ground_truth_middle_path.write_text(partial_data["middle_ground_truth"])

        # Save metadata
        metadata_path = generated_dir / f"{module_name}.metadata.txt"
        metadata_content = f"""Generation Method: Fill-in-the-Middle (Prefix-Suffix)
Prefix Lines: {partial_data['prefix_lines']}
Middle Lines (Ground Truth): {partial_data['middle_lines']}
Suffix Lines: {partial_data['suffix_lines']}
Total Lines: {partial_data['total_lines']}
Generated Middle Lines: {len(generated_middle.split(chr(10)))}

Split Ratio: 30% prefix - 40% middle - 30% suffix
Evaluation: Only the generated middle section is compared against ground truth middle.
"""
        metadata_path.write_text(metadata_content)

        # Ensure proper module format
        if not tla_body.startswith(f"---- MODULE"):
            tla_body = f"---- MODULE {module_name} ----\n" + tla_body
        if not tla_body.rstrip().endswith("===="):
            tla_body = tla_body.rstrip() + "\n===="

        # Write output files
        output_tla_path = generated_dir / f"{module_name}.tla"
        output_cfg_path = generated_dir / f"{module_name}.cfg"
        output_tla_path.write_text(tla_body)

        # Copy the original cfg file
        if target_cfg:
            output_cfg_path.write_text(target_cfg)

        results[module_name] = tla_body

    timing_csv_path = model_output_dir / "module_timings.csv"
    with open(timing_csv_path, 'w') as f:
        f.write("Module,Duration_Seconds,Duration_Minutes\n")
        for module, duration in sorted(module_timings, key=lambda x: x[1], reverse=True):
            f.write(f"{module},{duration:.2f},{duration/60:.2f}\n")

    print(f"\n=== Module Timing Summary ===")
    print(f"Saved detailed timings to: {timing_csv_path}")
    print("\nTop 5 slowest modules:")
    for module, duration in sorted(module_timings, key=lambda x: x[1], reverse=True)[:5]:
        print(f"  {module}: {duration:.2f}s ({duration/60:.2f} min)")

    return results