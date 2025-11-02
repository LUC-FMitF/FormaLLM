#!/usr/bin/env python3
"""
Collect statistics for the generated TLA+ outputs.
Generates generated_stats.csv with metrics for each generated model.
"""

import csv
import os
from pathlib import Path
from typing import Dict, Optional
import tiktoken
import argparse

# Token encoder cache (initialized in __main__)
_TOKEN_ENCODER = None


def init_token_encoder(model_name: str):
    global _TOKEN_ENCODER
    try:
        _TOKEN_ENCODER = tiktoken.encoding_for_model(model_name)
    except Exception:
        try:
            _TOKEN_ENCODER = tiktoken.get_encoding("cl100k_base")
        except Exception:
            _TOKEN_ENCODER = None


def count_tokens(text: str, model: str = None) -> int:
    """Count tokens using cached tiktoken encoder or a per-call model.

    Falls back to word count if tokenization is unavailable.
    """
    # If caller specified model, try per-call
    if model:
        try:
            enc = tiktoken.encoding_for_model(model)
            return len(enc.encode(text))
        except Exception:
            pass

    if _TOKEN_ENCODER:
        try:
            return len(_TOKEN_ENCODER.encode(text))
        except Exception:
            pass

    return len(text.split())

def get_file_stats(file_path: Path) -> Optional[Dict]:
    """Get statistics for a single file."""
    if not file_path.exists():
        return None
    
    try:
        content = file_path.read_text(encoding='utf-8')
        size_bytes = file_path.stat().st_size
        
        return {
            'size_bytes': size_bytes,
            'size_kb': round(size_bytes / 1024, 2),
            'lines': len(content.splitlines()),
            'characters': len(content),
            'tokens': count_tokens(content),
            'words': len(content.split()),
        }
    except Exception as e:
        print(f"Warning: Error reading {file_path}: {e}")
        return None

def collect_generated_stats():
    """Collect statistics for all generated files."""
    script_dir = Path(__file__).parent
    
    # Get model info from environment or use default
    backend = os.getenv("LLM_BACKEND", "ollama")
    model = os.getenv("LLM_MODEL", "llama3.1:latest")
    model_dir = script_dir / f"{backend}_{model}"
    
    generated_dir = model_dir / "generated"
    
    if not generated_dir.exists():
        print(f"Error: Generated directory not found: {generated_dir}")
        print(f"Please run the pipeline first: ./run.sh")
        return
    
    stats = []

    # Try to load mlflow trace token usage mapping: module_name -> token usage
    trace_token_usage = {}
    mlruns_dir = model_dir / "mlruns"
    if mlruns_dir.exists():
        # Walk experiments and traces
        for exp_dir in mlruns_dir.iterdir():
            traces_dir = exp_dir / "traces"
            if not traces_dir.exists():
                continue
            for trace_id_dir in traces_dir.iterdir():
                try:
                    req_meta = trace_id_dir / "request_metadata"
                    token_file = req_meta / "mlflow.trace.tokenUsage"
                    outputs_file = req_meta / "mlflow.traceOutputs"
                    if not token_file.exists():
                        continue
                    # Read token usage
                    import json as _json
                    tu = _json.loads(token_file.read_text())
                    input_tokens = tu.get("input_tokens")
                    output_tokens = tu.get("output_tokens")
                    total_tokens = tu.get("total_tokens")

                    # Try to extract module name from the outputs preview
                    module_name = None
                    if outputs_file.exists():
                        out_txt = outputs_file.read_text(errors='ignore')
                        # Look for TLA module header "---- MODULE <Name> ----"
                        import re as _re
                        m = _re.search(r"----\s*MODULE\s+([A-Za-z0-9_]+)", out_txt)
                        if m:
                            module_name = m.group(1)

                    if module_name:
                        # Sum token usage if multiple traces for same module
                        prev = trace_token_usage.get(module_name, {})
                        trace_token_usage[module_name] = {
                            'input_tokens': (prev.get('input_tokens', 0) or 0) + (input_tokens or 0),
                            'output_tokens': (prev.get('output_tokens', 0) or 0) + (output_tokens or 0),
                            'total_tokens': (prev.get('total_tokens', 0) or 0) + (total_tokens or 0),
                        }
                except Exception:
                    # Ignore trace parsing errors and continue
                    continue
    
    # Find all generated .tla files
    tla_files = sorted(generated_dir.glob("*.tla"))
    
    print(f"Found {len(tla_files)} generated TLA+ files")
    
    for tla_file in tla_files:
        model_name = tla_file.stem  # filename without extension
        print(f"Processing: {model_name}")
        
        model_stats = {
            'model_name': model_name,
        }
        
        # Get TLA file stats
        tla_stats = get_file_stats(tla_file)
        if tla_stats:
            for key, value in tla_stats.items():
                model_stats[f'tla_{key}'] = value
        else:
            for key in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                model_stats[f'tla_{key}'] = None
        
        # Check for corresponding CFG file
        cfg_file = generated_dir / f"{model_name}.cfg"
        cfg_stats = get_file_stats(cfg_file)
        if cfg_stats:
            for key, value in cfg_stats.items():
                model_stats[f'cfg_{key}'] = value
        else:
            for key in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                model_stats[f'cfg_{key}'] = None
        
        # Calculate totals
        total_size_bytes = sum(filter(None, [
            model_stats.get('tla_size_bytes'),
            model_stats.get('cfg_size_bytes')
        ])) or None
        
        total_tokens = sum(filter(None, [
            model_stats.get('tla_tokens'),
            model_stats.get('cfg_tokens')
        ])) or None
        
        model_stats['total_size_bytes'] = total_size_bytes
        model_stats['total_size_kb'] = round(total_size_bytes / 1024, 2) if total_size_bytes else None
        model_stats['total_tokens'] = total_tokens
        model_stats['has_cfg'] = cfg_file.exists()

        # Add llm model info and token usage (if available from traces)
        model_stats['llm_backend'] = backend
        model_stats['llm_model'] = model

        tu = trace_token_usage.get(model_name)
        if tu:
            model_stats['llm_input_tokens'] = tu.get('input_tokens')
            model_stats['llm_output_tokens'] = tu.get('output_tokens')
            model_stats['llm_total_tokens'] = tu.get('total_tokens')
        else:
            model_stats['llm_input_tokens'] = None
            model_stats['llm_output_tokens'] = None
            model_stats['llm_total_tokens'] = None
        # Placeholder fields for reasoning vs regular token counts.
        # Currently the pipeline records only total/input/output token counts
        # in mlflow traces under `mlflow.trace.tokenUsage`. To populate these
        # fields we need either (a) token-level traces annotated with a
        # `type`/`role` (e.g. 'reasoning' vs 'regular') in the trace artifacts,
        # or (b) explicit markers in prompts/outputs that allow segmenting the
        # text and counting tokens per segment. See notes below.
        model_stats['llm_reasoning_tokens'] = None
        model_stats['llm_regular_tokens'] = None
        
        stats.append(model_stats)
    
    # Write to a central generated_stats directory so we keep one CSV per backend_model
    output_dir = script_dir / "generated_stats"
    try:
        output_dir.mkdir(parents=True, exist_ok=True)
    except Exception:
        pass
    # sanitize filename by replacing os-unfriendly characters (colon) with underscore
    safe_model_name = f"{backend}_{model}".replace(':', '_')
    output_path = output_dir / f"{safe_model_name}.csv"
    
    if stats:
        # Get all possible fieldnames
        fieldnames = ['model_name']
        for prefix in ['tla', 'cfg']:
            for suffix in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                fieldnames.append(f'{prefix}_{suffix}')
        fieldnames.extend(['total_size_bytes', 'total_size_kb', 'total_tokens', 'has_cfg'])
        # LLM metadata and token usage (if available from mlflow traces)
        fieldnames.extend([
            'llm_backend', 'llm_model', 'llm_input_tokens', 'llm_output_tokens',
            'llm_total_tokens', 'llm_reasoning_tokens', 'llm_regular_tokens'
        ])

        with open(output_path, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(stats)

        print(f"\n✅ Statistics saved to: {output_path}")
        print(f"   Models processed: {len(stats)}")

        # Summary statistics
        total_models = len(stats)
        models_with_tla = sum(1 for s in stats if s.get('tla_size_bytes'))
        models_with_cfg = sum(1 for s in stats if s.get('has_cfg'))

        print(f"\nSummary:")
        print(f"   Total models: {total_models}")
        print(f"   With TLA files: {models_with_tla}")
        print(f"   With CFG files: {models_with_cfg}")

        total_tokens_list = [s.get('total_tokens') for s in stats if s.get('total_tokens')]
        if total_tokens_list:
            avg_tokens = sum(total_tokens_list) / len(total_tokens_list)
            print(f"   Average total tokens: {avg_tokens:.0f}")

        total_size_list = [s.get('total_size_kb') for s in stats if s.get('total_size_kb')]
        if total_size_list:
            total_size = sum(total_size_list)
            print(f"   Total size: {total_size:.2f} KB")
    else:
        print("No statistics collected")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Collect generated dataset statistics")
    parser.add_argument("--token-model", type=str, help="Token model name for tiktoken (env: TOKEN_MODEL or LLM_MODEL)")
    parser.add_argument("--backend", "-b", type=str, help="LLM backend to use (env: LLM_BACKEND)")
    parser.add_argument("--model", "-m", type=str, help="LLM model name to use (env: LLM_MODEL)")
    args = parser.parse_args()

    # Allow CLI flags to override environment variables for easier debugging/runs
    if args.backend:
        os.environ["LLM_BACKEND"] = args.backend
    if args.model:
        os.environ["LLM_MODEL"] = args.model

    token_model = args.token_model or os.getenv("TOKEN_MODEL") or os.getenv("LLM_MODEL") or "gpt-4"
    init_token_encoder(token_model)

    # Informative debug output so users can see exactly what backend/model will be used
    resolved_backend = os.getenv("LLM_BACKEND", "ollama")
    resolved_model = os.getenv("LLM_MODEL", "llama3.1:latest")
    script_dir = Path(__file__).parent
    model_dir = script_dir / f"{resolved_backend}_{resolved_model}"
    print(f"Debug: Using LLM_BACKEND={resolved_backend!r}, LLM_MODEL={resolved_model!r}")
    print(f"Debug: Looking for generated files in: {model_dir / 'generated'}")

    collect_generated_stats()
