#!/usr/bin/env python3
"""
Collect statistics for the original TLA+ dataset.
Generates dataset_stats.csv with metrics for each model.
"""

import csv
import json
from pathlib import Path
from typing import Dict, List, Optional
import tiktoken

def count_tokens(text: str, model: str = "gpt-4") -> int:
    """Count tokens using tiktoken."""
    try:
        encoding = tiktoken.encoding_for_model(model)
        return len(encoding.encode(text))
    except Exception:
        # Fallback: rough estimate
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

def collect_dataset_stats():
    """Collect statistics for all models in the dataset."""
    script_dir = Path(__file__).parent
    data_dir = script_dir
    all_models_path = data_dir / "all_models.json"
    
    if not all_models_path.exists():
        print(f"Error: {all_models_path} not found")
        return
    
    # Load model metadata
    with open(all_models_path, 'r') as f:
        all_models_data = json.load(f)
    
    # Handle both formats: array or {"data": array}
    if isinstance(all_models_data, dict) and 'data' in all_models_data:
        all_models = all_models_data['data']
    else:
        all_models = all_models_data
    
    stats = []
    
    for model_entry in all_models:
        model_name = model_entry.get('model', 'UNKNOWN')
        print(f"Processing: {model_name}")
        
        model_stats = {
            'model_name': model_name,
        }
        
        # Get paths from metadata
        comments_path = model_entry.get('comments_clean')
        tla_path = model_entry.get('tla')
        cfg_path = model_entry.get('cfg')
        
        # Resolve paths
        for file_type, rel_path in [('comments', comments_path), ('tla', tla_path), ('cfg', cfg_path)]:
            if rel_path:
                # Try relative to data directory
                file_path = data_dir / rel_path
                if not file_path.exists():
                    # Try searching for it
                    possible_files = list(data_dir.rglob(Path(rel_path).name))
                    if possible_files:
                        file_path = possible_files[0]
                
                file_stats = get_file_stats(file_path)
                if file_stats:
                    for key, value in file_stats.items():
                        model_stats[f'{file_type}_{key}'] = value
                else:
                    # File missing or error
                    for key in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                        model_stats[f'{file_type}_{key}'] = None
            else:
                # No path in metadata
                for key in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                    model_stats[f'{file_type}_{key}'] = None
        
        # Calculate totals
        total_size_bytes = sum(filter(None, [
            model_stats.get('comments_size_bytes'),
            model_stats.get('tla_size_bytes'),
            model_stats.get('cfg_size_bytes')
        ])) or None
        
        total_tokens = sum(filter(None, [
            model_stats.get('comments_tokens'),
            model_stats.get('tla_tokens'),
            model_stats.get('cfg_tokens')
        ])) or None
        
        model_stats['total_size_bytes'] = total_size_bytes
        model_stats['total_size_kb'] = round(total_size_bytes / 1024, 2) if total_size_bytes else None
        model_stats['total_tokens'] = total_tokens
        
        stats.append(model_stats)
    
    # Write to CSV
    output_path = data_dir / "dataset_stats.csv"
    
    if stats:
        # Get all possible fieldnames
        fieldnames = ['model_name']
        for prefix in ['comments', 'tla', 'cfg']:
            for suffix in ['size_bytes', 'size_kb', 'lines', 'characters', 'tokens', 'words']:
                fieldnames.append(f'{prefix}_{suffix}')
        fieldnames.extend(['total_size_bytes', 'total_size_kb', 'total_tokens'])
        
        with open(output_path, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(stats)
        
        print(f"\n✅ Statistics saved to: {output_path}")
        print(f"   Models processed: {len(stats)}")
        
        # Summary statistics
        total_models = len(stats)
        models_with_comments = sum(1 for s in stats if s.get('comments_size_bytes'))
        models_with_tla = sum(1 for s in stats if s.get('tla_size_bytes'))
        models_with_cfg = sum(1 for s in stats if s.get('cfg_size_bytes'))
        
        print(f"\nSummary:")
        print(f"   Total models: {total_models}")
        print(f"   With comments: {models_with_comments}")
        print(f"   With TLA files: {models_with_tla}")
        print(f"   With CFG files: {models_with_cfg}")
        
        avg_tokens = sum(filter(None, [s.get('total_tokens') for s in stats])) / total_models
        print(f"   Average total tokens: {avg_tokens:.0f}")
    else:
        print("No statistics collected")

if __name__ == "__main__":
    collect_dataset_stats()
