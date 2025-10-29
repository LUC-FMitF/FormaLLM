#!/usr/bin/env python3
"""
Preview Excel files: print sheet names and first 5 rows for each sheet.
"""
from pathlib import Path
import os
import sys

try:
    import pandas as pd
except Exception as e:
    print("Required package 'pandas' not installed. Please run: pip install pandas openpyxl")
    sys.exit(2)

project_root = Path(__file__).resolve().parents[1]
backend = os.getenv("LLM_BACKEND", "ollama")
model = os.getenv("LLM_MODEL", "llama3.1:latest")

files = [
    ("Original dataset", project_root / "data" / "dataset_stats.xlsx"),
    ("Generated dataset", project_root / "outputs" / f"{backend}_{model}" / "generated_stats.xlsx"),
]

for title, path in files:
    print("\n" + "="*60)
    print(f"Preview: {title}\nPath: {path}")
    if not path.exists():
        print("  -> File not found")
        continue
    try:
        xl = pd.ExcelFile(path)
        print(f"  Sheets: {xl.sheet_names}")
        for sheet in xl.sheet_names:
            print('\n  --- Sheet:', sheet, '---')
            df = xl.parse(sheet_name=sheet)
            print(f"   Rows: {len(df):,}, Columns: {len(df.columns)}")
            # print first 5 rows
            with pd.option_context('display.max_columns', None, 'display.width', 200):
                print(df.head(5).to_string(index=False))
    except Exception as e:
        print(f"  Error reading Excel: {e}")

print("\nPreview complete.")
