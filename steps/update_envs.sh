#!/bin/bash
set -e

echo "📦 Updating Conda environment from environment.yml..."
conda env update -n tla-llm -f /workspaces/FormaLLM/environment.yml
conda clean -afy
echo "✅ Conda environment updated."
