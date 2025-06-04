#!/bin/bash

set -e  # Exit on error

echo "Activating conda environment 'tla-llm'"
eval "$(conda shell.bash hook)"
conda activate tla-llm

echo "Installing ZenML integrations"
zenml integration install mlflow -y

echo "🧪 Registering MLflow experiment tracker..."
zenml experiment-tracker register mlflow_tracker --flavor=mlflow || true

echo "🧱 Setting MLflow as the active experiment tracker..."
zenml stack set default -e mlflow_tracker

# Optional: Set up DVC remote (replace with your own remote path)
# if dvc remote list | grep -q tla-remote; then
#   echo "DVC remote already exists"
# else
#   echo "Setting up DVC remote (Google Drive / others)..."
#   dvc remote add -d tla-remote gdrive://your-drive-folder-id
# fi

echo "Project environment setup complete."

# Optional: Uncomment to launch MLflow UI automatically
echo "🚀 Starting MLflow UI at http://localhost:5000"
mlflow ui &