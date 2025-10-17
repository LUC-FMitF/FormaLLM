#!/bin/bash
# Creates numbered virtual environments (venv, venv2, venv3, etc.)
# To properly execute this script run 'source ./venv_setup.sh'

if [ ! -d "venv" ]; then
    python3 -m venv venv
    source venv/bin/activate
    pip install --upgrade pip setuptools wheel
    pip install -r requirements.txt
    exit 0
fi

counter=2
while [ -d "venv${counter}" ]; do
    counter=$((counter + 1))
done

python3 -m venv "venv${counter}"
source "venv${counter}/bin/activate"
pip install --upgrade pip setuptools wheel
pip install -r requirements.txt