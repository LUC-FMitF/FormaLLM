#!/usr/bin/env python3
"""
Simple test script to verify LLM backend configuration works
"""
import os
import warnings
from langchain_ollama import ChatOllama
from langchain.prompts import PromptTemplate
from langchain.chains.llm import LLMChain

# Suppress warnings
warnings.filterwarnings('ignore')

# Test configuration
backend = os.getenv("LLM_BACKEND", "ollama")
model = os.getenv("LLM_MODEL", "llama3.1")

print(f"Testing LLM backend: {backend}")
print(f"Model: {model}")
print("-" * 50)

# Initialize LLM
if backend == "ollama":
    llm = ChatOllama(temperature=0, model=model)
    print(f"[OK] Successfully initialized {backend} with model {model}")
else:
    print(f"[ERROR] Backend {backend} not tested in this script")
    exit(1)

# Create a simple chain
prompt_template = PromptTemplate.from_template(
    "Write a simple TLA+ module called Hello that has a variable x. Keep it under 10 lines."
)
chain = LLMChain(llm=llm, prompt=prompt_template)

# Test the chain
print("\nSending test prompt to LLM...")
print("-" * 50)

try:
    response = chain.run({})
    print("\n[OK] Response received:")
    print("-" * 50)
    print(response)
    print("-" * 50)
    print("\n[SUCCESS] LLM backend test successful!")
except Exception as e:
    print(f"\n[ERROR] {e}")
    exit(1)
