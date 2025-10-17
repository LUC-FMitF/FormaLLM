#!/usr/bin/env python3
"""
Comprehensive LLM backend test script for FormaLLM
Tests OpenAI, Anthropic, and Ollama backends with proper error handling
"""
import os
import sys
import warnings
from pathlib import Path

# Add project root to path for imports
project_root = Path(__file__).resolve().parent
sys.path.append(str(project_root))

from langchain_openai import ChatOpenAI
from langchain_anthropic import ChatAnthropic 
from langchain_ollama import ChatOllama
from langchain.prompts import PromptTemplate
from langchain.chains.llm import LLMChain

# Suppress warnings for cleaner output
warnings.filterwarnings('ignore')

# Colors for better UX
RED = '\033[0;31m'
GREEN = '\033[0;32m'
YELLOW = '\033[1;33m'
BLUE = '\033[0;34m'
NC = '\033[0m'  # No Color

def print_colored(text, color):
    """Print text with color"""
    print(f"{color}{text}{NC}")

def load_env():
    """Load environment variables from .env file if it exists"""
    env_file = project_root / ".env"
    if env_file.exists():
        with open(env_file) as f:
            for line in f:
                if line.strip() and not line.startswith('#'):
                    try:
                        key, value = line.strip().split('=', 1)
                        os.environ[key] = value
                    except ValueError:
                        continue

def test_llm_backend(backend, model, test_prompt="Hello! Can you help me with TLA+ specifications?"):
    """Test a specific LLM backend"""
    print_colored(f"\nTesting {backend.upper()} with model: {model}", BLUE)
    print("-" * 60)
    
    try:
        # Initialize LLM based on backend
        if backend == "openai":
            api_key = os.getenv("OPENAI_API_KEY")
            if not api_key or api_key == "your-openai-key-here":
                raise ValueError("OpenAI API key not configured")
            llm = ChatOpenAI(temperature=0, model=model, api_key=api_key)
            
        elif backend == "anthropic":
            api_key = os.getenv("ANTHROPIC_API_KEY")
            if not api_key or api_key == "your-anthropic-key-here":
                raise ValueError("Anthropic API key not configured")
            llm = ChatAnthropic(temperature=0, model=model, api_key=api_key)
            
        elif backend == "ollama":
            base_url = os.getenv("OLLAMA_BASE_URL", "http://localhost:11434")
            llm = ChatOllama(temperature=0, model=model, base_url=base_url)
            print(f"Ollama endpoint: {base_url}")
            
        else:
            raise ValueError(f"Unsupported backend: {backend}")
        
        print_colored("[+] LLM initialized successfully", GREEN)
        
        # Test with a simple prompt
        chain = LLMChain(
            llm=llm,
            prompt=PromptTemplate.from_template("{input}")
        )
        
        print(f"Testing with prompt: '{test_prompt}'")
        response = chain.run(input=test_prompt)
        
        print_colored("[+] Response received successfully", GREEN)
        print(f"Response preview: {response[:100]}...")
        
        return True, response
        
    except Exception as e:
        print_colored(f"[ERROR] Error testing {backend}: {str(e)}", RED)
        return False, str(e)

def main():
    """Main test function"""
    print_colored("FormaLLM Multi-LLM Backend Test", BLUE)
    print_colored("=" * 60, BLUE)
    
    # Load environment variables
    load_env()
    
    # Get current configuration
    current_backend = os.getenv("LLM_BACKEND", "ollama")
    current_model = os.getenv("LLM_MODEL", "llama3.1")
    
    print(f"\nCurrent Configuration:")
    print(f"   Backend: {current_backend}")
    print(f"   Model: {current_model}")
    
    # Test current configuration
    success, result = test_llm_backend(current_backend, current_model)
    
    if success:
        print_colored(f"\n{current_backend.upper()} backend test PASSED!", GREEN)
    else:
        print_colored(f"\n{current_backend.upper()} backend test FAILED!", RED)
        print_colored("Troubleshooting tips:", YELLOW)
        
        if current_backend == "openai":
            print("   • Check your OPENAI_API_KEY in .env file")
            print("   • Verify the model name is correct")
            print("   • Ensure you have API credits")
            
        elif current_backend == "anthropic":
            print("   • Check your ANTHROPIC_API_KEY in .env file")
            print("   • Verify the model name is correct")
            print("   • Ensure you have API credits")
            
        elif current_backend == "ollama":
            print("   • Check if Ollama service is running: docker-compose ps")
            print("   • Start Ollama: docker-compose up -d ollama")
            print("   • Pull the model: docker-compose exec ollama ollama pull llama3.1")
            print("   • Check logs: docker-compose logs ollama")
    
    # Offer to test other backends
    if len(sys.argv) > 1 and sys.argv[1] == "--all":
        print_colored("\nTesting all configured backends...", BLUE)
        
        backends_to_test = []
        
        if os.getenv("OPENAI_API_KEY") and os.getenv("OPENAI_API_KEY") != "your-openai-key-here":
            backends_to_test.append(("openai", os.getenv("OPENAI_MODEL", "gpt-4")))
        
        if os.getenv("ANTHROPIC_API_KEY") and os.getenv("ANTHROPIC_API_KEY") != "your-anthropic-key-here":
            backends_to_test.append(("anthropic", os.getenv("ANTHROPIC_MODEL", "claude-3-5-sonnet-20241022")))
        
        if os.getenv("OLLAMA_ENABLED", "true").lower() == "true":
            backends_to_test.append(("ollama", os.getenv("OLLAMA_MODEL", "llama3.1")))
        
        results = {}
        for backend, model in backends_to_test:
            if backend != current_backend:  # Skip already tested
                success, _ = test_llm_backend(backend, model)
                results[backend] = success
        
        print_colored("\nTest Results Summary:", BLUE)
        print("-" * 40)
        results[current_backend] = success  # Add current backend result
        
        for backend, passed in results.items():
            status = "[PASS]" if passed else "[FAIL]"
            print(f"   {backend.upper()}: {status}")
    
    print_colored(f"\nTo reconfigure LLMs: ./run.sh --setup", YELLOW)
    print_colored(f"To test all backends: python test_llm.py --all", YELLOW)

if __name__ == "__main__":
    main()
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
