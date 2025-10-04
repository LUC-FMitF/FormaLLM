# Supported Ollama Models

The pipeline supports any Ollama model. Here are all available options:

## Recommended Models for TLA+ Code Generation

### Small Models (< 5GB)
| Model | Parameters | Size | Command | Best For |
|-------|-----------|------|---------|----------|
| **llama3.1** | 8B | 4.7GB | `ollama pull llama3.1` | General purpose (recommended) |
| **codellama** | 7B | 3.8GB | `ollama pull codellama` | Code generation |
| **mistral** | 7B | 4.1GB | `ollama pull mistral` | Fast & capable |
| **gemma3** | 4B | 3.3GB | `ollama pull gemma3` | Google model |
| **llama3.2** | 3B | 2.0GB | `ollama pull llama3.2` | Lightweight |
| **phi4-mini** | 3.8B | 2.5GB | `ollama pull phi4-mini` | Microsoft mini |
| **llama3.2** | 1B | 1.3GB | `ollama pull llama3.2:1b` | Very lightweight |
| **gemma3** | 1B | 815MB | `ollama pull gemma3:1b` | Smallest option |

### Medium Models (5-20GB)
| Model | Parameters | Size | Command | Best For |
|-------|-----------|------|---------|----------|
| **deepseek-r1** | 7B | 4.7GB | `ollama pull deepseek-r1` | Reasoning & code |
| **phi4** | 14B | 9.1GB | `ollama pull phi4` | Microsoft flagship |
| **llama3.2-vision** | 11B | 7.9GB | `ollama pull llama3.2-vision` | Multimodal |
| **gemma3** | 12B | 8.1GB | `ollama pull gemma3:12b` | Google large |

### Large Models (20GB+)
| Model | Parameters | Size | Command | Best For |
|-------|-----------|------|---------|----------|
| **qwq** | 32B | 20GB | `ollama pull qwq` | Advanced reasoning |
| **gemma3** | 27B | 17GB | `ollama pull gemma3:27b` | Google XL |
| **llama3.3** | 70B | 43GB | `ollama pull llama3.3` | Very powerful |
| **llama4:scout** | 109B | 67GB | `ollama pull llama4:scout` | Latest Llama |

### Specialized Models
| Model | Parameters | Size | Command | Best For |
|-------|-----------|------|---------|----------|
| **neural-chat** | 7B | 4.1GB | `ollama pull neural-chat` | Conversational |
| **starling-lm** | 7B | 4.1GB | `ollama pull starling-lm` | Instruction following |
| **llama2-uncensored** | 7B | 3.8GB | `ollama pull llama2-uncensored` | Unrestricted |
| **granite3.3** | 8B | 4.9GB | `ollama pull granite3.3` | IBM model |
| **moondream** | 1.4B | 829MB | `ollama pull moondream` | Vision tasks |

## Installing a Model

To use any model, first pull it with Ollama:

```bash
ollama pull <model-name>
```

For example:
```bash
ollama pull codellama
ollama pull mistral
ollama pull llama3.2
```

## Usage

When running `./run.sh`, select option 3 (Ollama) and enter the model name when prompted.

Or run directly:
```bash
python run_standalone.py --backend ollama --model codellama
```

## Model Selection Tips

- **For TLA+ generation**: llama3.1, codellama, or deepseek-coder
- **For fastest results**: phi3 or mistral
- **For best quality**: mixtral or llama3.2
- **For low memory**: Use quantized versions (model:7b, model:13b tags)

## Checking Available Models

```bash
ollama list
```
