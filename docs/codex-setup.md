# Enhanced OpenAI Codex Setup

This document describes the enhanced OpenAI Codex integration in GaussianSpec, including voice mode, online setup, and best-of-N sampling capabilities.

## Features

### 🎤 Voice Mode
- **Bidirectional communication** with Codex via voice
- **Speech-to-text** using OpenAI Whisper
- **Text-to-speech** using OpenAI TTS
- **Real-time audio processing** with voice activity detection

### 🌐 Online Setup
- **Streaming generation** for real-time responses
- **WebSocket support** for persistent connections
- **Real-time capabilities** with low latency

### 🎯 Best of N Sampling
- **Multiple sample generation** with quality ranking
- **Intelligent ranking strategies** (probability, length, custom)
- **Confidence scoring** for generated results
- **Alternative solutions** for complex problems

## Quick Start

### 1. Environment Setup

```bash
# Install dependencies
uv sync

# Set OpenAI API key
export OPENAI_API_KEY="your-api-key-here"

# Optional: Set organization ID
export OPENAI_ORG_ID="your-org-id"
```

### 2. Basic Usage

```python
from gaussianspec.codex_client import create_default_codex_client

# Create client
client = create_default_codex_client()

# Generate code
result = await client.generate_code(
    prompt="Write a function to compute matrix multiplication",
    system_prompt="You are an expert in numerical computing."
)

print(result.text)
```

### 3. Voice Mode Setup

#### Audio Dependencies
```bash
# Install audio dependencies
uv add sounddevice soundfile numpy

# On Linux, you may need additional system packages:
sudo apt-get install portaudio19-dev python3-pyaudio

# On macOS with Homebrew:
brew install portaudio
```

#### Voice Usage
```python
from gaussianspec.codex_client import create_voice_enabled_client

client = create_voice_enabled_client()

# Record and process audio
audio_data = client.record_audio(duration=5.0)
result = await client.voice_interaction(audio_input=audio_data)

print(f"You said: {result.transcribed_text}")
print(f"Codex responded: {result.generated_response}")

# Play audio response
if result.audio_response:
    client.play_audio(result.audio_response)
```

## Advanced Configuration

### Codex Configuration

```python
from gaussianspec.codex_client import CodexClient, CodexConfig, CodexModel, VoiceMode

config = CodexConfig(
    # Model settings
    model=CodexModel.GPT_4O,
    temperature=0.7,
    max_tokens=2048,
    
    # Best of N sampling
    best_of=5,
    n_samples=1,
    ranking_strategy="probability",
    
    # Voice mode
    voice_mode=VoiceMode.BIDIRECTIONAL,
    voice_model="tts-1",
    voice_name="alloy",
    speech_recognition_model="whisper-1",
    
    # Streaming
    stream_enabled=True,
    real_time_enabled=True,
    
    # Audio settings
    sample_rate=24000,
    audio_format="wav",
    voice_activity_detection=True
)

client = CodexClient(config)
```

### Best of N Sampling

```python
from gaussianspec.codex_client import create_best_of_n_client

# Create client with best-of-N sampling
client = create_best_of_n_client(n=5)

result = await client.generate_code(
    prompt="Implement quicksort with error handling",
    system_prompt="Write clean, efficient code."
)

print(f"Best result (confidence: {result.confidence_score:.2f}):")
print(result.text)

print(f"\nGenerated {len(result.samples)} alternatives")
for i, (sample, score) in enumerate(zip(result.samples, result.rankings)):
    print(f"Sample {i+1} (score: {score:.3f}): {sample[:50]}...")
```

## Integration with GaussianSpec Pipeline

### 1. Lean Proof Generation

```python
from gaussianspec.codex_subagent import LeanProofGenerationSubagent

subagent = LeanProofGenerationSubagent(
    problem_statement="Prove that Gaussian elimination produces a left inverse",
    formal_statement="theorem gaussianElimination_is_left_inverse (A : Matrix n n ℝ) (h : IsNonsingular A) : gaussianElimination A * A = 1 :=",
    use_best_of_n=True,
    n_samples=5
)

result = subagent.run()
if result.success:
    print("Generated proof:")
    print(result.proof_code)
```

### 2. OCR Enhancement

```python
from gaussianspec.codex_subagent import CodexEnhancedOCRSubagent

# Enhance OCR results using Codex
subagent = CodexEnhancedOCRSubagent(
    ocr_text="Gaussain Elimnation algoritm...",  # OCR text with errors
    domain="mathematical",
    use_best_of_n=True
)

result = subagent.run()
if result.success:
    print("Corrected text:")
    print(result.processed_text)
```

### 3. Pipeline Integration

```python
from gaussianspec.pipeline import run_pipeline, PipelineArgs
from gaussianspec.codex_subagent import CodexGenerationSubagent

# Enhanced pipeline with Codex code generation
def enhanced_pipeline(args: PipelineArgs):
    # Run standard pipeline
    result = run_pipeline(args)
    
    # Generate enhanced Lean code using Codex
    if result.ocr.success:
        code_gen = CodexGenerationSubagent(
            prompt=f"Convert this mathematical text to Lean 4 code: {result.ocr.txt_path.read_text()[:500]}",
            system_prompt="You are an expert in Lean 4 theorem proving.",
            best_of=3
        )
        
        codex_result = code_gen.run()
        if codex_result.success:
            print("Codex-generated Lean code:")
            print(codex_result.generated_code)
    
    return result
```

## Voice Mode Setup

### System Requirements

- **Microphone** for audio input
- **Speakers/headphones** for audio output
- **Audio drivers** (PortAudio)

### Linux Setup
```bash
# Install system dependencies
sudo apt-get update
sudo apt-get install portaudio19-dev python3-pyaudio alsamixer

# Test audio
arecord -d 5 test.wav
aplay test.wav
```

### macOS Setup
```bash
# Install PortAudio via Homebrew
brew install portaudio

# Test audio (built-in tools)
say "Testing audio output"
```

### Windows Setup
```bash
# PortAudio is typically included with sounddevice
# Test with Windows built-in tools
```

### Voice Configuration

```python
from gaussianspec.codex_client import CodexConfig, VoiceMode

config = CodexConfig(
    voice_mode=VoiceMode.BIDIRECTIONAL,
    
    # Voice settings
    voice_model="tts-1-hd",  # Higher quality
    voice_name="nova",       # Available: alloy, echo, fable, onyx, nova, shimmer
    
    # Speech recognition
    speech_recognition_model="whisper-1",
    
    # Audio settings
    sample_rate=24000,
    audio_format="wav",
    voice_activity_detection=True
)
```

## Error Handling and Troubleshooting

### Common Issues

#### 1. Audio Not Working
```python
# Check audio devices
import sounddevice as sd
print(sd.query_devices())

# Test recording
try:
    client = create_voice_enabled_client()
    audio = client.record_audio(duration=2.0)
    print(f"Recorded {len(audio)} bytes")
except Exception as e:
    print(f"Audio error: {e}")
```

#### 2. API Rate Limits
```python
# Configure rate limiting
config = CodexConfig(
    request_timeout=60.0,  # Longer timeout
    best_of=3,             # Reduce concurrent requests
)
```

#### 3. Large Response Handling
```python
# Use streaming for large responses
config = CodexConfig(
    stream_enabled=True,
    max_tokens=4096,
    stream_timeout=120.0
)
```

### Debugging

```python
import logging

# Enable debug logging
logging.basicConfig(level=logging.DEBUG)

# Test connection
client = create_default_codex_client()
try:
    result = await client.generate_code("print('hello')")
    print("Connection successful")
except Exception as e:
    print(f"Connection failed: {e}")
```

## Performance Optimization

### 1. Best of N Configuration

```python
# For development (fast)
config = CodexConfig(best_of=1, temperature=0.5)

# For production (quality)
config = CodexConfig(best_of=5, temperature=0.3, ranking_strategy="probability")
```

### 2. Streaming for Long Responses

```python
# Enable streaming for better user experience
config = CodexConfig(
    stream_enabled=True,
    real_time_enabled=True
)
```

### 3. Caching

```python
# Implement result caching
from functools import lru_cache

@lru_cache(maxsize=100)
def cached_generate(prompt: str, system_prompt: str = None):
    client = create_default_codex_client()
    return asyncio.run(client.generate_code(prompt, system_prompt))
```

## Examples

See `src/gaussianspec/codex_examples.py` for comprehensive examples including:

- Basic code generation
- Best-of-N sampling
- Voice interactions
- Lean proof generation
- OCR enhancement
- Streaming generation
- GaussianSpec-specific use cases

## API Reference

### CodexClient Methods

- `generate_code()` - Generate code with configurable sampling
- `voice_interaction()` - Voice-enabled interaction
- `generate_lean_proof()` - Specialized Lean proof generation
- `record_audio()` - Record audio from microphone
- `play_audio()` - Play audio through speakers

### Subagents

- `CodexGenerationSubagent` - General code generation
- `LeanProofGenerationSubagent` - Lean proof generation
- `VoiceCodexSubagent` - Voice interactions
- `CodexEnhancedOCRSubagent` - OCR text enhancement
- `StreamingCodexSubagent` - Streaming generation

### Factory Functions

- `create_default_codex_client()` - Basic client
- `create_voice_enabled_client()` - Voice-enabled client
- `create_best_of_n_client(n)` - Best-of-N sampling client
- `create_streaming_client()` - Streaming client

## Security Considerations

1. **API Keys**: Store securely in environment variables
2. **Audio Privacy**: Voice data is sent to OpenAI for processing
3. **Rate Limits**: Monitor usage to avoid exceeding quotas
4. **Error Handling**: Implement proper error handling for production use

## Support

- Check the [OpenAI Codex Changelog](https://help.openai.com/en/articles/11428266-codex-changelog) for updates
- Review `src/gaussianspec/codex_examples.py` for usage patterns
- Report issues to the GaussianSpec repository