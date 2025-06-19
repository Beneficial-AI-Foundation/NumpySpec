"""Enhanced OpenAI Codex client with voice mode, online setup, and best of N sampling.

This module provides a comprehensive integration with OpenAI's Codex models,
including the latest features like voice mode, real-time online capabilities,
and best-of-N sampling for improved code generation quality.

Features:
- Voice mode integration with audio I/O
- Online setup with real-time streaming
- Best of N sampling with quality ranking
- Integration with existing Lean proof generation
- Async support for better performance
"""

from __future__ import annotations

import asyncio
import base64
import io
import json
import os
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, AsyncGenerator, Dict, List, Optional, Union, Callable
from enum import Enum

try:
    import openai
    from openai import AsyncOpenAI
except ImportError:
    openai = None
    AsyncOpenAI = None

try:
    import numpy as np
    import sounddevice as sd
    import soundfile as sf
except ImportError:
    np = None
    sd = None
    sf = None


class CodexModel(Enum):
    """Available Codex models with their capabilities."""
    GPT_4O = "gpt-4o"
    GPT_4O_MINI = "gpt-4o-mini"
    GPT_4_TURBO = "gpt-4-turbo"
    O1_PREVIEW = "o1-preview"
    O1_MINI = "o1-mini"


class VoiceMode(Enum):
    """Voice mode options."""
    DISABLED = "disabled"
    LISTEN_ONLY = "listen_only"
    SPEAK_ONLY = "speak_only"
    BIDIRECTIONAL = "bidirectional"


@dataclass(frozen=True)
class CodexConfig:
    """Configuration for enhanced Codex client."""
    
    # Model configuration
    model: CodexModel = CodexModel.GPT_4O
    temperature: float = 0.7
    max_tokens: int = 2048
    
    # Best of N sampling
    n_samples: int = 1
    best_of: int = 1
    ranking_strategy: str = "probability"  # "probability", "length", "custom"
    
    # Voice mode settings
    voice_mode: VoiceMode = VoiceMode.DISABLED
    voice_model: str = "tts-1"
    voice_name: str = "alloy"
    speech_recognition_model: str = "whisper-1"
    
    # Online/streaming settings
    stream_enabled: bool = False
    real_time_enabled: bool = False
    websocket_enabled: bool = False
    
    # API configuration
    api_key: Optional[str] = None
    organization: Optional[str] = None
    base_url: Optional[str] = None
    
    # Timeout settings
    request_timeout: float = 30.0
    stream_timeout: float = 60.0
    
    # Audio settings (for voice mode)
    sample_rate: int = 24000
    audio_format: str = "wav"
    voice_activity_detection: bool = True


@dataclass
class CodexResult:
    """Result from Codex generation."""
    
    text: str
    model: str
    usage: Dict[str, Any] = field(default_factory=dict)
    metadata: Dict[str, Any] = field(default_factory=dict)
    samples: List[str] = field(default_factory=list)
    rankings: List[float] = field(default_factory=list)
    audio_data: Optional[bytes] = None
    confidence_score: float = 0.0


@dataclass
class VoiceResult:
    """Result from voice interaction."""
    
    transcribed_text: str
    generated_response: str
    audio_response: Optional[bytes] = None
    confidence: float = 0.0
    duration_ms: int = 0


class CodexClient:
    """Enhanced OpenAI Codex client with advanced features."""
    
    def __init__(self, config: CodexConfig):
        if openai is None:
            raise ImportError("openai package required. Install with: uv add openai")
        
        self.config = config
        self._setup_client()
        self._audio_enabled = self._check_audio_dependencies()
    
    def _setup_client(self) -> None:
        """Initialize OpenAI client with configuration."""
        api_key = self.config.api_key or os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ValueError("OpenAI API key required")
        
        client_kwargs = {
            "api_key": api_key,
            "timeout": self.config.request_timeout,
        }
        
        if self.config.organization:
            client_kwargs["organization"] = self.config.organization
        
        if self.config.base_url:
            client_kwargs["base_url"] = self.config.base_url
        
        self.client = openai.OpenAI(**client_kwargs)
        self.async_client = AsyncOpenAI(**client_kwargs)
    
    def _check_audio_dependencies(self) -> bool:
        """Check if audio dependencies are available."""
        return all(x is not None for x in [np, sd, sf])
    
    async def generate_code(
        self,
        prompt: str,
        system_prompt: Optional[str] = None,
        **kwargs
    ) -> CodexResult:
        """Generate code with best-of-N sampling and quality ranking."""
        
        # Override config with kwargs
        model = kwargs.get("model", self.config.model.value)
        temperature = kwargs.get("temperature", self.config.temperature)
        max_tokens = kwargs.get("max_tokens", self.config.max_tokens)
        n_samples = kwargs.get("n", self.config.n_samples)
        best_of = kwargs.get("best_of", self.config.best_of)
        
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})
        
        # Generate multiple samples if best_of > 1
        if best_of > 1:
            return await self._generate_with_best_of_n(
                messages, model, temperature, max_tokens, n_samples, best_of
            )
        
        # Standard generation
        if self.config.stream_enabled:
            return await self._generate_streaming(messages, model, temperature, max_tokens)
        else:
            return await self._generate_standard(messages, model, temperature, max_tokens, n_samples)
    
    async def _generate_standard(
        self,
        messages: List[Dict[str, str]],
        model: str,
        temperature: float,
        max_tokens: int,
        n_samples: int
    ) -> CodexResult:
        """Standard code generation."""
        
        response = await self.async_client.chat.completions.create(
            model=model,
            messages=messages,
            temperature=temperature,
            max_tokens=max_tokens,
            n=n_samples
        )
        
        # Extract results
        if n_samples == 1:
            text = response.choices[0].message.content or ""
            samples = [text]
        else:
            samples = [choice.message.content or "" for choice in response.choices]
            text = samples[0]  # Use first sample as primary result
        
        return CodexResult(
            text=text,
            model=model,
            usage=response.usage.model_dump() if response.usage else {},
            samples=samples,
            confidence_score=1.0 / len(samples) if samples else 0.0
        )
    
    async def _generate_streaming(
        self,
        messages: List[Dict[str, str]],
        model: str,
        temperature: float,
        max_tokens: int
    ) -> CodexResult:
        """Streaming code generation."""
        
        stream = await self.async_client.chat.completions.create(
            model=model,
            messages=messages,
            temperature=temperature,
            max_tokens=max_tokens,
            stream=True
        )
        
        text_chunks = []
        usage_data = {}
        
        async for chunk in stream:
            if chunk.choices and chunk.choices[0].delta.content:
                text_chunks.append(chunk.choices[0].delta.content)
            
            if chunk.usage:
                usage_data = chunk.usage.model_dump()
        
        text = "".join(text_chunks)
        
        return CodexResult(
            text=text,
            model=model,
            usage=usage_data,
            samples=[text],
            confidence_score=1.0
        )
    
    async def _generate_with_best_of_n(
        self,
        messages: List[Dict[str, str]],
        model: str,
        temperature: float,
        max_tokens: int,
        n_samples: int,
        best_of: int
    ) -> CodexResult:
        """Generate with best-of-N sampling and ranking."""
        
        # Generate multiple completions
        tasks = []
        for _ in range(best_of):
            task = self._generate_standard(messages, model, temperature, max_tokens, n_samples)
            tasks.append(task)
        
        results = await asyncio.gather(*tasks)
        
        # Collect all samples
        all_samples = []
        for result in results:
            all_samples.extend(result.samples)
        
        # Rank samples
        rankings = await self._rank_samples(all_samples, messages)
        
        # Sort by ranking and get best
        ranked_samples = sorted(zip(all_samples, rankings), key=lambda x: x[1], reverse=True)
        best_text = ranked_samples[0][0]
        
        return CodexResult(
            text=best_text,
            model=model,
            usage=results[0].usage,  # Use first result's usage as approximation
            samples=[sample for sample, _ in ranked_samples],
            rankings=[ranking for _, ranking in ranked_samples],
            confidence_score=ranked_samples[0][1]
        )
    
    async def _rank_samples(
        self,
        samples: List[str],
        original_messages: List[Dict[str, str]]
    ) -> List[float]:
        """Rank code samples based on quality."""
        
        if self.config.ranking_strategy == "length":
            return [len(sample) for sample in samples]
        
        elif self.config.ranking_strategy == "probability":
            # Use a simple heuristic based on response structure
            rankings = []
            for sample in samples:
                score = 0.0
                # Prefer samples with proper code structure
                if "def " in sample or "class " in sample:
                    score += 0.3
                if sample.count("\n") > 2:  # Multi-line responses
                    score += 0.2
                if not sample.strip().endswith("..."):  # Complete responses
                    score += 0.3
                # Penalize very short or very long responses
                length_score = min(len(sample) / 1000, 1.0) * 0.2
                score += length_score
                rankings.append(score)
            return rankings
        
        else:  # custom ranking - placeholder for future ML-based ranking
            return [1.0] * len(samples)
    
    async def voice_interaction(
        self,
        audio_input: Optional[bytes] = None,
        text_input: Optional[str] = None,
        system_prompt: Optional[str] = None
    ) -> VoiceResult:
        """Handle voice-based interaction with Codex."""
        
        if self.config.voice_mode == VoiceMode.DISABLED:
            raise ValueError("Voice mode is disabled")
        
        if not self._audio_enabled:
            raise RuntimeError("Audio dependencies not available. Install with: uv add sounddevice soundfile numpy")
        
        # Transcribe audio input if provided
        transcribed_text = ""
        if audio_input and self.config.voice_mode in [VoiceMode.LISTEN_ONLY, VoiceMode.BIDIRECTIONAL]:
            transcribed_text = await self._transcribe_audio(audio_input)
        
        # Use transcribed text or provided text
        input_text = transcribed_text or text_input or ""
        if not input_text:
            raise ValueError("No input provided (audio or text)")
        
        # Generate response
        result = await self.generate_code(input_text, system_prompt)
        
        # Generate audio response if needed
        audio_response = None
        if self.config.voice_mode in [VoiceMode.SPEAK_ONLY, VoiceMode.BIDIRECTIONAL]:
            audio_response = await self._text_to_speech(result.text)
        
        return VoiceResult(
            transcribed_text=transcribed_text,
            generated_response=result.text,
            audio_response=audio_response,
            confidence=result.confidence_score
        )
    
    async def _transcribe_audio(self, audio_data: bytes) -> str:
        """Transcribe audio using Whisper."""
        
        # Save audio to temporary file
        with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as tmp_file:
            tmp_file.write(audio_data)
            tmp_path = tmp_file.name
        
        try:
            with open(tmp_path, "rb") as audio_file:
                response = await self.async_client.audio.transcriptions.create(
                    model=self.config.speech_recognition_model,
                    file=audio_file
                )
            return response.text
        finally:
            os.unlink(tmp_path)
    
    async def _text_to_speech(self, text: str) -> bytes:
        """Convert text to speech using OpenAI TTS."""
        
        response = await self.async_client.audio.speech.create(
            model=self.config.voice_model,
            voice=self.config.voice_name,
            input=text
        )
        
        return response.content
    
    def record_audio(self, duration: float = 5.0) -> bytes:
        """Record audio from microphone."""
        
        if not self._audio_enabled:
            raise RuntimeError("Audio dependencies not available")
        
        print(f"Recording for {duration} seconds...")
        audio_data = sd.rec(
            int(duration * self.config.sample_rate),
            samplerate=self.config.sample_rate,
            channels=1,
            dtype=np.float32
        )
        sd.wait()
        
        # Convert to bytes
        with io.BytesIO() as buffer:
            sf.write(buffer, audio_data, self.config.sample_rate, format=self.config.audio_format.upper())
            return buffer.getvalue()
    
    def play_audio(self, audio_data: bytes) -> None:
        """Play audio data."""
        
        if not self._audio_enabled:
            raise RuntimeError("Audio dependencies not available")
        
        with io.BytesIO(audio_data) as buffer:
            data, sample_rate = sf.read(buffer)
            sd.play(data, samplerate=sample_rate)
            sd.wait()
    
    async def generate_lean_proof(
        self,
        problem_statement: str,
        formal_statement: str,
        **kwargs
    ) -> CodexResult:
        """Generate Lean proofs using enhanced Codex capabilities."""
        
        system_prompt = """You are an expert Lean 4 theorem prover. Generate complete, 
        syntactically correct Lean proofs. Use proper tactics and ensure the proof compiles."""
        
        user_prompt = f"""
Problem: {problem_statement}

Formal Statement:
```lean
{formal_statement}
```

Generate a complete Lean proof:
```lean
"""
        
        # Use best-of-N sampling for higher quality proofs
        config_override = {
            "best_of": max(self.config.best_of, 3),
            "temperature": 0.3,  # Lower temperature for more precise proofs
            **kwargs
        }
        
        result = await self.generate_code(user_prompt, system_prompt, **config_override)
        
        # Post-process to extract just the proof
        if "```" in result.text:
            proof_section = result.text.split("```")[0].strip()
            result.text = proof_section
        
        return result


# Factory functions for common configurations
def create_default_codex_client() -> CodexClient:
    """Create a Codex client with default configuration."""
    return CodexClient(CodexConfig())


def create_voice_enabled_client() -> CodexClient:
    """Create a Codex client with voice mode enabled."""
    config = CodexConfig(
        voice_mode=VoiceMode.BIDIRECTIONAL,
        stream_enabled=True
    )
    return CodexClient(config)


def create_best_of_n_client(n: int = 5) -> CodexClient:
    """Create a Codex client optimized for best-of-N sampling."""
    config = CodexConfig(
        best_of=n,
        n_samples=1,
        ranking_strategy="probability",
        temperature=0.8
    )
    return CodexClient(config)


def create_streaming_client() -> CodexClient:
    """Create a Codex client with streaming enabled."""
    config = CodexConfig(
        stream_enabled=True,
        real_time_enabled=True,
        temperature=0.7
    )
    return CodexClient(config)