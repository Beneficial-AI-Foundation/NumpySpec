from __future__ import annotations
"""OpenAI Codex integration for Lean theorem proving with voice mode, online setup, and best-of-n.

This module provides enhanced Codex capabilities for the GaussianSpec project:
- Voice mode: Speech-to-text for dictating theorem statements
- Online setup: Real-time Codex API calls for Lean code completion
- Best of N: Generate multiple completions and select the best one

Example
-------
>>> from gaussianspec.codex_utils import CodexClient, best_of_n_completion
>>> client = CodexClient()
>>> completions = best_of_n_completion(client, "theorem example : 1 + 1 = 2 := ", n=3)
>>> print(completions[0])  # doctest: +SKIP
"""

import os
import json
import base64
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass
from pathlib import Path
import tempfile
import subprocess
import time

try:
    import openai
    _OPENAI_AVAILABLE = True
except ImportError:
    _OPENAI_AVAILABLE = False

try:
    import speech_recognition as sr
    _SPEECH_RECOGNITION_AVAILABLE = True
except ImportError:
    _SPEECH_RECOGNITION_AVAILABLE = False


@dataclass
class CodexCompletion:
    """Represents a single Codex completion with metadata."""
    text: str
    confidence: float
    finish_reason: str
    tokens_used: int


@dataclass
class VoiceInput:
    """Represents processed voice input."""
    text: str
    confidence: float
    audio_duration: float


class CodexClient:
    """OpenAI Codex client with enhanced features for Lean theorem proving."""
    
    def __init__(
        self,
        api_key: Optional[str] = None,
        model: str = "gpt-4",  # Using GPT-4 as Codex is deprecated, but with code-optimized prompts
        max_tokens: int = 512,
        temperature: float = 0.2,
    ):
        """Initialize Codex client.
        
        Parameters
        ----------
        api_key : str, optional
            OpenAI API key. If None, reads from OPENAI_API_KEY environment variable.
        model : str
            Model to use. Defaults to GPT-4 with code-optimized prompts.
        max_tokens : int
            Maximum tokens per completion.
        temperature : float
            Sampling temperature for completions.
        """
        if not _OPENAI_AVAILABLE:
            raise ImportError("OpenAI package not available. Install with: uv add openai")
        
        self.api_key = api_key or os.getenv("OPENAI_API_KEY")
        if not self.api_key:
            raise ValueError("OpenAI API key required. Set OPENAI_API_KEY environment variable.")
        
        self.client = openai.OpenAI(api_key=self.api_key)
        self.model = model
        self.max_tokens = max_tokens
        self.temperature = temperature
    
    def complete_lean_code(
        self,
        prompt: str,
        context: str = "",
        max_tokens: Optional[int] = None,
        temperature: Optional[float] = None,
    ) -> CodexCompletion:
        """Generate a single Lean code completion.
        
        Parameters
        ----------
        prompt : str
            The Lean code prompt to complete.
        context : str
            Additional context about the theorem or proof.
        max_tokens : int, optional
            Override default max_tokens.
        temperature : float, optional
            Override default sampling temperature.
            
        Returns
        -------
        CodexCompletion
            The generated completion with metadata.
        """
        system_prompt = (
            "You are an expert Lean 4 theorem prover. Generate precise, syntactically correct "
            "Lean code completions. Focus on mathematical rigor and proper Lean syntax. "
            "Do not include explanations unless requested."
        )
        
        if context:
            user_prompt = f"Context: {context}\n\nComplete this Lean code:\n{prompt}"
        else:
            user_prompt = f"Complete this Lean code:\n{prompt}"
        
        response = self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt}
            ],
            max_tokens=max_tokens or self.max_tokens,
            temperature=temperature or self.temperature,
            stop=["theorem", "lemma", "def", "example", "\n\n"]
        )
        
        choice = response.choices[0]
        return CodexCompletion(
            text=choice.message.content or "",
            confidence=1.0,  # GPT models don't return confidence scores
            finish_reason=choice.finish_reason or "stop",
            tokens_used=response.usage.total_tokens if response.usage else 0
        )


def best_of_n_completion(
    client: CodexClient,
    prompt: str,
    n: int = 3,
    context: str = "",
    selection_criteria: str = "shortest_valid",
) -> List[CodexCompletion]:
    """Generate multiple completions and return them ranked by quality.
    
    Parameters
    ----------
    client : CodexClient
        The Codex client to use.
    prompt : str
        The Lean code prompt to complete.
    n : int
        Number of completions to generate.
    context : str
        Additional context for the completion.
    selection_criteria : str
        How to rank completions: "shortest_valid", "most_tokens", "random"
        
    Returns
    -------
    List[CodexCompletion]
        Completions sorted by quality (best first).
    """
    completions = []
    
    for i in range(n):
        try:
            # Vary temperature slightly for diversity
            temp = client.temperature + (i * 0.1)
            completion = client.complete_lean_code(
                prompt=prompt,
                context=context,
                temperature=min(temp, 1.0)
            )
            completions.append(completion)
        except Exception as e:
            print(f"Warning: Failed to generate completion {i+1}: {e}")
            continue
    
    # Rank completions based on selection criteria
    if selection_criteria == "shortest_valid":
        # Prefer shorter completions that don't have syntax errors
        completions.sort(key=lambda c: (
            _has_lean_syntax_errors(c.text),  # Errors go last
            len(c.text.strip())  # Shorter is better among valid ones
        ))
    elif selection_criteria == "most_tokens":
        completions.sort(key=lambda c: c.tokens_used, reverse=True)
    # "random" keeps original order
    
    return completions


def _has_lean_syntax_errors(lean_code: str) -> bool:
    """Basic heuristic to check if Lean code has obvious syntax errors."""
    # Simple checks for common syntax issues
    common_errors = [
        lean_code.count("(") != lean_code.count(")"),
        lean_code.count("{") != lean_code.count("}"),
        lean_code.count("[") != lean_code.count("]"),
        "by sorry" in lean_code.lower(),
        lean_code.strip().endswith(","),
    ]
    return any(common_errors)


class VoiceMode:
    """Voice input support for dictating Lean theorem statements."""
    
    def __init__(self, language: str = "en-US", timeout: float = 10.0):
        """Initialize voice mode.
        
        Parameters
        ----------
        language : str
            Language code for speech recognition.
        timeout : float
            Maximum time to wait for speech input.
        """
        if not _SPEECH_RECOGNITION_AVAILABLE:
            raise ImportError(
                "Speech recognition not available. Install with: uv add speechrecognition pyaudio"
            )
        
        self.recognizer = sr.Recognizer()
        self.language = language
        self.timeout = timeout
    
    def listen_for_theorem(self, prompt: str = "Speak your theorem statement:") -> VoiceInput:
        """Listen for voice input and convert to text.
        
        Parameters
        ----------
        prompt : str
            Text prompt to display to user.
            
        Returns
        -------
        VoiceInput
            The processed voice input.
        """
        print(prompt)
        
        with sr.Microphone() as source:
            print("Listening... (speak now)")
            self.recognizer.adjust_for_ambient_noise(source, duration=1)
            
            start_time = time.time()
            try:
                audio = self.recognizer.listen(source, timeout=self.timeout)
                duration = time.time() - start_time
                
                # Try Google Speech Recognition (free tier)
                try:
                    text = self.recognizer.recognize_google(audio, language=self.language)
                    confidence = 0.8  # Google doesn't return confidence by default
                except sr.UnknownValueError:
                    text = ""
                    confidence = 0.0
                except sr.RequestError as e:
                    print(f"Could not request results from Google Speech Recognition: {e}")
                    text = ""
                    confidence = 0.0
                
                return VoiceInput(
                    text=text,
                    confidence=confidence,
                    audio_duration=duration
                )
                
            except sr.WaitTimeoutError:
                return VoiceInput(
                    text="",
                    confidence=0.0,
                    audio_duration=self.timeout
                )
    
    def theorem_from_voice(self, voice_input: VoiceInput) -> str:
        """Convert voice input to formal Lean theorem statement.
        
        This uses Codex to convert natural language to Lean syntax.
        """
        if not voice_input.text or voice_input.confidence < 0.5:
            raise ValueError("Voice input too unclear or empty")
        
        # Use OpenAI to convert natural language to Lean
        client = openai.OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
        
        response = client.chat.completions.create(
            model="gpt-4",
            messages=[
                {
                    "role": "system",
                    "content": (
                        "You are an expert at converting natural language mathematical statements "
                        "into formal Lean 4 theorem statements. Provide only the theorem statement, "
                        "no proof. Use proper Lean 4 syntax."
                    )
                },
                {
                    "role": "user",
                    "content": f"Convert this to a Lean 4 theorem statement: {voice_input.text}"
                }
            ],
            max_tokens=256,
            temperature=0.1
        )
        
        return response.choices[0].message.content or ""


class OnlineCodexSetup:
    """Real-time Codex integration for interactive proof development."""
    
    def __init__(self, client: CodexClient, auto_complete: bool = True):
        """Initialize online Codex setup.
        
        Parameters
        ----------
        client : CodexClient
            The Codex client to use.
        auto_complete : bool
            Whether to automatically suggest completions.
        """
        self.client = client
        self.auto_complete = auto_complete
        self.completion_cache: Dict[str, List[CodexCompletion]] = {}
    
    def get_completions(
        self,
        current_code: str,
        cursor_position: int,
        n_suggestions: int = 3,
    ) -> List[CodexCompletion]:
        """Get real-time code completions at cursor position.
        
        Parameters
        ----------
        current_code : str
            The current Lean code being edited.
        cursor_position : int
            Position of the cursor in the code.
        n_suggestions : int
            Number of suggestions to generate.
            
        Returns
        -------
        List[CodexCompletion]
            Ranked completion suggestions.
        """
        # Extract context around cursor
        before_cursor = current_code[:cursor_position]
        after_cursor = current_code[cursor_position:]
        
        # Create completion prompt
        prompt = before_cursor
        context = f"Complete this in the context of: {after_cursor[:100]}..."
        
        # Check cache first
        cache_key = f"{prompt}|{context}"
        if cache_key in self.completion_cache:
            return self.completion_cache[cache_key]
        
        # Generate completions
        completions = best_of_n_completion(
            client=self.client,
            prompt=prompt,
            n=n_suggestions,
            context=context,
            selection_criteria="shortest_valid"
        )
        
        # Cache results
        self.completion_cache[cache_key] = completions
        
        return completions
    
    def clear_cache(self):
        """Clear the completion cache."""
        self.completion_cache.clear()


def setup_codex_environment() -> Dict[str, Any]:
    """Setup and validate the Codex environment.
    
    Returns
    -------
    Dict[str, Any]
        Environment status and available features.
    """
    status = {
        "openai_available": _OPENAI_AVAILABLE,
        "speech_recognition_available": _SPEECH_RECOGNITION_AVAILABLE,
        "api_key_configured": bool(os.getenv("OPENAI_API_KEY")),
        "features": {
            "code_completion": _OPENAI_AVAILABLE and bool(os.getenv("OPENAI_API_KEY")),
            "voice_mode": _SPEECH_RECOGNITION_AVAILABLE,
            "best_of_n": _OPENAI_AVAILABLE and bool(os.getenv("OPENAI_API_KEY")),
            "online_setup": _OPENAI_AVAILABLE and bool(os.getenv("OPENAI_API_KEY")),
        }
    }
    
    return status


# Example usage and integration
if __name__ == "__main__":
    # Test the setup
    status = setup_codex_environment()
    print("Codex Environment Status:")
    print(json.dumps(status, indent=2))
    
    if status["features"]["code_completion"]:
        client = CodexClient()
        
        # Test basic completion
        prompt = "theorem add_comm (a b : ℕ) : a + b = b + a := "
        completion = client.complete_lean_code(prompt)
        print(f"\nBasic completion: {completion.text}")
        
        # Test best-of-n
        completions = best_of_n_completion(client, prompt, n=2)
        print(f"\nBest of 2 completions:")
        for i, comp in enumerate(completions):
            print(f"  {i+1}: {comp.text}")