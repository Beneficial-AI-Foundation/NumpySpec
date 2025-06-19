"""Codex subagent for integration with the existing GaussianSpec pipeline.

This subagent provides OpenAI Codex capabilities within the existing
subagent architecture, including voice mode, best-of-N sampling,
and streaming generation.
"""

from __future__ import annotations

import asyncio
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Dict, Any

from .codex_client import (
    CodexClient,
    CodexConfig,
    CodexResult,
    VoiceResult,
    VoiceMode,
    CodexModel,
    create_default_codex_client,
    create_voice_enabled_client,
    create_best_of_n_client,
    create_streaming_client,
)


@dataclass(frozen=True)
class CodexGenerationResult:
    """Result from Codex code generation."""
    
    generated_code: str
    success: bool
    error: Optional[str] = None
    usage: Dict[str, Any] = None
    confidence_score: float = 0.0
    samples: List[str] = None
    audio_response: Optional[bytes] = None


@dataclass(frozen=True)
class CodexGenerationSubagent:
    """Subagent for OpenAI Codex code generation."""
    
    prompt: str
    system_prompt: Optional[str] = None
    model: CodexModel = CodexModel.GPT_4O
    temperature: float = 0.7
    max_tokens: int = 2048
    best_of: int = 1
    voice_mode: VoiceMode = VoiceMode.DISABLED
    stream_enabled: bool = False
    
    def run(self) -> CodexGenerationResult:
        """Run Codex generation."""
        return asyncio.run(self._run_async())
    
    async def _run_async(self) -> CodexGenerationResult:
        """Async implementation of Codex generation."""
        try:
            config = CodexConfig(
                model=self.model,
                temperature=self.temperature,
                max_tokens=self.max_tokens,
                best_of=self.best_of,
                voice_mode=self.voice_mode,
                stream_enabled=self.stream_enabled
            )
            
            client = CodexClient(config)
            result = await client.generate_code(
                prompt=self.prompt,
                system_prompt=self.system_prompt
            )
            
            return CodexGenerationResult(
                generated_code=result.text,
                success=True,
                usage=result.usage,
                confidence_score=result.confidence_score,
                samples=result.samples
            )
            
        except Exception as e:
            return CodexGenerationResult(
                generated_code="",
                success=False,
                error=str(e)
            )


@dataclass(frozen=True)
class LeanProofGenerationResult:
    """Result from Lean proof generation using Codex."""
    
    proof_code: str
    success: bool
    error: Optional[str] = None
    problem_statement: str = ""
    formal_statement: str = ""
    confidence_score: float = 0.0
    alternative_proofs: List[str] = None


@dataclass(frozen=True)
class LeanProofGenerationSubagent:
    """Subagent for generating Lean proofs using enhanced Codex."""
    
    problem_statement: str
    formal_statement: str
    use_best_of_n: bool = True
    n_samples: int = 5
    temperature: float = 0.3
    max_tokens: int = 1024
    
    def run(self) -> LeanProofGenerationResult:
        """Run Lean proof generation."""
        return asyncio.run(self._run_async())
    
    async def _run_async(self) -> LeanProofGenerationResult:
        """Async implementation of Lean proof generation."""
        try:
            if self.use_best_of_n:
                client = create_best_of_n_client(self.n_samples)
            else:
                client = create_default_codex_client()
            
            result = await client.generate_lean_proof(
                problem_statement=self.problem_statement,
                formal_statement=self.formal_statement,
                temperature=self.temperature,
                max_tokens=self.max_tokens
            )
            
            return LeanProofGenerationResult(
                proof_code=result.text,
                success=True,
                problem_statement=self.problem_statement,
                formal_statement=self.formal_statement,
                confidence_score=result.confidence_score,
                alternative_proofs=result.samples[1:] if len(result.samples) > 1 else []
            )
            
        except Exception as e:
            return LeanProofGenerationResult(
                proof_code="",
                success=False,
                error=str(e),
                problem_statement=self.problem_statement,
                formal_statement=self.formal_statement
            )


@dataclass(frozen=True)
class VoiceCodexResult:
    """Result from voice-enabled Codex interaction."""
    
    transcribed_input: str
    generated_response: str
    success: bool
    error: Optional[str] = None
    audio_response: Optional[bytes] = None
    confidence: float = 0.0
    duration_ms: int = 0


@dataclass(frozen=True)
class VoiceCodexSubagent:
    """Subagent for voice-enabled Codex interactions."""
    
    audio_input: Optional[bytes] = None
    text_input: Optional[str] = None
    system_prompt: Optional[str] = None
    voice_mode: VoiceMode = VoiceMode.BIDIRECTIONAL
    
    def run(self) -> VoiceCodexResult:
        """Run voice-enabled Codex interaction."""
        return asyncio.run(self._run_async())
    
    async def _run_async(self) -> VoiceCodexResult:
        """Async implementation of voice Codex interaction."""
        try:
            client = create_voice_enabled_client()
            
            result = await client.voice_interaction(
                audio_input=self.audio_input,
                text_input=self.text_input,
                system_prompt=self.system_prompt
            )
            
            return VoiceCodexResult(
                transcribed_input=result.transcribed_text,
                generated_response=result.generated_response,
                success=True,
                audio_response=result.audio_response,
                confidence=result.confidence,
                duration_ms=result.duration_ms
            )
            
        except Exception as e:
            return VoiceCodexResult(
                transcribed_input="",
                generated_response="",
                success=False,
                error=str(e)
            )


@dataclass(frozen=True)
class CodexEnhancedOCRResult:
    """Result from Codex-enhanced OCR processing."""
    
    processed_text: str
    success: bool
    error: Optional[str] = None
    original_ocr: str = ""
    improvements: List[str] = None
    confidence_score: float = 0.0


@dataclass(frozen=True)
class CodexEnhancedOCRSubagent:
    """Subagent that uses Codex to enhance OCR results."""
    
    ocr_text: str
    domain: str = "mathematical"  # "mathematical", "code", "general"
    use_best_of_n: bool = True
    
    def run(self) -> CodexEnhancedOCRResult:
        """Run Codex-enhanced OCR processing."""
        return asyncio.run(self._run_async())
    
    async def _run_async(self) -> CodexEnhancedOCRResult:
        """Async implementation of Codex-enhanced OCR."""
        try:
            client = create_best_of_n_client(3) if self.use_best_of_n else create_default_codex_client()
            
            system_prompt = self._get_system_prompt()
            user_prompt = self._get_user_prompt()
            
            result = await client.generate_code(
                prompt=user_prompt,
                system_prompt=system_prompt,
                temperature=0.3
            )
            
            return CodexEnhancedOCRResult(
                processed_text=result.text,
                success=True,
                original_ocr=self.ocr_text,
                confidence_score=result.confidence_score,
                improvements=result.samples[1:] if len(result.samples) > 1 else []
            )
            
        except Exception as e:
            return CodexEnhancedOCRResult(
                processed_text=self.ocr_text,  # Fallback to original
                success=False,
                error=str(e),
                original_ocr=self.ocr_text
            )
    
    def _get_system_prompt(self) -> str:
        """Get system prompt based on domain."""
        if self.domain == "mathematical":
            return """You are an expert at cleaning and correcting OCR text from mathematical textbooks. 
            Fix OCR errors while preserving mathematical formulas, symbols, and notation. 
            Maintain the original structure and meaning."""
        elif self.domain == "code":
            return """You are an expert at cleaning and correcting OCR text from programming books. 
            Fix OCR errors in code snippets while preserving syntax and structure. 
            Maintain proper indentation and formatting."""
        else:
            return """You are an expert at cleaning and correcting OCR text. 
            Fix common OCR errors while preserving the original meaning and structure."""
    
    def _get_user_prompt(self) -> str:
        """Generate user prompt for OCR enhancement."""
        return f"""Please clean and correct the following OCR text. Fix obvious errors while preserving the original meaning:

OCR Text:
{self.ocr_text}

Corrected Text:"""


@dataclass(frozen=True)
class StreamingCodexResult:
    """Result from streaming Codex generation."""
    
    final_text: str
    success: bool
    error: Optional[str] = None
    chunks: List[str] = None
    total_tokens: int = 0


@dataclass(frozen=True)
class StreamingCodexSubagent:
    """Subagent for streaming Codex generation."""
    
    prompt: str
    system_prompt: Optional[str] = None
    model: CodexModel = CodexModel.GPT_4O
    temperature: float = 0.7
    max_tokens: int = 2048
    
    def run(self) -> StreamingCodexResult:
        """Run streaming Codex generation."""
        return asyncio.run(self._run_async())
    
    async def _run_async(self) -> StreamingCodexResult:
        """Async implementation of streaming generation."""
        try:
            client = create_streaming_client()
            
            result = await client.generate_code(
                prompt=self.prompt,
                system_prompt=self.system_prompt,
                model=self.model.value,
                temperature=self.temperature,
                max_tokens=self.max_tokens
            )
            
            return StreamingCodexResult(
                final_text=result.text,
                success=True,
                chunks=result.samples,
                total_tokens=result.usage.get("total_tokens", 0) if result.usage else 0
            )
            
        except Exception as e:
            return StreamingCodexResult(
                final_text="",
                success=False,
                error=str(e)
            )