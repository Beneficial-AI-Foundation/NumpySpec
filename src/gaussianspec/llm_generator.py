"""
LLM-based Lean code and specification generator.

This module provides a two-stage pipeline:
1. Input (Python code/docstring) -> Lean implementation
2. Lean implementation -> Lean specification

Uses the existing hf_utils infrastructure for model loading and generation.
Created: 2025-06-11
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Union, Dict, Any
from .model_deployment import ModelDeployment, ModelConfig

# @dataclass(frozen=True)
class LeanCodeGenerationResult:
    """Result of generating Lean code from Python input."""
    lean_code: str
    success: bool
    error: Optional[str] = None

    def __init__(self, lean_code: str, success: bool, error: Optional[str] = None):
        self.lean_code = lean_code
        self.success = success
        self.error = error


# @dataclass(frozen=True)
class LeanSpecGenerationResult:
    """Result of generating Lean specification from Lean code."""
    lean_spec: str
    success: bool
    error: Optional[str] = None

    def __init__(self, lean_spec: str, success: bool, error: Optional[str] = None):
        self.lean_spec = lean_spec
        self.success = success
        self.error = error


# @dataclass
class LLMCodeSpecGenerator:
    """Generate Lean code and specifications using LLM inference.
    
    This generator follows a two-stage pipeline:
    1. Python program/docstring -> Lean implementation
    2. Lean implementation -> Lean specification
    
    Supports both local and API models through unified deployment interface.
    """
    
    _deployment: ModelDeployment | None = None
    _load_error: str | None = None
    model_config: ModelConfig
    debug_save_responses: bool = False
    debug_output_dir: Path


    def __init__(self, 
                 model_config: Union[Dict[str, Any], ModelConfig, None] = None,
                 model_name: Optional[str] = None,  # For backward compatibility
                 max_new_tokens: int = 512, 
                 temperature: float = 0.2, 
                 top_p: float = 0.9, 
                 debug_save_responses: bool = False, 
                 debug_output_dir: Optional[Path] = None):
        
        # Handle backward compatibility and different config options
        if model_config is None:
            # Use default local model configuration
            model_name = model_name or "nvidia/Nemotron-Research-Reasoning-Qwen-1.5B"
            self.model_config = ModelConfig(
                type="local",
                model_name_or_path=model_name,
                max_tokens=max_new_tokens,
                temperature=temperature,
                top_p=top_p
            )
        elif isinstance(model_config, dict):
            # Fill in missing generation parameters
            config_dict = model_config.copy()
            config_dict.setdefault("max_tokens", max_new_tokens)
            config_dict.setdefault("temperature", temperature)
            config_dict.setdefault("top_p", top_p)
            self.model_config = ModelConfig(**config_dict)
        else:
            self.model_config = model_config
        
        self.debug_save_responses = debug_save_responses
        self.debug_output_dir = debug_output_dir or Path("debug_llm_responses")

        try:
            self._deployment = ModelDeployment(self.model_config)
        except Exception as e:
            print(f"Error loading model: {e}")
            self._deployment = None
            self._load_error = str(e)
       
    
    def generate_lean_code(self, python_input: str) -> LeanCodeGenerationResult:
        """Generate Lean implementation from Python program/docstring.
        
        Parameters
        ----------
        python_input : str
            Python code and/or docstring to translate to Lean
            
        Returns
        -------
        LeanCodeGenerationResult
            Generated Lean code with success status
        """
        if self._deployment is None or not self._deployment.is_available():
            return LeanCodeGenerationResult(
                "", False, f"Model deployment failed: {getattr(self, '_load_error', 'Unknown error')}"
            )
        
        prompt = self._build_code_generation_prompt(python_input)
        
        completion = self._deployment.generate(prompt)
        
        # Save debug information if requested
        if self.debug_save_responses:
            self._save_debug_response("code_generation", prompt, completion, python_input)
        
        # Extract Lean code from completion
        lean_code = self._extract_lean_code(completion)
        
        return LeanCodeGenerationResult(lean_code, True)
    
    def generate_lean_spec(self, lean_code: str) -> LeanSpecGenerationResult:
        """Generate Lean specification from Lean implementation.
        
        Parameters
        ----------
        lean_code : str
            Lean implementation code to generate specification for
            
        Returns
        -------
        LeanSpecGenerationResult
            Generated Lean specification with success status
        """
        if self._deployment is None or not self._deployment.is_available():
            return LeanSpecGenerationResult(
                "", False, f"Model deployment failed: {getattr(self, '_load_error', 'Unknown error')}"
            )
        
        try:
            prompt = self._build_spec_generation_prompt(lean_code)
            
            completion = self._deployment.generate(prompt)
            
            # Save debug information if requested
            if self.debug_save_responses:
                self._save_debug_response("spec_generation", prompt, completion, lean_code)
            
            # Extract Lean spec from completion
            lean_spec = self._extract_lean_spec(completion)
            
            return LeanSpecGenerationResult(lean_spec, True)
            
        except Exception as e:
            return LeanSpecGenerationResult("", False, str(e))
    
    def generate_full_pipeline(self, python_input: str) -> tuple[LeanCodeGenerationResult, LeanSpecGenerationResult]:
        """Run the full pipeline: Python -> Lean code -> Lean spec.
        
        Parameters
        ----------
        python_input : str
            Python code and/or docstring
            
        Returns
        -------
        tuple[LeanCodeGenerationResult, LeanSpecGenerationResult]
            Results from both generation stages
        """
        # Stage 1: Generate Lean code
        code_result = self.generate_lean_code(python_input)
        
        # Stage 2: Generate Lean spec (only if stage 1 succeeded)
        if code_result.success:
            spec_result = self.generate_lean_spec(code_result.lean_code)
        else:
            spec_result = LeanSpecGenerationResult(
                "", False, "Lean code generation failed"
            )
        
        return code_result, spec_result
    
    def _build_code_generation_prompt(self, python_input: str) -> str:
        """Build prompt for Python -> Lean code generation."""
        system_msg = """You are an expert in formal verification and Lean 4. You translate Python programs into equivalent Lean 4 implementations."""
        
        user_msg = (
            "Translate the following Python code into Lean 4. "
            "Focus on creating clean, idiomatic Lean code that captures the essential logic. "
            "Use appropriate Lean 4 syntax and mathlib types where applicable.\n\n"
            f"Python code:\n```python\n{python_input}\n```\n\n"
            "You can think multiple times before writing the code. "
            "Output your results in the following format: "
            "[[OUTPUT]]your output here[[\\OUTPUT]]"
        )
        
        prompt = (
            f"<|im_start|>system\n{system_msg}<|im_end|>\n"
            f"<|im_start|>user\n{user_msg}<|im_end|>\n"
            "<|im_start|>assistant\n"
        )
        
        return prompt
    
    def _build_spec_generation_prompt(self, lean_code: str) -> str:
        """Build prompt for Lean code -> Lean specification generation."""
        system_msg = """You are an expert in formal verification and Lean 4. You write precise specifications and theorems for Lean implementations."""
        
        user_msg = (
            "Given the following Lean 4 implementation, write formal specifications (theorems) that capture its intended behavior. "
            "Include preconditions, postconditions, and key properties. Use standard Lean 4 theorem syntax.\n\n"
            f"Lean implementation:\n```lean\n{lean_code}\n```\n\n"
            "You can think multiple times before writing the code. "
            "Output your results in the following format: "
            "[[OUTPUT]]your output here[[\\OUTPUT]]"
        )
        
        prompt = (
            f"<|im_start|>system\n{system_msg}<|im_end|>\n"
            f"<|im_start|>user\n{user_msg}<|im_end|>\n"
            "<|im_start|>assistant\n"
        )
        
        return prompt
    
    def _extract_lean_code(self, completion: str) -> str:
        """Extract Lean code from model completion using [[OUTPUT]] markers."""
        # Look for the new output format first
        if "[[OUTPUT]]" in completion and "[[\\OUTPUT]]" in completion:
            # Extract content between the markers
            start_marker = "[[OUTPUT]]"
            end_marker = "[[\\OUTPUT]]"
            start_idx = completion.find(start_marker)
            end_idx = completion.find(end_marker)
            
            if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
                code = completion[start_idx + len(start_marker):end_idx].strip()
            else:
                # Fallback if markers are malformed
                code = completion.strip()
        # Fallback to old code fence format
        elif "```" in completion:
            code = completion.split("```")[0].strip()
        else:
            code = completion.strip()
        
        # Clean up common artifacts and preserve only Lean code
        return self._clean_lean_content(code)
    
    def _extract_lean_spec(self, completion: str) -> str:
        """Extract Lean specification from model completion using [[OUTPUT]] markers."""
        # Look for the new output format first
        if "[[OUTPUT]]" in completion and "[[\\OUTPUT]]" in completion:
            # Extract content between the markers
            start_marker = "[[OUTPUT]]"
            end_marker = "[[\\OUTPUT]]"
            start_idx = completion.find(start_marker)
            end_idx = completion.find(end_marker)
            
            if start_idx != -1 and end_idx != -1 and end_idx > start_idx:
                spec = completion[start_idx + len(start_marker):end_idx].strip()
            else:
                # Fallback if markers are malformed
                spec = completion.strip()
        # Fallback to old code fence format
        elif "```" in completion:
            spec = completion.split("```")[0].strip()
        else:
            spec = completion.strip()
        
        # Clean up common artifacts and preserve only Lean spec
        return self._clean_lean_content(spec)
    
    def _save_debug_response(self, stage: str, prompt: str, completion: str, input_context: str):
        """Save full LLM communication for debugging."""
        if not self.debug_save_responses:
            return
            
        self.debug_output_dir.mkdir(parents=True, exist_ok=True)
        
        import datetime
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        debug_file = self.debug_output_dir / f"{stage}_{timestamp}.md"
        
        debug_content = f"""# LLM Debug Log - {stage.title()}
Generated: {timestamp}
Model: {self.model_config.model_name_or_path or self.model_config.model_type}

## Input Context
```
{input_context}
```

## Prompt Sent to LLM
```
{prompt}
```

## Raw LLM Response
```
{completion}
```

## Extracted Content
"""
        if stage == "code_generation":
            extracted = self._extract_lean_code(completion)
        else:
            extracted = self._extract_lean_spec(completion)
            
        debug_content += f"""```lean
{extracted}
```

## Cleaned Content
```lean
{self._clean_lean_content(extracted)}
```
"""
        
        debug_file.write_text(debug_content)
        print(f"Debug info saved to: {debug_file}")
    
    def _clean_lean_content(self, content: str) -> str:
        """Clean Lean content to preserve only code/spec, removing thinking text."""
        lines = content.split('\n')
        cleaned_lines = []
        
        for line in lines:
            stripped = line.strip()
            
            # Skip empty lines
            if not stripped:
                continue
            
            # Skip obvious thinking/explanation lines
            thinking_patterns = [
                'let me think',
                'i need to',
                'the idea is',
                'we need to',
                'first,',
                'next,',
                'then,',
                'finally,',
                'note that',
                'observe that',
                'it\'s important',
                'remember that',
                'here\'s how',
                'this will',
                'this should',
                'this means',
                'in this case',
                'for this',
                'so we',
                'we can see',
                'we have',
                'we define',
                'we want',
                'the goal is',
                'the approach',
                'the key insight'
            ]
            
            line_lower = stripped.lower()
            is_thinking = any(pattern in line_lower for pattern in thinking_patterns)
            
            # Skip thinking lines
            if is_thinking:
                continue
                
            # Skip explanatory comments that look like natural language
            if stripped.startswith('--') and any(word in line_lower for word in ['this', 'the', 'we', 'that', 'will', 'should', 'can', 'would', 'could']):
                continue
            
            # Skip lines that are purely explanatory text (no Lean syntax)
            lean_keywords = ['def', 'theorem', 'lemma', 'inductive', 'structure', 'class', 'instance', 'variable', 'axiom', 'namespace', 'section', 'import', 'open', 'by', ':=', '→', '∀', '∃', 'Prop', 'Type', 'Sort']
            has_lean_syntax = any(keyword in stripped for keyword in lean_keywords) or any(char in stripped for char in [':', '(', ')', '{', '}', '[', ']'])
            
            # If it looks like plain English explanation without Lean syntax, skip it
            if not has_lean_syntax and len(stripped.split()) > 3 and not stripped.startswith('--'):
                continue
            
            cleaned_lines.append(line)
        
        result = '\n'.join(cleaned_lines).strip()
        
        # Remove multiple consecutive blank lines
        import re
        result = re.sub(r'\n\s*\n\s*\n', '\n\n', result)
        
        return result


# @dataclass(frozen=True)
class LLMCodeSpecSubagent:
    """Subagent for LLM-based Lean code and spec generation.
    
    Follows the same pattern as other subagents in the codebase.
    """
    
    python_input: str
    model_config: Union[Dict[str, Any], ModelConfig]
    output_dir: Optional[Path] = None
    
    def __init__(self, 
                 python_input: str, 
                 model_config: Union[Dict[str, Any], ModelConfig, None] = None,
                 model_name: Optional[str] = None,  # For backward compatibility
                 output_dir: Optional[Path] = None, 
                 debug_save_responses: bool = False):
        self.python_input = python_input
        self.output_dir = output_dir
        self.debug_save_responses = debug_save_responses
        
        # Handle backward compatibility
        if model_config is None and model_name is not None:
            self.model_config = ModelConfig(
                type="local",
                model_name_or_path=model_name
            )
        elif model_config is None:
            self.model_config = ModelConfig(
                type="local",
                model_name_or_path="nvidia/Nemotron-Research-Reasoning-Qwen-1.5B"
            )
        else:
            self.model_config = model_config
    
    def run(self) -> tuple[LeanCodeGenerationResult, LeanSpecGenerationResult]:
        """Run the LLM generation pipeline."""
        generator = LLMCodeSpecGenerator(
            model_config=self.model_config,
            debug_save_responses=self.debug_save_responses,
            debug_output_dir=self.output_dir / "debug" if self.output_dir else None
        )
        code_result, spec_result = generator.generate_full_pipeline(self.python_input)
        
        # Optionally save results to files
        if self.output_dir and code_result.success:
            self.output_dir.mkdir(parents=True, exist_ok=True)
            
            # Save generated Lean code
            code_file = self.output_dir / "generated_code.lean"
            code_file.write_text(code_result.lean_code)
            
            # Save generated spec if available
            if spec_result.success:
                spec_file = self.output_dir / "generated_spec.lean"
                spec_file.write_text(spec_result.lean_spec)
        
        return code_result, spec_result
