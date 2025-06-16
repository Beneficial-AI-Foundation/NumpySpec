"""
Tests for LLM-based Lean code and spec generation.
"""

import pytest
from pathlib import Path
from gaussianspec.llm_generator import (
    LLMCodeSpecGenerator,
    LLMCodeSpecSubagent,
    LeanCodeGenerationResult,
    LeanSpecGenerationResult,
)
from gaussianspec.model_deployment import ModelConfig, create_openai_deployment


def test_llm_generator_basic():
    """Test basic functionality of LLM code/spec generator."""
    # Simple Python input for testing
    python_input = """
def add(a: int, b: int) -> int:
    '''Add two integers.'''
    return a + b
"""
    
    generator = LLMCodeSpecGenerator()
    
    # Test code generation
    code_result = generator.generate_lean_code(python_input)
    assert isinstance(code_result, LeanCodeGenerationResult)
    
    # Test spec generation (using dummy Lean code if model not available)
    if code_result.success:
        spec_result = generator.generate_lean_spec(code_result.lean_code)
    else:
        # Use dummy Lean code for testing when model unavailable
        dummy_lean = "def add (a b : Nat) : Nat := a + b"
        spec_result = generator.generate_lean_spec(dummy_lean)
    
    assert isinstance(spec_result, LeanSpecGenerationResult)


def test_llm_generator_full_pipeline():
    """Test the full pipeline: Python -> Lean code -> Lean spec."""
    python_input = """
def factorial(n: int) -> int:
    '''Calculate factorial of n.'''
    if n <= 1:
        return 1
    return n * factorial(n - 1)
"""
    
    generator = LLMCodeSpecGenerator()
    code_result, spec_result = generator.generate_full_pipeline(python_input)
    
    assert isinstance(code_result, LeanCodeGenerationResult)
    assert isinstance(spec_result, LeanSpecGenerationResult)
    
    # If code generation fails (e.g., model not available), spec should also indicate failure
    if not code_result.success:
        assert not spec_result.success


def test_llm_subagent(tmp_path):
    """Test the LLM subagent interface."""
    python_input = """
def square(x: int) -> int:
    '''Return the square of x.'''
    return x * x
"""
    
    subagent = LLMCodeSpecSubagent(
        python_input=python_input,
        output_dir=tmp_path
    )
    
    code_result, spec_result = subagent.run()
    
    assert isinstance(code_result, LeanCodeGenerationResult)
    assert isinstance(spec_result, LeanSpecGenerationResult)
    
    # Check that files are created if generation succeeds
    if code_result.success:
        code_file = tmp_path / "generated_code.lean"
        assert code_file.exists()
        assert len(code_file.read_text()) > 0
        
        if spec_result.success:
            spec_file = tmp_path / "generated_spec.lean"
            assert spec_file.exists()
            assert len(spec_file.read_text()) > 0


def test_prompt_building():
    """Test prompt building functions."""
    generator = LLMCodeSpecGenerator()
    
    python_code = "def test(): pass"
    code_prompt = generator._build_code_generation_prompt(python_code)
    
    assert "Python code:" in code_prompt
    assert python_code in code_prompt
    assert "[[OUTPUT]]" in code_prompt
    
    lean_code = "def test : Unit := ()"
    spec_prompt = generator._build_spec_generation_prompt(lean_code)
    
    assert "Lean implementation:" in spec_prompt
    assert lean_code in spec_prompt
    assert "[[OUTPUT]]" in spec_prompt


def test_extraction_functions():
    """Test code and spec extraction from model completions."""
    generator = LLMCodeSpecGenerator()
    
    # Test code extraction with new format
    completion_with_markers = "Some thinking here\n[[OUTPUT]]def add (a b : Nat) : Nat := a + b[[\\OUTPUT]]\nSome explanation"
    extracted = generator._extract_lean_code(completion_with_markers)
    assert "def add (a b : Nat) : Nat := a + b" in extracted
    assert "Some explanation" not in extracted
    
    # Test fallback to old format
    completion_with_fence = "def add (a b : Nat) : Nat := a + b\n```\nSome explanation"
    extracted_old = generator._extract_lean_code(completion_with_fence)
    assert "def add (a b : Nat) : Nat := a + b" in extracted_old
    
    # Test spec extraction with new format
    spec_completion = "Some analysis\n[[OUTPUT]]theorem add_comm : add a b = add b a := by sorry[[\\OUTPUT]]"
    extracted_spec = generator._extract_lean_spec(spec_completion)
    assert "theorem add_comm" in extracted_spec


def test_llm_generator_with_local_model():
    """Test LLM generator with explicit local model configuration."""
    python_input = """
def multiply(a: int, b: int) -> int:
    '''Multiply two integers.'''
    return a * b
"""
    
    # Test with local model config
    local_config = ModelConfig(
        type="local",
        model_name_or_path="sshleifer/tiny-gpt2",  # Use small model for testing
        max_tokens=64,
        temperature=0.1
    )
    
    generator = LLMCodeSpecGenerator(model_config=local_config)
    code_result = generator.generate_lean_code(python_input)
    
    assert isinstance(code_result, LeanCodeGenerationResult)
    # The result may fail if model is not available, which is expected in test environment


def test_llm_generator_with_api_model():
    """Test LLM generator with API model configuration."""
    python_input = """
def divide(a: int, b: int) -> float:
    '''Divide two numbers.'''
    return a / b
"""
    
    # Test with API model config (this will fail without real API key, which is expected)
    api_config = ModelConfig(
        type="api",
        api_key="test-key",
        url="https://api.openai.com/v1/chat/completions",
        model_type="openai",
        max_tokens=64,
        temperature=0.1
    )
    
    generator = LLMCodeSpecGenerator(model_config=api_config)
    code_result = generator.generate_lean_code(python_input)
    
    assert isinstance(code_result, LeanCodeGenerationResult)
    # The result will fail without valid API key, which is expected in test environment


def test_llm_generator_backward_compatibility():
    """Test that old interface still works (backward compatibility)."""
    python_input = """
def power(base: int, exp: int) -> int:
    '''Calculate base raised to the power of exp.'''
    return base ** exp
"""
    
    # Test old interface with just model_name
    generator = LLMCodeSpecGenerator(model_name="sshleifer/tiny-gpt2")
    code_result = generator.generate_lean_code(python_input)
    
    assert isinstance(code_result, LeanCodeGenerationResult)


def test_llm_subagent_with_config():
    """Test subagent with model configuration."""
    python_input = """
def absolute(x: int) -> int:
    '''Return absolute value.'''
    return abs(x)
"""
    
    # Test with model config
    config = ModelConfig(
        type="local",
        model_name_or_path="sshleifer/tiny-gpt2",
        max_tokens=32
    )
    
    subagent = LLMCodeSpecSubagent(
        python_input=python_input,
        model_config=config
    )
    
    code_result, spec_result = subagent.run()
    
    assert isinstance(code_result, LeanCodeGenerationResult)
    assert isinstance(spec_result, LeanSpecGenerationResult)


def test_deployment_integration_demo():
    """Demonstrate how to use different deployment types."""
    python_input = "def demo(): return 42"
    
    # Local deployment example
    local_config = {
        "type": "local",
        "model_name_or_path": "sshleifer/tiny-gpt2",
        "max_tokens": 32,
        "temperature": 0.1
    }
    
    generator_local = LLMCodeSpecGenerator(model_config=local_config)
    assert generator_local.model_config.type == "local"
    
    # API deployment example (for demonstration - will fail without real key)
    api_config = {
        "type": "api",
        "api_key": "dummy-key-for-testing",
        "url": "https://api.openai.com/v1/chat/completions",
        "model_type": "openai",
        "max_tokens": 64
    }
    
    generator_api = LLMCodeSpecGenerator(model_config=api_config)
    assert generator_api.model_config.type == "api"
    assert generator_api.model_config.model_type == "openai"


if __name__ == "__main__":
    pytest.main([__file__])
