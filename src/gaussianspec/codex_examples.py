"""Examples and usage patterns for enhanced Codex integration.

This module demonstrates how to use the new Codex features including
voice mode, best-of-N sampling, and streaming in the GaussianSpec context.
"""

import asyncio
from pathlib import Path
from typing import List

from .codex_client import (
    CodexClient,
    CodexConfig,
    VoiceMode,
    CodexModel,
    create_default_codex_client,
    create_voice_enabled_client,
    create_best_of_n_client,
    create_streaming_client,
)
from .codex_subagent import (
    CodexGenerationSubagent,
    LeanProofGenerationSubagent,
    VoiceCodexSubagent,
    CodexEnhancedOCRSubagent,
    StreamingCodexSubagent,
)


async def example_basic_code_generation():
    """Example: Basic code generation with Codex."""
    
    client = create_default_codex_client()
    
    result = await client.generate_code(
        prompt="Write a Python function to compute the factorial of a number",
        system_prompt="You are a helpful Python programming assistant."
    )
    
    print("Generated Code:")
    print(result.text)
    print(f"Confidence: {result.confidence_score:.2f}")


async def example_best_of_n_generation():
    """Example: Best-of-N sampling for higher quality results."""
    
    client = create_best_of_n_client(n=5)
    
    result = await client.generate_code(
        prompt="Implement quicksort algorithm in Python with proper error handling",
        system_prompt="You are an expert algorithms programmer. Write clean, efficient code."
    )
    
    print("Best Result:")
    print(result.text)
    print(f"\nConfidence: {result.confidence_score:.2f}")
    print(f"Total samples generated: {len(result.samples)}")
    
    print("\nAll samples (ranked):")
    for i, (sample, rank) in enumerate(zip(result.samples, result.rankings)):
        print(f"\n--- Sample {i+1} (Score: {rank:.3f}) ---")
        print(sample[:200] + "..." if len(sample) > 200 else sample)


async def example_streaming_generation():
    """Example: Streaming code generation."""
    
    client = create_streaming_client()
    
    print("Streaming generation...")
    result = await client.generate_code(
        prompt="Create a comprehensive Python class for matrix operations",
        system_prompt="You are a numerical computing expert."
    )
    
    print("Final Result:")
    print(result.text)


async def example_lean_proof_generation():
    """Example: Generate Lean proofs using enhanced Codex."""
    
    problem = "Prove that the sum of two even numbers is even"
    formal_statement = """theorem sum_even_is_even (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) :="""
    
    subagent = LeanProofGenerationSubagent(
        problem_statement=problem,
        formal_statement=formal_statement,
        use_best_of_n=True,
        n_samples=3
    )
    
    result = subagent.run()
    
    if result.success:
        print("Generated Lean Proof:")
        print(f"{result.formal_statement}")
        print(result.proof_code)
        print(f"\nConfidence: {result.confidence_score:.2f}")
        
        if result.alternative_proofs:
            print(f"\nAlternative proofs generated: {len(result.alternative_proofs)}")
    else:
        print(f"Proof generation failed: {result.error}")


def example_voice_interaction():
    """Example: Voice-enabled Codex interaction."""
    
    try:
        # Create voice-enabled client
        client = create_voice_enabled_client()
        
        # Record audio (5 seconds)
        print("Recording audio for 5 seconds...")
        audio_data = client.record_audio(duration=5.0)
        
        # Process with voice subagent
        subagent = VoiceCodexSubagent(
            audio_input=audio_data,
            system_prompt="You are a helpful coding assistant. Respond concisely.",
            voice_mode=VoiceMode.BIDIRECTIONAL
        )
        
        result = subagent.run()
        
        if result.success:
            print(f"Transcribed: {result.transcribed_input}")
            print(f"Response: {result.generated_response}")
            
            if result.audio_response:
                print("Playing audio response...")
                client.play_audio(result.audio_response)
        else:
            print(f"Voice interaction failed: {result.error}")
            
    except Exception as e:
        print(f"Voice interaction not available: {e}")
        print("Install audio dependencies: uv add sounddevice soundfile numpy")


def example_ocr_enhancement():
    """Example: Enhance OCR results using Codex."""
    
    # Simulate OCR text with errors
    ocr_text = """
    Gaussain Elimnation Algoritm
    
    For a matrx A of siz n x n, the algorthm proceds as folows:
    1. Forr each row i from 1 to n:
       a) Find the pivt element
       b) Swap rows if necesary
       c) Elimnate entres below the pivt
    2. The resut is an uper triangular matrx
    """
    
    subagent = CodexEnhancedOCRSubagent(
        ocr_text=ocr_text,
        domain="mathematical",
        use_best_of_n=True
    )
    
    result = subagent.run()
    
    if result.success:
        print("Original OCR:")
        print(result.original_ocr)
        print("\nEnhanced Text:")
        print(result.processed_text)
        print(f"\nConfidence: {result.confidence_score:.2f}")
    else:
        print(f"OCR enhancement failed: {result.error}")


def example_subagent_integration():
    """Example: Integration with existing subagent pipeline."""
    
    # Generate code using subagent
    code_gen = CodexGenerationSubagent(
        prompt="Write a Python function to multiply two matrices",
        system_prompt="You are a numerical computing expert.",
        model=CodexModel.GPT_4O,
        temperature=0.5,
        best_of=3
    )
    
    result = code_gen.run()
    
    if result.success:
        print("Generated Code:")
        print(result.generated_code)
        print(f"Confidence: {result.confidence_score:.2f}")
        print(f"Samples generated: {len(result.samples) if result.samples else 1}")
        
        if result.usage:
            print(f"Tokens used: {result.usage}")
    else:
        print(f"Code generation failed: {result.error}")


async def example_gaussian_elimination_proof():
    """Example: Generate proof for Gaussian elimination using enhanced Codex."""
    
    problem = """
    Prove that Gaussian elimination produces the left inverse of a nonsingular matrix.
    Given a nonsingular square matrix A, show that the result of Gaussian elimination
    satisfies the property that GaussianElimination(A) * A = I.
    """
    
    formal_statement = """
    theorem gaussianElimination_is_left_inverse (A : Matrix n n ℝ) (h : IsNonsingular A) :
      gaussianElimination A * A = 1 :=
    """
    
    # Use best-of-N for this complex proof
    subagent = LeanProofGenerationSubagent(
        problem_statement=problem,
        formal_statement=formal_statement,
        use_best_of_n=True,
        n_samples=5,
        temperature=0.2,  # Lower temperature for mathematical proofs
        max_tokens=2048
    )
    
    result = subagent.run()
    
    if result.success:
        print("=== Gaussian Elimination Proof ===")
        print(f"Problem: {result.problem_statement}")
        print(f"\nFormal Statement:")
        print(result.formal_statement)
        print(f"\nGenerated Proof:")
        print(result.proof_code)
        print(f"\nConfidence Score: {result.confidence_score:.3f}")
        
        if result.alternative_proofs:
            print(f"\n=== Alternative Approaches ({len(result.alternative_proofs)}) ===")
            for i, alt_proof in enumerate(result.alternative_proofs[:2], 1):
                print(f"\n--- Alternative {i} ---")
                print(alt_proof[:300] + "..." if len(alt_proof) > 300 else alt_proof)
    else:
        print(f"Proof generation failed: {result.error}")


def main():
    """Run all examples."""
    
    print("=== Enhanced OpenAI Codex Examples ===\n")
    
    # Basic examples
    print("1. Basic Code Generation")
    asyncio.run(example_basic_code_generation())
    
    print("\n" + "="*50 + "\n")
    
    print("2. Best-of-N Generation")
    asyncio.run(example_best_of_n_generation())
    
    print("\n" + "="*50 + "\n")
    
    print("3. Streaming Generation")
    asyncio.run(example_streaming_generation())
    
    print("\n" + "="*50 + "\n")
    
    print("4. Lean Proof Generation")
    asyncio.run(example_lean_proof_generation())
    
    print("\n" + "="*50 + "\n")
    
    print("5. Voice Interaction (requires audio setup)")
    example_voice_interaction()
    
    print("\n" + "="*50 + "\n")
    
    print("6. OCR Enhancement")
    example_ocr_enhancement()
    
    print("\n" + "="*50 + "\n")
    
    print("7. Subagent Integration")
    example_subagent_integration()
    
    print("\n" + "="*50 + "\n")
    
    print("8. Gaussian Elimination Proof (Project-Specific)")
    asyncio.run(example_gaussian_elimination_proof())


if __name__ == "__main__":
    main()