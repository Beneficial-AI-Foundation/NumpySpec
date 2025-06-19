#!/usr/bin/env python3
"""Test script for the new OpenAI Codex integration.

This script tests the three main features:
1. Voice mode support
2. Online setup functionality  
3. Best of N feature

Run this script to validate the Codex setup works correctly.
"""

import os
import sys
from pathlib import Path

# Add src to path for testing
sys.path.insert(0, str(Path(__file__).parent / "src"))

from gaussianspec.codex_utils import (
    setup_codex_environment,
    CodexClient,
    VoiceMode,
    OnlineCodexSetup,
    best_of_n_completion,
)
from gaussianspec.agent import (
    create_lean_edit_with_codex,
    enhanced_proof_generation,
    setup_online_codex_assistant,
)


def test_environment_setup():
    """Test that the Codex environment is properly configured."""
    print("=== Testing Codex Environment Setup ===")
    
    status = setup_codex_environment()
    print(f"OpenAI available: {status['openai_available']}")
    print(f"Speech recognition available: {status['speech_recognition_available']}")
    print(f"API key configured: {status['api_key_configured']}")
    print(f"Available features: {status['features']}")
    
    return status


def test_basic_codex_completion():
    """Test basic Codex code completion."""
    print("\n=== Testing Basic Codex Completion ===")
    
    try:
        client = CodexClient()
        completion = client.complete_lean_code(
            prompt="theorem simple_add (a b : ℕ) : a + b = b + a := ",
            context="Prove commutativity of natural number addition"
        )
        
        print(f"✓ Basic completion successful")
        print(f"Generated: {completion.text[:100]}...")
        print(f"Tokens used: {completion.tokens_used}")
        return True
        
    except Exception as e:
        print(f"✗ Basic completion failed: {e}")
        return False


def test_best_of_n():
    """Test the best-of-n completion feature."""
    print("\n=== Testing Best-of-N Feature ===")
    
    try:
        client = CodexClient()
        completions = best_of_n_completion(
            client=client,
            prompt="theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := ",
            n=2,
            context="Prove associativity of addition",
            selection_criteria="shortest_valid"
        )
        
        print(f"✓ Generated {len(completions)} completions")
        for i, comp in enumerate(completions):
            print(f"  {i+1}: {comp.text[:50]}... (tokens: {comp.tokens_used})")
        
        return len(completions) > 0
        
    except Exception as e:
        print(f"✗ Best-of-N failed: {e}")
        return False


def test_online_setup():
    """Test the online Codex setup."""
    print("\n=== Testing Online Setup ===")
    
    try:
        client = CodexClient()
        online_setup = OnlineCodexSetup(client, auto_complete=True)
        
        # Test getting completions for a code snippet
        test_code = """theorem test_theorem (n : ℕ) : n + 0 = n := 
by """
        
        completions = online_setup.get_completions(
            current_code=test_code,
            cursor_position=len(test_code),
            n_suggestions=2
        )
        
        print(f"✓ Online setup working, got {len(completions)} suggestions")
        for i, comp in enumerate(completions):
            print(f"  Suggestion {i+1}: {comp.text[:30]}...")
        
        return True
        
    except Exception as e:
        print(f"✗ Online setup failed: {e}")
        return False


def test_voice_mode_availability():
    """Test if voice mode is available (without actually using microphone)."""
    print("\n=== Testing Voice Mode Availability ===")
    
    try:
        # Just test if we can instantiate VoiceMode
        voice_mode = VoiceMode()
        print("✓ Voice mode available")
        print("  Note: Actual voice testing requires microphone and manual interaction")
        return True
        
    except Exception as e:
        print(f"✗ Voice mode not available: {e}")
        print("  Install with: uv add speechrecognition pyaudio")
        return False


def test_agent_integration():
    """Test the integration with the main agent module."""
    print("\n=== Testing Agent Integration ===")
    
    try:
        # Test enhanced proof generation
        proof = enhanced_proof_generation(
            theorem_statement="theorem mul_comm (a b : ℕ) : a * b = b * a := ",
            context="Prove commutativity of multiplication",
            methods=["codex"],  # Only test Codex to avoid HF model loading
            use_best_of_n=True
        )
        
        print("✓ Enhanced proof generation working")
        print(f"Generated proof: {proof[:100]}...")
        
        # Test online assistant setup
        project_root = Path(__file__).parent
        assistant = setup_online_codex_assistant(project_root)
        
        if assistant:
            print("✓ Online assistant setup successful")
        else:
            print("⚠ Online assistant setup returned None")
        
        return True
        
    except Exception as e:
        print(f"✗ Agent integration failed: {e}")
        return False


def main():
    """Run all tests."""
    print("OpenAI Codex Integration Test Suite")
    print("=" * 50)
    
    # Check if API key is available
    if not os.getenv("OPENAI_API_KEY"):
        print("⚠ Warning: OPENAI_API_KEY not set. Some tests will fail.")
        print("Set your API key: export OPENAI_API_KEY='your-key-here'")
        print()
    
    # Run tests
    tests = [
        test_environment_setup,
        test_basic_codex_completion,
        test_best_of_n,
        test_online_setup,
        test_voice_mode_availability,
        test_agent_integration,
    ]
    
    results = []
    for test in tests:
        try:
            result = test()
            results.append(result)
        except Exception as e:
            print(f"Test {test.__name__} crashed: {e}")
            results.append(False)
    
    # Summary
    print("\n" + "=" * 50)
    print("Test Summary:")
    passed = sum(1 for r in results if r)
    total = len(results)
    print(f"Passed: {passed}/{total}")
    
    if passed == total:
        print("🎉 All tests passed! Codex integration is working correctly.")
    else:
        print("⚠ Some tests failed. Check the output above for details.")
    
    return passed == total


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)