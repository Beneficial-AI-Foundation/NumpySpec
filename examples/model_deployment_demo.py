#!/usr/bin/env python3
"""
Demo script showing how to use the unified model deployment system
with both local and API models.

Run this script to see examples of:
1. Using local models (HuggingFace transformers)
2. Using API models (OpenAI, Anthropic, etc.)
3. Integrating with the LLM generator for Lean code generation

Usage:
    python model_deployment_demo.py --model-type local
    python model_deployment_demo.py --model-type api --api-key YOUR_API_KEY
"""

import argparse
import sys
from pathlib import Path

# Add src to path for development
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

from gaussianspec.model_deployment import (
    ModelDeployment,
    ModelConfig,
    create_local_deployment,
    create_openai_deployment,
    create_anthropic_deployment,
)
from gaussianspec.llm_generator import LLMCodeSpecGenerator


def demo_local_model():
    """Demonstrate local model deployment."""
    print("=== Local Model Deployment Demo ===")
    
    # Create local model deployment
    print("Creating local model deployment...")
    deployment = create_local_deployment(
        model_name_or_path="sshleifer/tiny-gpt2",  # Small model for demo
        temperature=0.1,
        max_tokens=64
    )
    
    print(f"Model info: {deployment.get_info()}")
    
    if deployment.is_available():
        print("✓ Model loaded successfully")
        
        # Test generation
        prompt = "Hello, world!"
        try:
            result = deployment.generate(prompt)
            print(f"Generated text: {result[:100]}...")
        except Exception as e:
            print(f"Generation failed: {e}")
    else:
        print("✗ Model not available (transformers/torch may not be installed)")
    
    print()


def demo_api_model(api_key: str, model_type: str = "openai"):
    """Demonstrate API model deployment."""
    print(f"=== {model_type.title()} API Model Deployment Demo ===")
    
    # Create API model deployment
    print(f"Creating {model_type} API deployment...")
    if model_type == "openai":
        deployment = create_openai_deployment(
            api_key=api_key,
            temperature=0.1,
            max_tokens=64
        )
    elif model_type == "anthropic":
        deployment = create_anthropic_deployment(
            api_key=api_key,
            temperature=0.1,
            max_tokens=64
        )
    else:
        print(f"Unknown API model type: {model_type}")
        return
    
    print(f"Model info: {deployment.get_info()}")
    
    if deployment.is_available():
        print("✓ API model configured successfully")
        
        # Test generation
        prompt = "Explain what is machine learning in one sentence."
        try:
            result = deployment.generate(prompt)
            print(f"Generated text: {result}")
        except Exception as e:
            print(f"API generation failed: {e}")
    else:
        print("✗ API model not properly configured")
    
    print()


def demo_llm_generator_integration(model_config):
    """Demonstrate integration with LLM generator."""
    print("=== LLM Generator Integration Demo ===")
    
    # Create LLM generator with specific model config
    generator = LLMCodeSpecGenerator(model_config=model_config)
    
    # Sample Python code to translate
    python_code = """
def fibonacci(n: int) -> int:
    '''Calculate the nth Fibonacci number.'''
    if n <= 1:
        return n
    return fibonacci(n-1) + fibonacci(n-2)
"""
    
    print("Translating Python code to Lean...")
    print(f"Input Python code:{python_code}")
    
    # Generate Lean code
    code_result = generator.generate_lean_code(python_code)
    
    if code_result.success:
        print("✓ Lean code generation successful:")
        print(f"Generated Lean code:\n{code_result.lean_code}")
        
        # Generate specification
        print("\nGenerating Lean specification...")
        spec_result = generator.generate_lean_spec(code_result.lean_code)
        
        if spec_result.success:
            print("✓ Lean spec generation successful:")
            print(f"Generated Lean spec:\n{spec_result.lean_spec}")
        else:
            print(f"✗ Lean spec generation failed: {spec_result.error}")
    else:
        print(f"✗ Lean code generation failed: {code_result.error}")
    
    print()


def demo_config_file_operations(tmp_dir: Path):
    """Demonstrate saving and loading model configurations."""
    print("=== Configuration File Operations Demo ===")
    
    # Create a model configuration
    config = ModelConfig(
        type="local",
        model_name_or_path="test-model",
        temperature=0.7,
        max_tokens=256,
        top_p=0.9
    )
    
    deployment = ModelDeployment(config)
    
    # Save configuration to file
    config_file = tmp_dir / "model_config.json"
    deployment.save_config(config_file)
    print(f"✓ Configuration saved to: {config_file}")
    
    # Load configuration from file
    loaded_deployment = ModelDeployment.from_config_file(config_file)
    print(f"✓ Configuration loaded from file")
    print(f"Loaded config: {loaded_deployment.get_info()}")
    
    print()


def main():
    parser = argparse.ArgumentParser(description="Model Deployment Demo")
    parser.add_argument(
        "--model-type", 
        choices=["local", "api"], 
        default="local",
        help="Type of model to demo"
    )
    parser.add_argument(
        "--api-provider",
        choices=["openai", "anthropic"],
        default="openai",
        help="API provider for API models"
    )
    parser.add_argument(
        "--api-key",
        help="API key for API models"
    )
    parser.add_argument(
        "--skip-generation",
        action="store_true",
        help="Skip actual model generation (for testing config only)"
    )
    
    args = parser.parse_args()
    
    print("🚀 Model Deployment System Demo")
    print("=" * 50)
    
    if args.model_type == "local":
        demo_local_model()
        
        if not args.skip_generation:
            # Demo integration with local model
            local_config = ModelConfig(
                type="local",
                model_name_or_path="sshleifer/tiny-gpt2",
                temperature=0.1,
                max_tokens=32
            )
            demo_llm_generator_integration(local_config)
    
    elif args.model_type == "api":
        if not args.api_key:
            print("❌ API key required for API model demo")
            print("Use --api-key YOUR_API_KEY")
            return
        
        demo_api_model(args.api_key, args.api_provider)
        
        if not args.skip_generation:
            # Demo integration with API model
            if args.api_provider == "openai":
                api_config = ModelConfig(
                    type="api",
                    api_key=args.api_key,
                    url="https://api.openai.com/v1/chat/completions",
                    model_type="openai",
                    temperature=0.1,
                    max_tokens=64
                )
            else:  # anthropic
                api_config = ModelConfig(
                    type="api",
                    api_key=args.api_key,
                    url="https://api.anthropic.com/v1/messages",
                    model_type="anthropic",
                    temperature=0.1,
                    max_tokens=64
                )
            
            demo_llm_generator_integration(api_config)
    
    # Demo config file operations
    from tempfile import TemporaryDirectory
    with TemporaryDirectory() as tmp_dir:
        demo_config_file_operations(Path(tmp_dir))
    
    print("✅ Demo completed!")
    
    # Print usage examples
    print("\n📚 Usage Examples:")
    print("================")
    print("# Local model usage in your code:")
    print("from gaussianspec.model_deployment import create_local_deployment")
    print("deployment = create_local_deployment('your-model-name')")
    print("result = deployment.generate('your prompt')")
    print()
    print("# API model usage in your code:")
    print("from gaussianspec.model_deployment import create_openai_deployment")
    print("deployment = create_openai_deployment('your-api-key')")
    print("result = deployment.generate('your prompt')")
    print()
    print("# LLM Generator usage:")
    print("from gaussianspec.llm_generator import LLMCodeSpecGenerator")
    print("from gaussianspec.model_deployment import ModelConfig")
    print("config = ModelConfig(type='local', model_name_or_path='your-model')")
    print("generator = LLMCodeSpecGenerator(model_config=config)")
    print("code_result = generator.generate_lean_code('def add(a, b): return a + b')")


if __name__ == "__main__":
    main()
