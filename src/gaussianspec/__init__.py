"""
GaussianSpec: Enhanced AI-driven Lean 4 formal verification platform.

Features:
- MorphCloud-driven Lean agent system
- Enhanced OpenAI Codex integration with voice mode, best-of-N sampling, and streaming
- OCR preprocessing with AI enhancement
- Reinforcement learning environment for theorem proving
"""

from .rl_env import LeanEnv, EditLibrary

# Enhanced Codex exports
from .codex_client import (
    CodexClient,
    CodexConfig,
    CodexResult,
    VoiceResult,
    CodexModel,
    VoiceMode,
    create_default_codex_client,
    create_voice_enabled_client,
    create_best_of_n_client,
    create_streaming_client,
)

from .codex_subagent import (
    CodexGenerationSubagent,
    CodexGenerationResult,
    LeanProofGenerationSubagent,
    LeanProofGenerationResult,
    VoiceCodexSubagent,
    VoiceCodexResult,
    CodexEnhancedOCRSubagent,
    CodexEnhancedOCRResult,
    StreamingCodexSubagent,
    StreamingCodexResult,
)

# Auto-load environment variables from a local .env if present
try:
    from pathlib import Path
    from dotenv import load_dotenv

    env_path = Path(__file__).resolve().parent.parent.parent / ".env"
    if env_path.exists():
        load_dotenv(dotenv_path=env_path)  # type: ignore[call-arg]
except ModuleNotFoundError:
    # python-dotenv is optional; skip if absent
    pass

__all__ = [
    # Core RL environment
    "LeanEnv",
    "EditLibrary",
    
    # Enhanced Codex client
    "CodexClient",
    "CodexConfig", 
    "CodexResult",
    "VoiceResult",
    "CodexModel",
    "VoiceMode",
    "create_default_codex_client",
    "create_voice_enabled_client", 
    "create_best_of_n_client",
    "create_streaming_client",
    
    # Enhanced Codex subagents
    "CodexGenerationSubagent",
    "CodexGenerationResult",
    "LeanProofGenerationSubagent", 
    "LeanProofGenerationResult",
    "VoiceCodexSubagent",
    "VoiceCodexResult",
    "CodexEnhancedOCRSubagent",
    "CodexEnhancedOCRResult", 
    "StreamingCodexSubagent",
    "StreamingCodexResult",
]


def main() -> None:
    """Main entry point for gaussianspec."""
    print("GaussianSpec: Enhanced AI-driven Lean 4 formal verification platform")
    print("Features: Codex integration, voice mode, best-of-N sampling, streaming generation")
    
    # Display available Codex models
    print("\nAvailable Codex models:")
    for model in CodexModel:
        print(f"  - {model.value}")
    
    print("\nFor usage examples, see: src/gaussianspec/codex_examples.py")
    print("For setup guide, see: docs/codex-setup.md")
