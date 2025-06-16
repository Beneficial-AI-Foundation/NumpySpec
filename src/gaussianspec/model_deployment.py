"""
Unified model deployment system supporting both local and API models.

This module provides a unified interface for deploying models either locally
via HuggingFace transformers or through API endpoints (OpenAI, Anthropic, etc.).

Example usage:
    # Local model
    deployment = ModelDeployment({
        "type": "local",
        "model_name_or_path": "nvidia/Nemotron-Research-Reasoning-Qwen-1.5B"
    })
    
    # API model
    deployment = ModelDeployment({
        "type": "api",
        "api_key": "your-api-key",
        "url": "https://api.openai.com/v1/chat/completions",
        "model_type": "openai"
    })
"""

from __future__ import annotations
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Dict, Any, Optional, Union, List
import json
import requests
from pathlib import Path

try:
    from .hf_utils import load_model, generate
    from transformers import AutoModelForCausalLM, AutoTokenizer
except ImportError:
    # Handle optional dependencies
    load_model = None
    generate = None
    AutoModelForCausalLM = None
    AutoTokenizer = None


@dataclass
class ModelConfig:
    """Configuration for model deployment."""
    type: str  # "local" or "api"
    model_name_or_path: Optional[str] = None  # For local models
    api_key: Optional[str] = None  # For API models
    url: Optional[str] = None  # For API models
    model_type: Optional[str] = None  # "openai", "anthropic", "custom"
    
    # Generation parameters
    max_tokens: int = 512
    temperature: float = 0.2
    top_p: float = 0.9
    
    # Local model specific
    dtype: Optional[str] = None
    device: Optional[str] = None
    trust_remote_code: bool = True
    
    # API model specific
    timeout: int = 30
    max_retries: int = 3


class ModelInterface(ABC):
    """Abstract interface for model deployment."""
    
    @abstractmethod
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate text from prompt."""
        pass
    
    @abstractmethod
    def is_available(self) -> bool:
        """Check if model is available and ready."""
        pass
    
    @abstractmethod
    def get_info(self) -> Dict[str, Any]:
        """Get model information."""
        pass


class LocalModelInterface(ModelInterface):
    """Interface for local HuggingFace models."""
    
    def __init__(self, config: ModelConfig):
        self.config = config
        self._model = None
        self._tokenizer = None
        self._load_error = None
        
        if load_model is None:
            self._load_error = "transformers/torch not available"
            return
        
        try:
            dtype = None
            if config.dtype:
                import torch
                dtype = getattr(torch, config.dtype, None)
            
            self._model, self._tokenizer = load_model(
                config.model_name_or_path,
                dtype=dtype,
                device=config.device,
                trust_remote_code=config.trust_remote_code
            )
        except Exception as e:
            self._load_error = str(e)
    
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate text using local model."""
        if not self.is_available():
            raise RuntimeError(f"Model not available: {self._load_error}")
        
        # Merge config defaults with kwargs
        gen_kwargs = {
            "max_new_tokens": kwargs.get("max_tokens", self.config.max_tokens),
            "temperature": kwargs.get("temperature", self.config.temperature),
            "top_p": kwargs.get("top_p", self.config.top_p),
            "do_sample": True
        }
        
        return generate(self._model, self._tokenizer, prompt, **gen_kwargs)
    
    def is_available(self) -> bool:
        """Check if local model is loaded and ready."""
        return self._model is not None and self._tokenizer is not None
    
    def get_info(self) -> Dict[str, Any]:
        """Get local model information."""
        return {
            "type": "local",
            "model_name": self.config.model_name_or_path,
            "available": self.is_available(),
            "error": self._load_error
        }


class APIModelInterface(ModelInterface):
    """Interface for API-based models (OpenAI, Anthropic, etc.)."""
    
    def __init__(self, config: ModelConfig):
        self.config = config
        self._session = requests.Session()
        self._session.headers.update({
            "Content-Type": "application/json"
        })
        
        # Set up authentication based on model type
        if config.model_type == "openai":
            self._session.headers["Authorization"] = f"Bearer {config.api_key}"
        elif config.model_type == "anthropic":
            self._session.headers["x-api-key"] = config.api_key
        else:
            # For custom APIs, assume bearer token
            self._session.headers["Authorization"] = f"Bearer {config.api_key}"
    
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate text using API model."""
        if not self.is_available():
            raise RuntimeError("API model not properly configured")
        
        # Build request payload based on model type
        payload = self._build_payload(prompt, **kwargs)
        
        # Make API request with retries
        for attempt in range(self.config.max_retries):
            try:
                response = self._session.post(
                    self.config.url,
                    json=payload,
                    timeout=self.config.timeout
                )
                response.raise_for_status()
                return self._extract_response(response.json())
            except Exception as e:
                if attempt == self.config.max_retries - 1:
                    raise RuntimeError(f"API request failed after {self.config.max_retries} attempts: {e}")
                continue
    
    def _build_payload(self, prompt: str, **kwargs) -> Dict[str, Any]:
        """Build API request payload based on model type."""
        max_tokens = kwargs.get("max_tokens", self.config.max_tokens)
        temperature = kwargs.get("temperature", self.config.temperature)
        top_p = kwargs.get("top_p", self.config.top_p)
        
        if self.config.model_type == "openai":
            return {
                "model": kwargs.get("model", "gpt-3.5-turbo"),
                "messages": [{"role": "user", "content": prompt}],
                "max_tokens": max_tokens,
                "temperature": temperature,
                "top_p": top_p
            }
        elif self.config.model_type == "anthropic":
            return {
                "model": kwargs.get("model", "claude-3-haiku-20240307"),
                "max_tokens": max_tokens,
                "temperature": temperature,
                "top_p": top_p,
                "messages": [{"role": "user", "content": prompt}]
            }
        else:
            # Generic API format
            return {
                "prompt": prompt,
                "max_tokens": max_tokens,
                "temperature": temperature,
                "top_p": top_p
            }
    
    def _extract_response(self, response_data: Dict[str, Any]) -> str:
        """Extract generated text from API response."""
        if self.config.model_type == "openai":
            return response_data["choices"][0]["message"]["content"]
        elif self.config.model_type == "anthropic":
            return response_data["content"][0]["text"]
        else:
            # Try common response formats
            if "choices" in response_data:
                return response_data["choices"][0].get("text", "")
            elif "content" in response_data:
                return response_data["content"]
            elif "text" in response_data:
                return response_data["text"]
            else:
                raise ValueError(f"Unknown response format: {response_data}")
    
    def is_available(self) -> bool:
        """Check if API model is properly configured."""
        return (
            self.config.api_key is not None and
            self.config.url is not None and
            self.config.model_type is not None
        )
    
    def get_info(self) -> Dict[str, Any]:
        """Get API model information."""
        return {
            "type": "api",
            "model_type": self.config.model_type,
            "url": self.config.url,
            "available": self.is_available()
        }


class ModelDeployment:
    """Unified model deployment interface."""
    
    def __init__(self, config: Union[Dict[str, Any], ModelConfig]):
        """Initialize model deployment.
        
        Args:
            config: Model configuration dict or ModelConfig object
        """
        if isinstance(config, dict):
            self.config = ModelConfig(**config)
        else:
            self.config = config
        
        # Create appropriate interface based on type
        if self.config.type == "local":
            self.interface = LocalModelInterface(self.config)
        elif self.config.type == "api":
            self.interface = APIModelInterface(self.config)
        else:
            raise ValueError(f"Unknown model type: {self.config.type}")
    
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate text from prompt."""
        return self.interface.generate(prompt, **kwargs)
    
    def is_available(self) -> bool:
        """Check if model is available."""
        return self.interface.is_available()
    
    def get_info(self) -> Dict[str, Any]:
        """Get model information."""
        return self.interface.get_info()
    
    @classmethod
    def from_config_file(cls, config_path: Union[str, Path]) -> "ModelDeployment":
        """Load model deployment from configuration file."""
        config_path = Path(config_path)
        with open(config_path) as f:
            config_data = json.load(f)
        return cls(config_data)
    
    def save_config(self, config_path: Union[str, Path]) -> None:
        """Save model configuration to file."""
        config_path = Path(config_path)
        config_dict = {
            "type": self.config.type,
            "model_name_or_path": self.config.model_name_or_path,
            "api_key": self.config.api_key,
            "url": self.config.url,
            "model_type": self.config.model_type,
            "max_tokens": self.config.max_tokens,
            "temperature": self.config.temperature,
            "top_p": self.config.top_p,
            "dtype": self.config.dtype,
            "device": self.config.device,
            "trust_remote_code": self.config.trust_remote_code,
            "timeout": self.config.timeout,
            "max_retries": self.config.max_retries
        }
        
        with open(config_path, 'w') as f:
            json.dump(config_dict, f, indent=2)


# Convenience functions for common use cases
def create_local_deployment(
    model_name_or_path: str,
    **kwargs
) -> ModelDeployment:
    """Create a local model deployment."""
    config = ModelConfig(
        type="local",
        model_name_or_path=model_name_or_path,
        **kwargs
    )
    return ModelDeployment(config)


def create_api_deployment(
    api_key: str,
    url: str,
    model_type: str,
    **kwargs
) -> ModelDeployment:
    """Create an API model deployment."""
    config = ModelConfig(
        type="api",
        api_key=api_key,
        url=url,
        model_type=model_type,
        **kwargs
    )
    return ModelDeployment(config)


def create_openai_deployment(api_key: str, **kwargs) -> ModelDeployment:
    """Create an OpenAI API deployment."""
    return create_api_deployment(
        api_key=api_key,
        url="https://api.openai.com/v1/chat/completions",
        model_type="openai",
        **kwargs
    )


def create_anthropic_deployment(api_key: str, **kwargs) -> ModelDeployment:
    """Create an Anthropic API deployment."""
    return create_api_deployment(
        api_key=api_key,
        url="https://api.anthropic.com/v1/messages",
        model_type="anthropic",
        **kwargs
    )
