"""
Tests for unified model deployment system.
"""

import pytest
import json
# import requests_mock  # Optional dependency for API testing
from unittest.mock import patch, MagicMock
from pathlib import Path
from gaussianspec.model_deployment import (
    ModelDeployment,
    ModelConfig,
    LocalModelInterface,
    APIModelInterface,
    create_local_deployment,
    create_api_deployment,
    create_openai_deployment,
    create_anthropic_deployment,
)


class TestModelConfig:
    """Test model configuration."""
    
    def test_model_config_creation(self):
        """Test creating model configurations."""
        # Local model config
        local_config = ModelConfig(
            type="local",
            model_name_or_path="test-model",
            max_tokens=256,
            temperature=0.5
        )
        assert local_config.type == "local"
        assert local_config.model_name_or_path == "test-model"
        assert local_config.max_tokens == 256
        
        # API model config
        api_config = ModelConfig(
            type="api",
            api_key="test-key",
            url="https://api.test.com",
            model_type="openai",
            temperature=0.7
        )
        assert api_config.type == "api"
        assert api_config.api_key == "test-key"
        assert api_config.model_type == "openai"


def test_create_local_deployment():
    """Test creating local deployment."""
    deployment = create_local_deployment("test-model", temperature=0.5)
    assert deployment.config.type == "local"
    assert deployment.config.model_name_or_path == "test-model"
    assert deployment.config.temperature == 0.5


def test_create_openai_deployment():
    """Test creating OpenAI deployment."""
    deployment = create_openai_deployment("test-key", temperature=0.8)
    assert deployment.config.type == "api"
    assert deployment.config.api_key == "test-key"
    assert deployment.config.url == "https://api.openai.com/v1/chat/completions"
    assert deployment.config.model_type == "openai"
    assert deployment.config.temperature == 0.8


if __name__ == "__main__":
    pytest.main([__file__])
