import os
import pytest

from specdraft.models import load_model

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _validate_outputs(outputs):
    """Basic sanity checks on the generation result list."""
    assert isinstance(outputs, list), "Outputs must be a list"
    assert outputs, "Outputs list is empty"
    for item in outputs:
        assert isinstance(item, str), "Each output must be a string"
        assert item.strip(), "Output string is blank"

# ---------------------------------------------------------------------------
# Tests – local model (HuggingFace)
# ---------------------------------------------------------------------------

@pytest.mark.slow
def test_local_gpt2_generation():
    """Ensure that the local GPT-2 model can be loaded and generate text."""
    cfg = {
        "type": "local",
        "model_name": "gpt2",  # small ~500 MB download
        "generate_kwargs": {"max_new_tokens": 8, "do_sample": False},
    }

    generate = load_model(cfg)
    outputs = generate("You are a test assistant.", ["Hello there!"])
    model_outputs = _validate_outputs(outputs) 
    print(model_outputs)

# ---------------------------------------------------------------------------
# Tests – remote model (OpenAI GPT-4o)
# ---------------------------------------------------------------------------

@pytest.mark.slow
def test_api_openai_gpt4o_generation():
    """Hit the OpenAI chat completions endpoint (if API key is present)."""
    os.environ["OPENAI_API_KEY"] = "sk-proj-1234567890"
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        pytest.skip("OPENAI_API_KEY not set – skipping external API call.")

    cfg = {
        "type": "api",
        "url": "https://api.openai.com/v1/chat/completions",
        "headers": {"Authorization": f"Bearer {api_key}"},
        "chat_mode": True,  # Use our OpenAI-chat compatible path
        "base_payload": {
            "model": "gpt-4o",  # You can change variant if needed
            "temperature": 0.0,
            "max_tokens": 16,
        },
    }

    generate = load_model(cfg)
    outputs = generate("You are a test assistant.", ["Say hi in one sentence."])
    model_outputs = _validate_outputs(outputs) 
    print(model_outputs)

def __main__():
    test_local_gpt2_generation()
    test_api_openai_gpt4o_generation()

if __name__ == "__main__":
    __main__()