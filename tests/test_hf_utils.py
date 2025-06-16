from __future__ import annotations

import importlib.util
import pytest

from gaussianspec import hf_utils


@pytest.mark.skipif(importlib.util.find_spec("torch") is None, reason="requires torch")
def test_tiny_model_generate():
    model, tok = hf_utils.load_model("sshleifer/tiny-gpt2", dtype=None, device="cpu")
    out = hf_utils.generate(model, tok, "Hello", max_new_tokens=5, do_sample=False)
    assert isinstance(out, str) and len(out) > 0
