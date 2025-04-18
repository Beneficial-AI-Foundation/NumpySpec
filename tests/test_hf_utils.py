from __future__ import annotations

from gaussianspec.hf_utils import load_model, generate


def test_tiny_model_generate():
    # Use a CPU‑friendly tiny model to keep CI light.
    model, tok = load_model("sshleifer/tiny-gpt2", dtype=None, device="cpu")
    out = generate(model, tok, "Hello", max_new_tokens=5, do_sample=False)
    assert isinstance(out, str) and len(out) > 0 