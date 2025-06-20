from __future__ import annotations
"""High‑level utilities for loading HuggingFace transformer models and generating
Lean proof text.

These thin wrappers isolate the `transformers` / `accelerate` details from the
rest of the codebase so that other modules can rely on a small, typed surface
area.

Example
-------
>>> from numpyspec.hf_utils import load_model, generate
>>> model, tok = load_model("sshleifer/tiny-gpt2")
>>> print(generate(model, tok, "Hello", max_new_tokens=5))
"Hello..."  # doctest: +SKIP
"""

from pathlib import Path
from functools import lru_cache
from typing import Tuple, List

import torch  # type: ignore
from transformers import AutoModelForCausalLM, AutoTokenizer, GenerationConfig  # type: ignore

# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def load_model(
    model_name: str = "AI-MO/Kimina-Prover-Preview-Distill-1.5B",
    dtype: torch.dtype | None = torch.bfloat16,
    device: str | torch.device | None = None,
    trust_remote_code: bool = True,
):
    """Load a causal‑LM model + tokenizer pair with sensible defaults.

    Parameters
    ----------
    model_name: str
        HuggingFace repo id (or local path) to load.
    dtype: torch.dtype | None
        Low‑precision dtype to use for weights. Default bf16 (works on Ampere+).
    device: str | torch.device | None
        Target device. If *None*, choose "cuda" when available otherwise "cpu".
    trust_remote_code: bool
        Forwarded to `from_pretrained` to allow gated repositories.

    Returns
    -------
    model : AutoModelForCausalLM
    tokenizer : AutoTokenizer
    """
    if device is None:
        device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    # Tokenizer first so we can resize tokens later if needed.
    tokenizer = AutoTokenizer.from_pretrained(
        model_name, use_fast=True, trust_remote_code=trust_remote_code
    )

    model = AutoModelForCausalLM.from_pretrained(
        model_name,
        torch_dtype=dtype,
        device_map="auto" if device != "cpu" else None,
        trust_remote_code=trust_remote_code,
    )

    # Ensure pad_token exists for generation.
    if tokenizer.pad_token_id is None:
        tokenizer.pad_token = tokenizer.eos_token

    return model, tokenizer


def generate(
    model: AutoModelForCausalLM,
    tokenizer: AutoTokenizer,
    prompt: str,
    max_new_tokens: int = 256,
    temperature: float = 0.7,
    top_p: float = 0.95,
    do_sample: bool = True,
) -> str:
    """Generate completion text from *prompt* using *model* and *tokenizer*."""
    input_ids = tokenizer(prompt, return_tensors="pt").input_ids.to(model.device)
    gen_cfg = GenerationConfig(
        max_new_tokens=max_new_tokens,
        temperature=temperature,
        top_p=top_p,
        do_sample=do_sample,
        pad_token_id=tokenizer.pad_token_id,
    )
    with torch.no_grad():
        output_ids = model.generate(input_ids, generation_config=gen_cfg)[0]
    return tokenizer.decode(output_ids[input_ids.size(1):], skip_special_tokens=True)


# ---------------------------------------------------------------------------
# Domain‑specific helpers
# ---------------------------------------------------------------------------

def propose_proof(
    model,
    tokenizer,
    problem_statement: str,
    formal_statement: str,
    **gen_kwargs,
) -> str:
    """Prepare a few‑shot prompt and let the model propose a Lean proof."""

    system_msg = """You are Kimina‑Prover, an expert Lean‑4 automated theorem prover."""
    user_msg = (
        "Think step‑by‑step and produce a complete Lean proof.\n"
        f"# Problem:\n{problem_statement}\n"
        f"# Formal statement (Lean):\n```lean\n{formal_statement}\n```\n"
        "# Proof:\n```lean\n"
    )

    prompt = (
        f"<|im_start|>system\n{system_msg}<|im_end|>\n"
        f"<|im_start|>user\n{user_msg}<|im_end|>\n"
        "<|im_start|>assistant\n"
    )

    completion = generate(model, tokenizer, prompt, **gen_kwargs)

    # Trim after code fence if present.
    proof = completion.split("```", 1)[0].strip()
    return proof 