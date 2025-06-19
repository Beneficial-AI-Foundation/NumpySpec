"""
MorphCloud-driven Lean agent for Gaussian elimination spec development.
- Drives Lean code edits, builds, and feedback loop.
- Uses morphcloud for orchestration.
- Uses subprocess for Lean build and feedback.
- Designed for compositional, functional extension.
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterator, Sequence, Any
import subprocess
import importlib, sys, os
from pdf2image import convert_from_path
from concurrent.futures import ThreadPoolExecutor
from PIL import Image
from tqdm.auto import tqdm
from gaussianspec.subagents import LeanEditResult

from tqdm.auto import tqdm

# ---------------- utility: ensure a package is installed ---------------- #


def _ensure_package(pkg: str, import_name: str | None = None):
    """Import *pkg*, installing via `uv` if necessary, and return the module."""

    name = import_name or pkg
    try:
        return importlib.import_module(name)
    except ModuleNotFoundError:
        print(f"[agent] Installing missing dependency '{pkg}' via uv…", file=sys.stderr)
        subprocess.run(["uv", "add", pkg], check=True)
        return importlib.import_module(name)


# Third-party deps (installed on-demand)
morphcloud = _ensure_package("morphcloud")
genai = _ensure_package("google-generativeai", "google.generativeai")
openai = _ensure_package("openai")

# Import Codex utilities
try:
    from gaussianspec.codex_utils import CodexClient, VoiceMode, OnlineCodexSetup, best_of_n_completion, setup_codex_environment
    _CODEX_AVAILABLE = True
except ImportError as e:
    print(f"[agent] Codex utilities not available: {e}", file=sys.stderr)
    _CODEX_AVAILABLE = False

# We no longer depend on local Tesseract.

from gaussianspec.subagents import LeanEditResult  # type: ignore F401

# Optional local Tesseract OCR backend
try:
    import pytesseract  # type: ignore

    _TESSERACT_AVAILABLE = True
except ModuleNotFoundError:
    _TESSERACT_AVAILABLE = False


# --- Types ---
@dataclass(frozen=True)
class LeanEdit:
    file: Path
    edit: str
    description: str


@dataclass(frozen=True)
class BuildResult:
    success: bool
    output: str


# --- Core functions ---
def run_lake_build(project_root: Path) -> BuildResult:
    """Run `lake build` and return result."""
    proc = subprocess.run(
        ["lake", "build"], cwd=project_root, capture_output=True, text=True
    )
    return BuildResult(success=proc.returncode == 0, output=proc.stdout + proc.stderr)


def apply_lean_edit(edit: LeanEdit) -> LeanEditResult:
    """Apply *edit* to its target Lean file and return a :class:`LeanEditResult` so
    that upstream orchestrators can inspect success/failure without having to
    replicate the file-system side-effects.
    """
    try:
        with edit.file.open("a") as f:
            f.write("\n" + edit.edit)
        return LeanEditResult(file=edit.file, success=True)
    except Exception as exc:
        return LeanEditResult(file=edit.file, success=False, error=str(exc))


def parse_build_feedback(output: str) -> str:
    """Extract error or success message from build output."""
    for line in output.splitlines():
        low = line.lower()
        if "error:" in low or low.startswith("error"):
            return line
        # Pantograph summariser prefixes messages with "ERROR @" (caps)
        if line.strip().startswith("ERROR"):
            return line
    return "success"


# --- Codex-Enhanced Proof Generation ---
def create_lean_edit_with_codex(
    file: Path,
    theorem_statement: str,
    *,
    use_voice: bool = False,
    use_best_of_n: bool = True,
    n_completions: int = 3,
    description: str = "",
) -> LeanEdit:
    """Create a LeanEdit using Codex with optional voice input and best-of-n selection.
    
    Parameters
    ----------
    file : Path
        Target Lean file for the edit.
    theorem_statement : str
        The theorem statement to complete, or empty string for voice input.
    use_voice : bool
        Whether to use voice input for the theorem statement.
    use_best_of_n : bool
        Whether to generate multiple completions and select the best.
    n_completions : int
        Number of completions to generate if using best-of-n.
    description : str
        Description of the edit.
    
    Returns
    -------
    LeanEdit
        The generated Lean edit.
    """
    if not _CODEX_AVAILABLE:
        raise RuntimeError("Codex utilities not available. Check dependencies.")
    
    final_statement = theorem_statement
    
    # Voice input mode
    if use_voice and not final_statement:
        try:
            voice_mode = VoiceMode()
            voice_input = voice_mode.listen_for_theorem()
            final_statement = voice_mode.theorem_from_voice(voice_input)
            print(f"[agent] Voice input converted to: {final_statement}")
        except Exception as e:
            print(f"[agent] Voice input failed: {e}", file=sys.stderr)
            final_statement = "-- Voice input failed, please provide theorem manually"
    
    if not final_statement:
        raise ValueError("No theorem statement provided and voice input not available")
    
    # Generate proof using Codex
    client = CodexClient()
    
    if use_best_of_n:
        completions = best_of_n_completion(
            client=client,
            prompt=final_statement,
            n=n_completions,
            context="Complete this Lean theorem with a rigorous proof"
        )
        proof_completion = completions[0].text if completions else "by sorry"
    else:
        completion = client.complete_lean_code(
            prompt=final_statement,
            context="Complete this Lean theorem with a rigorous proof"
        )
        proof_completion = completion.text
    
    # Combine statement and proof
    full_edit = f"{final_statement}\n{proof_completion}"
    
    return LeanEdit(
        file=file,
        edit=full_edit,
        description=description or f"Codex-generated proof for theorem"
    )


def enhanced_proof_generation(
    theorem_statement: str,
    context: str = "",
    *,
    methods: list[str] = ["codex", "hf"],
    use_best_of_n: bool = True,
) -> str:
    """Generate proofs using multiple AI backends and select the best.
    
    Parameters
    ----------
    theorem_statement : str
        The theorem statement to prove.
    context : str
        Additional context about the theorem.
    methods : list[str]
        List of methods to try: "codex", "hf" (HuggingFace).
    use_best_of_n : bool
        Whether to use best-of-n selection for Codex.
    
    Returns
    -------
    str
        The best generated proof.
    """
    proofs = []
    
    # Try Codex if available
    if "codex" in methods and _CODEX_AVAILABLE:
        try:
            client = CodexClient()
            if use_best_of_n:
                completions = best_of_n_completion(
                    client=client,
                    prompt=theorem_statement,
                    n=3,
                    context=context
                )
                if completions:
                    proofs.append(("codex", completions[0].text))
            else:
                completion = client.complete_lean_code(theorem_statement, context)
                proofs.append(("codex", completion.text))
        except Exception as e:
            print(f"[agent] Codex proof generation failed: {e}", file=sys.stderr)
    
    # Try HuggingFace model if available
    if "hf" in methods:
        try:
            from gaussianspec.hf_utils import load_model, propose_proof
            model, tokenizer = load_model()
            hf_proof = propose_proof(
                model=model,
                tokenizer=tokenizer,
                problem_statement=context or "Prove the given theorem",
                formal_statement=theorem_statement
            )
            proofs.append(("hf", hf_proof))
        except Exception as e:
            print(f"[agent] HuggingFace proof generation failed: {e}", file=sys.stderr)
    
    if not proofs:
        return "by sorry -- No proof generation methods available"
    
    # For now, prefer Codex over HuggingFace
    codex_proofs = [p for method, p in proofs if method == "codex"]
    if codex_proofs:
        return codex_proofs[0]
    
    return proofs[0][1]


def setup_online_codex_assistant(project_root: Path) -> OnlineCodexSetup | None:
    """Setup online Codex assistant for interactive proof development.
    
    Parameters
    ----------
    project_root : Path
        Root directory of the Lean project.
    
    Returns
    -------
    OnlineCodexSetup | None
        The online assistant, or None if not available.
    """
    if not _CODEX_AVAILABLE:
        print("[agent] Codex not available for online assistance", file=sys.stderr)
        return None
    
    try:
        client = CodexClient()
        assistant = OnlineCodexSetup(client=client, auto_complete=True)
        print(f"[agent] Online Codex assistant ready for {project_root}")
        return assistant
    except Exception as e:
        print(f"[agent] Failed to setup online Codex assistant: {e}", file=sys.stderr)
        return None


# --- OCR Preprocessing ---
def ocr_pdf_to_text(
    pdf_path: Path,
    txt_path: Path | None = None,
    *,
    lang: str = "eng",
    start_page: int = 1,
    end_page: int | None = None,
    parallel: bool = True,
    max_workers: int | None = None,
    method: str = "auto",  # 'auto' | 'openai' | 'gemini'
    strip_right_px: int = 0,
) -> Path:
    """OCR a slice of pages from *pdf_path* into *txt_path*.

    If *txt_path* exists, return it (simple caching).

    Parameters
    ----------
    pdf_path : Path
        PDF file to process.
    txt_path : Path | None
        Output text path. Defaults to ``pdf_path.with_suffix('.txt')`` or, if a page
        range is specified, ``pdf_path.stem_{start}-{end}.txt``.
    start_page : int, default 1
        First 1‑indexed page to process
    end_page : int | None
        Last page (inclusive). ``None`` means till the end of the document.
    parallel : bool, default True
        Whether to OCR pages concurrently (thread‑pool – GIL is released inside
        Tesseract so threads scale reasonably).
    max_workers : int | None
        Overrides default worker count for the ThreadPoolExecutor.
    method : str, default 'auto'
        OCR backend to use.  'auto' tries *openai → gemini* in that order.
        Explicit values 'openai', 'gemini' force a single engine.
    strip_right_px : int, default 0
        If > 0, crop *strip_right_px* pixels from the right margin of each
        page image **before** OCR.  This is useful for PDFs like *Numerical
        Recipes* that contain a vertical "sample page" column on the right
        which confuses OCR.
    """

    # Derive default txt filename that encodes page range so chunks are cached separately
    if txt_path is None:
        suffix = f"_{start_page}-{end_page}" if end_page is not None else ""
        txt_path = pdf_path.parent / f"{pdf_path.stem}{suffix}.txt"

    if txt_path.exists():
        return txt_path

    # Load only the required page range (pdf2image supports this natively)
    images_raw = convert_from_path(
        str(pdf_path), first_page=start_page, last_page=end_page or 0
    )

    # Optional preprocessing: strip right-hand sample text column that
    # appears in the Numerical Recipes PDF (and similar).  This greatly
    # improves OCR fidelity by removing vertically-oriented noise.
    images: list[Image.Image] = []
    if strip_right_px > 0:
        for img in images_raw:
            # Ensure we don't crop into negative width
            new_w = max(1, img.width - strip_right_px)
            images.append(img.crop((0, 0, new_w, img.height)))
    else:
        images = list(images_raw)

    # --- choose OCR backends ---
    if method not in {"auto", "openai", "gemini"}:
        raise ValueError("method must be 'auto', 'openai', or 'gemini'")

    methods_to_try: list[str] = ["openai", "gemini"] if method == "auto" else [method]

    # --- helper: attempt OCR via selected backend over *all* pages ---

    def ocr_with_backend(backend: str) -> list[str]:
        if backend == "openai":
            return _openai_ocr_images(images).split("\n")
        elif backend == "gemini":
            return _gemini_ocr_images(images).split("\n")
        else:
            raise RuntimeError(f"Unknown OCR backend: {backend}")

    # Try each backend in turn, respecting policy-refusal detection
    last_error: Exception | None = None
    text_pages: list[str] | None = None
    for backend in methods_to_try:
        try:
            text_pages = ocr_with_backend(backend)

            combined = "\n".join(text_pages)
            if _ocr_refused(combined) or _ocr_refused_llm(combined):
                raise RuntimeError(f"{backend} refused due to policy")

            break  # success
        except Exception as exc:
            last_error = exc
            continue

    if text_pages is None:
        # All backends failed
        assert last_error is not None
        raise last_error

    txt_path.write_text("\n".join(text_pages))
    return txt_path


# --- Agent loop ---
def agent_loop(
    project_root: Path,
    edits: Sequence[LeanEdit],
    build_fn: Callable[[Path], BuildResult] = run_lake_build,
    edit_fn: Callable[[LeanEdit], LeanEditResult] = apply_lean_edit,
    feedback_fn: Callable[[str], str] = parse_build_feedback,
) -> Iterator[str]:
    """Drive Lean code edits and builds, yielding feedback after each step."""
    for edit in edits:
        edit_fn(edit)  # result ignored for now; could be yielded later
        result = build_fn(project_root)
        feedback = feedback_fn(result.output)
        yield feedback


# --- Pipeline composition ---
def agent_pipeline(
    project_root: Path,
    pdf_path: Path,
    edits: Sequence[LeanEdit],
    ocr_fn: Callable[[Path], Path] = lambda pdf: ocr_pdf_to_text(pdf),
    build_fn: Callable[[Path], BuildResult] = run_lake_build,
    edit_fn: Callable[[LeanEdit], LeanEditResult] = apply_lean_edit,
    feedback_fn: Callable[[str], str] = parse_build_feedback,
) -> Iterator[str]:
    """
    Full agent pipeline: OCR textbook, then run Lean edit/build/feedback loop.
    Yields feedback after each Lean step.
    """
    ocr_txt = ocr_fn(pdf_path)
    yield f"OCR complete: {ocr_txt}"
    yield from agent_loop(project_root, edits, build_fn, edit_fn, feedback_fn)


# --- Example usage (to be replaced by MorphCloud orchestration) ---
if __name__ == "__main__":
    root = Path(__file__).parent.parent.parent
    
    # Traditional example
    edits = [
        LeanEdit(
            file=root / "GaussianSpec.lean",
            edit="-- Example edit by agent",
            description="Add a comment for testing.",
        )
    ]
    
    print("=== Traditional Agent Loop ===")
    for feedback in agent_loop(root, edits):
        print("Agent feedback:", feedback)
    
    # Codex-enhanced examples
    if _CODEX_AVAILABLE:
        print("\n=== Codex Environment Status ===")
        status = setup_codex_environment()
        print(f"Features available: {status['features']}")
        
        if status['features']['code_completion']:
            print("\n=== Codex-Enhanced Proof Generation ===")
            try:
                # Example: Create a proof using Codex with best-of-n
                codex_edit = create_lean_edit_with_codex(
                    file=root / "GaussianSpec.lean",
                    theorem_statement="theorem add_zero (n : ℕ) : n + 0 = n := ",
                    use_best_of_n=True,
                    n_completions=2,
                    description="Codex-generated proof with best-of-n selection"
                )
                print(f"Generated edit: {codex_edit.edit}")
                
                # Example: Enhanced proof generation with multiple backends
                enhanced_proof = enhanced_proof_generation(
                    theorem_statement="theorem zero_add (n : ℕ) : 0 + n = n := ",
                    context="This is a basic theorem about natural number addition",
                    methods=["codex", "hf"],
                    use_best_of_n=True
                )
                print(f"Enhanced proof: {enhanced_proof}")
                
            except Exception as e:
                print(f"Codex example failed: {e}")
        
        if status['features']['online_setup']:
            print("\n=== Online Codex Assistant ===")
            assistant = setup_online_codex_assistant(root)
            if assistant:
                print("Online assistant ready for interactive development")
        
        if status['features']['voice_mode']:
            print("\n=== Voice Mode Available ===")
            print("Voice input can be used with: use_voice=True in create_lean_edit_with_codex")
    
    else:
        print("\n=== Codex Features Not Available ===")
        print("Install dependencies: uv add speechrecognition pyaudio")


# ---------- helper: Gemini OCR ----------


def _gemini_ocr_images(
    images: list[Image.Image],
    *,
    prompt: str | None = None,
    model: str = "gemini-1.5-flash-latest",
) -> str:
    """OCR a list of PIL images using Google Gemini.

    Requires the *google‑generativeai* package and the API key in
    ``$GOOGLE_GEMINI_API_KEY``.  Concatenates page outputs with newlines.
    """

    # at this point genai import succeeded via _ensure_package

    api_key = os.getenv("GOOGLE_GEMINI_API_KEY")
    if api_key is None:
        raise RuntimeError(
            f"Environment variable GOOGLE_GEMINI_API_KEY not set; cannot use Gemini OCR."
        )

    genai.configure(api_key=api_key)  # type: ignore[attr-defined]

    if prompt is None:
        prompt = (
            "You are a precise OCR engine. Extract the *verbatim* text, including any LaTeX "
            "math and special symbols. Do not add commentary."
        )

    model_obj = genai.GenerativeModel(model)  # type: ignore[attr-defined]

    results: list[str] = []
    for img in images:
        resp = model_obj.generate_content([prompt, img])
        results.append(resp.text)

    return "\n".join(results)


# ---------- helper: OpenAI OCR ---------------------------------------------


def _openai_ocr_images(
    images: list[Image.Image],
    *,
    prompt: str | None = None,
    model: str = "gpt-4o-mini",
) -> str:
    """OCR a list of images using OpenAI Vision models (e.g. GPT‑4o‑mini).

    Requires the *openai* package and an ``$OPENAI_API_KEY`` environment variable.
    """

    # openai import already ensured

    api_key = os.getenv("OPENAI_API_KEY")
    if api_key is None:
        raise RuntimeError(
            f"Environment variable OPENAI_API_KEY not set; cannot use OpenAI OCR."
        )

    # Lazy import to avoid polluting global namespace
    import base64, io

    if prompt is None:
        prompt = (
            "You are a precise OCR engine. Extract the *verbatim* text, including any LaTeX "
            "math and special symbols. Do not add commentary."
        )

    results: list[str] = []

    for img in images:
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        b64 = base64.b64encode(buf.getvalue()).decode()

        resp = openai.OpenAI(api_key=api_key).chat.completions.create(
            model=model,
            messages=[
                {
                    "role": "user",
                    "content": [
                        {"type": "text", "text": prompt},
                        {
                            "type": "image_url",
                            "image_url": {"url": f"data:image/png;base64,{b64}"},
                        },
                    ],
                }
            ],
        )

        msg_content = resp.choices[0].message.content or ""
        results.append(msg_content)

    return "\n".join(results)


# --- refusal heuristics ----------------------------------------------------


def _ocr_refused(text: str) -> bool:
    """Return True if *text* looks like a policy refusal / copyright block."""
    lowered = text.lower()
    bad_phrases = [
        "i'm sorry",
        "i am sorry",
        "sorry",
        "can't help with that",
        " violate",
        "copyright",
        "policy",
    ]
    return any(p in lowered for p in bad_phrases)


# --- LLM-based refusal detection ------------------------------------------


def _ocr_refused_llm(text: str, *, model: str = "gpt-4o-mini") -> bool:
    """Use a small OpenAI model to classify whether *text* is a refusal message.

    Returns False if OpenAI client/key unavailable to avoid blocking.
    """

    # openai import ensured above

    api_key = os.getenv("OPENAI_API_KEY")
    if api_key is None:
        return False

    try:
        client = openai.OpenAI(api_key=api_key)

        prompt_system = (
            "You are a text classifier. Respond with exactly 'yes' if the given text is an AI policy "
            "refusal / apology and not genuine OCR content. Respond with 'no' otherwise."
        )

        user_text = text[:1000]  # truncate for cost

        resp = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": prompt_system},
                {"role": "user", "content": user_text},
            ],
            max_tokens=1,
        )

        msg_content = resp.choices[0].message.content or ""
        answer = msg_content.strip().lower()
        return answer.startswith("y")
    except Exception:
        return False
