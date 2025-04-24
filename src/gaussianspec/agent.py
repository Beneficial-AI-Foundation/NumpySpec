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

# morphcloud is optional; this module can be imported without it for local builds.
try:
    import morphcloud  # type: ignore
except ModuleNotFoundError:
    morphcloud = None
from pdf2image import convert_from_path
from concurrent.futures import ThreadPoolExecutor
from PIL import Image  # type: ignore
import os

# Optional frontier‑model OCR (Google 1.5 Flash / 2.5 etc.)
try:
    import google.generativeai as genai  # type: ignore

    _GEMINI_AVAILABLE = True
except ModuleNotFoundError:
    _GEMINI_AVAILABLE = False

# Optional OpenAI Vision model (GPT‑4o‑mini etc.)
try:
    import openai  # type: ignore

    _OPENAI_AVAILABLE = True
except ModuleNotFoundError:
    _OPENAI_AVAILABLE = False

# ENV var bearing the API key expected by google‑generativeai
_GEMINI_API_ENV = "GOOGLE_GEMINI_API_KEY"

# ENV var names for API keys
_OPENAI_API_ENV = "OPENAI_API_KEY"

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


def apply_lean_edit(edit: LeanEdit) -> None:
    """Apply an edit to a Lean file."""
    with edit.file.open("a") as f:
        f.write("\n" + edit.edit)


def parse_build_feedback(output: str) -> str:
    """Extract error or success message from build output."""
    # Simple heuristic: return first error or 'success'
    for line in output.splitlines():
        if "error:" in line:
            return line
    return "success"


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
    method: str = "auto",  # 'auto' | 'openai' | 'gemini' | 'tesseract'
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
        OCR backend to use.  'auto' tries *openai → gemini → tesseract* in that
        order.  Explicit values 'openai', 'gemini', 'tesseract' force a single
        engine.
    """

    # Derive default txt filename that encodes page range so chunks are cached separately
    if txt_path is None:
        suffix = f"_{start_page}-{end_page}" if end_page is not None else ""
        txt_path = pdf_path.parent / f"{pdf_path.stem}{suffix}.txt"

    if txt_path.exists():
        return txt_path

    # Load only the required page range (pdf2image supports this natively)
    images = convert_from_path(
        str(pdf_path), first_page=start_page, last_page=end_page or 0
    )

    def _tesseract_ocr(imgs: list[Image.Image]) -> str:
        """Local Tesseract OCR (optionally parallel)."""

        def ocr_image(img):
            return pytesseract.image_to_string(img, lang=lang)

        if parallel and len(imgs) > 1:
            with ThreadPoolExecutor(max_workers=max_workers) as pool:
                futures = [pool.submit(ocr_image, img) for img in imgs]
                return "\n".join(f.result() for f in futures)
        else:
            return "\n".join(ocr_image(img) for img in imgs)

    methods_to_try: list[str] = (
        [
            m
            for m in ["openai", "gemini", "tesseract"]
            if (m != "tesseract" or _TESSERACT_AVAILABLE)
        ]
        if method == "auto"
        else ([method] if (method != "tesseract" or _TESSERACT_AVAILABLE) else [])
    )

    def ocr_page(img: Image.Image) -> str:
        """OCR a single page trying each provider until one succeeds."""

        last_error: Exception | None = None
        for m in methods_to_try:
            try:
                if m == "openai":
                    page_text = _openai_ocr_images([img])
                elif m == "gemini":
                    page_text = _gemini_ocr_images([img])
                else:  # tesseract
                    if not _TESSERACT_AVAILABLE:
                        raise RuntimeError("Tesseract OCR backend not available")
                    page_text = _tesseract_ocr([img])

                if m == "tesseract":
                    # Assume Tesseract output is always allowed; no policy checks.
                    return page_text

                flagged = _ocr_refused(page_text) or _ocr_refused_llm(page_text)

                if flagged:
                    raise RuntimeError(f"{m} refused due to policy")

                return page_text
            except Exception as exc:
                last_error = exc
                continue

        # If we exited loop without returning, raise last error
        assert last_error is not None
        raise last_error

    # Perform OCR page by page (enables split‑on‑error fallback)
    try:
        text_pages = [ocr_page(img) for img in images]
    except Exception as top_exc:
        # If user explicitly requested single provider, bubble error; otherwise, raise.
        raise top_exc

    text = "\n".join(text_pages)

    txt_path.write_text(text)
    return txt_path


# --- Agent loop ---
def agent_loop(
    project_root: Path,
    edits: Sequence[LeanEdit],
    build_fn: Callable[[Path], BuildResult] = run_lake_build,
    edit_fn: Callable[[LeanEdit], None] = apply_lean_edit,
    feedback_fn: Callable[[str], str] = parse_build_feedback,
) -> Iterator[str]:
    """Drive Lean code edits and builds, yielding feedback after each step."""
    for edit in edits:
        edit_fn(edit)
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
    edit_fn: Callable[[LeanEdit], None] = apply_lean_edit,
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
    edits = [
        LeanEdit(
            file=root / "GaussianSpec.lean",
            edit="-- Example edit by agent",
            description="Add a comment for testing.",
        )
    ]
    for feedback in agent_loop(root, edits):
        print("Agent feedback:", feedback)


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

    if not _GEMINI_AVAILABLE:
        raise RuntimeError(
            "google-generativeai not installed. Run: `uv add google-generativeai`."
        )

    api_key = os.getenv(_GEMINI_API_ENV)
    if api_key is None:
        raise RuntimeError(
            f"Environment variable {_GEMINI_API_ENV} not set; cannot use Gemini OCR."
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

    if not _OPENAI_AVAILABLE:
        raise RuntimeError("openai package not installed. Run: `uv add openai`. ")

    api_key = os.getenv(_OPENAI_API_ENV)
    if api_key is None:
        raise RuntimeError(
            f"Environment variable {_OPENAI_API_ENV} not set; cannot use OpenAI OCR."
        )

    # New client API (>=1.0)
    client = openai.OpenAI(api_key=api_key)

    if prompt is None:
        prompt = (
            "You are a precise OCR engine. Extract the *verbatim* text, including any LaTeX "
            "math and special symbols. Do not add commentary."
        )

    import base64, io

    results: list[str] = []

    for img in images:
        buf = io.BytesIO()
        img.save(buf, format="PNG")
        b64 = base64.b64encode(buf.getvalue()).decode()

        resp = client.chat.completions.create(
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

    if not _OPENAI_AVAILABLE:
        return False

    api_key = os.getenv(_OPENAI_API_ENV)
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
