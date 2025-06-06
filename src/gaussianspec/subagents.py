"""
Subagents for compositional, feedback-driven Lean agent system.
Each subagent is a pure dataclass with a run() method and clear feedback.
Created: 2025-04-15T21:11 UTC
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Dict
try:
    from pdf2image import convert_from_path
except ModuleNotFoundError:  # optional dependency
    convert_from_path = None  # type: ignore

try:
    import pytesseract  # type: ignore
except ModuleNotFoundError:  # optional dependency
    pytesseract = None  # type: ignore
import subprocess
from gaussianspec.lean_server import deploy_and_get_client, LeanServerClient  # type: ignore
import asyncio
try:
    from httpx import HTTPStatusError
except ModuleNotFoundError:  # optional dependency
    HTTPStatusError = Exception  # type: ignore


# --- OCR Subagent ---
@dataclass(frozen=True)
class OCRResult:
    txt_path: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class OCRSubagent:
    pdf_path: Path
    txt_path: Optional[Path] = None
    lang: str = "eng"

    def run(self) -> OCRResult:
        """Run OCR on the PDF, cache result, return feedback."""
        txt_path = self.txt_path or self.pdf_path.with_suffix(".txt")
        if txt_path.exists():
            return OCRResult(txt_path, True)
        try:
            images = convert_from_path(str(self.pdf_path))
            text = "\n".join(
                pytesseract.image_to_string(img, lang=self.lang) for img in images
            )
            txt_path.write_text(text)
            return OCRResult(txt_path, True)
        except Exception as e:
            return OCRResult(txt_path, False, str(e))


# --- PDF Crop Subagent ---
@dataclass(frozen=True)
class PDFCropResult:
    out_pdf: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class PDFCropSubagent:
    """Prepare a *cropped* version of the input PDF before OCR.

    For now this subagent applies a *fixed‐width* white mask on the right‐hand
    margin of each page (default ``90 pt``) which is sufficient to remove the
    sideways annotations in *Numerical Recipes in C*.

    The implementation purposefully avoids relying on external binaries –
    everything is handled in-process via ``PyPDF2`` and ``reportlab`` so the
    agent remains portable.
    """

    pdf_path: Path
    margin_pt: float = 90.0  # ≈ 1.25 in
    out_pdf: Optional[Path] = None
    refresh_cache: bool = False  # re-create cropped PDF even if cache exists

    def run(self) -> PDFCropResult:
        from io import BytesIO

        try:
            from PyPDF2 import PdfReader, PdfWriter  # heavy but ubiquitous
            from reportlab.pdfgen import canvas
        except ModuleNotFoundError as exc:
            return PDFCropResult(
                self.out_pdf
                or self.pdf_path.with_name(
                    self.pdf_path.stem + "_cropped" + self.pdf_path.suffix
                ),
                False,
                f"missing dependency: {exc} (did you `uv sync`?)",
            )

        try:
            out_pdf = self.out_pdf or self.pdf_path.with_name(
                f"{self.pdf_path.stem}_cropped{self.pdf_path.suffix}"
            )

            # Short-circuit if already generated (idempotent behaviour) unless
            # caller requested a *fresh* run.
            if out_pdf.exists() and not self.refresh_cache:
                return PDFCropResult(out_pdf, True)

            # If `refresh_cache` is set we remove the old file so a new one is written.
            if self.refresh_cache and out_pdf.exists():
                try:
                    out_pdf.unlink()
                except Exception as exc:
                    # Non-fatal: cropping can still proceed and overwrite.
                    print(
                        f"[PDFCropSubagent] Could not delete old cache {out_pdf}: {exc}"
                    )

            reader = PdfReader(str(self.pdf_path))
            writer = PdfWriter()

            if not reader.pages:
                return PDFCropResult(out_pdf, False, "empty PDF – nothing to crop")

            # Assume uniform page size (true for virtually all textbooks).
            width_pt = float(reader.pages[0].mediabox.width)
            height_pt = float(reader.pages[0].mediabox.height)
            x0 = max(0.0, width_pt - self.margin_pt)

            # Build overlay once and reuse for all pages.
            packet = BytesIO()
            c = canvas.Canvas(packet, pagesize=(width_pt, height_pt))
            c.setFillColorRGB(1.0, 1.0, 1.0)
            c.setStrokeColorRGB(1.0, 1.0, 1.0)
            c.rect(x0, 0.0, width_pt - x0, height_pt, stroke=0, fill=1)
            c.save()
            packet.seek(0)
            overlay_page = PdfReader(packet).pages[0]

            for page in reader.pages:
                page.merge_page(overlay_page)
                writer.add_page(page)

            out_pdf.parent.mkdir(parents=True, exist_ok=True)
            with out_pdf.open("wb") as fh:
                writer.write(fh)

            return PDFCropResult(out_pdf, True)
        except Exception as exc:  # pragma: no cover – diagnostics only
            return PDFCropResult(out_pdf, False, str(exc))


# --- Lean Edit Subagent ---
@dataclass(frozen=True)
class LeanEditResult:
    file: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class LeanEditSubagent:
    file: Path
    edit: str

    def run(self) -> LeanEditResult:
        """Apply an edit to a Lean file."""
        try:
            with self.file.open("a") as f:
                f.write("\n" + self.edit)
            return LeanEditResult(self.file, True)
        except Exception as e:
            return LeanEditResult(self.file, False, str(e))


# --- Lean Build Subagent ---
@dataclass(frozen=True)
class LeanBuildResult:
    success: bool
    output: str


@dataclass(frozen=True)
class LeanBuildSubagent:
    project_root: Path

    def run(self) -> LeanBuildResult:
        """Run `lake build` and return result."""
        proc = subprocess.run(
            ["lake", "build"], cwd=self.project_root, capture_output=True, text=True
        )
        return LeanBuildResult(proc.returncode == 0, proc.stdout + proc.stderr)


# --- Feedback Parse Subagent ---
@dataclass(frozen=True)
class FeedbackParseResult:
    message: str
    is_success: bool


@dataclass(frozen=True)
class FeedbackParseSubagent:
    output: str

    def run(self) -> FeedbackParseResult:
        """Parse Lean build output for actionable feedback.

        The heuristic considers three signals (in order):

        1. Explicit lines containing the substring ``"error:"`` – this captures
           standard Lean diagnostics.
        2. Our own wrapper prefix ``"Remote compile failed:"`` emitted by
           :class:`LeanRemoteBuildSubagent` for transport-layer issues.
        3. A final fallback that *assumes failure* if the caller set
           ``build.success = False`` but no diagnostic string was matched.  This
           prevents false "success" in cases where the build crashed before
           emitting Lean-style errors (e.g. HTTP 502 gateway failures).
        """

        lowered_lines = [ln.lower() for ln in self.output.splitlines()]

        # 1) Standard Lean errors
        for raw, low in zip(self.output.splitlines(), lowered_lines):
            if "error:" in low:
                return FeedbackParseResult(raw.strip(), False)

        # 2) Remote compile wrapper
        for raw in self.output.splitlines():
            if raw.startswith("Remote compile failed"):
                return FeedbackParseResult(raw.strip(), False)

        # 3) Fallback – treat empty output as unknown failure
        if not self.output.strip():
            return FeedbackParseResult("empty build output", False)

        return FeedbackParseResult("success", True)


# --- Lake Project Init Subagent ---
@dataclass(frozen=True)
class LakeInitResult:
    """Result of initializing a Lake project (e.g. via `lake init`)."""

    project_path: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class LakeProjectInitSubagent:
    """Ensure a Lake project exists at *project_path* with Verso dependency.

    This subagent is *idempotent*: If the project already contains a
    `lakefile.lean`, it is assumed to be correctly configured and nothing is
    changed.  Otherwise, it creates the minimal files required for other
    agents to dump content (Lean source under `Book/`).  The implementation
    favors explicit file writes over invoking external commands like
    `lake init`, which can vary across Lean versions and require user
    interaction.  This keeps the agent deterministic and avoids shelling
    out when unnecessary.
    """

    project_path: Path

    def run(self) -> LakeInitResult:
        try:
            lakefile = self.project_path / "lakefile.lean"
            if lakefile.exists():
                return LakeInitResult(self.project_path, True)

            # --- create directory structure ---
            book_dir = self.project_path / "Book"
            book_dir.mkdir(parents=True, exist_ok=True)

            # --- write lakefile.lean ---
            lakefile.write_text(
                """import Lake\nopen Lake DSL\n\npackage versobook\nrequire verso from git \"https://github.com/leanprover/verso\" @ \"main\"\n"""
            )

            # --- sync lean-toolchain ---
            root_toolchain = Path.cwd() / "lean-toolchain"
            if root_toolchain.exists():
                (self.project_path / "lean-toolchain").write_text(
                    root_toolchain.read_text()
                )

            # --- write initial Lean file so `lake build` succeeds ---
            (book_dir / "Main.lean").write_text("import Verso\n")

            return LakeInitResult(self.project_path, True)
        except Exception as exc:
            return LakeInitResult(self.project_path, False, str(exc))


# --- Lean Remote Build Subagent (Pantograph on Morph Cloud) ---
@dataclass(frozen=True)
class LeanRemoteBuildSubagent:
    """Compile Lean code *remotely* using a Pantograph Lean server.

    This subagent mirrors :class:`LeanBuildSubagent`, but instead of running
    `lake build` locally it uploads the contents of a single Lean file to a
    Pantograph-powered Lean server (see `external/morphcloud-examples-public/`
    for reference) and returns a :class:`LeanBuildResult` compatible with
    downstream glue code.  Provisioning of the server is handled
    automatically via :pyfunc:`gaussianspec.lean_server.deploy_and_get_client`.
    """

    lean_file: Path
    client: LeanServerClient | None = None  # allow caller-supplied connection

    # If remote compilation keeps failing after *max_retries* attempts we can
    # optionally fall back to a local `lake build` run so that the overall
    # pipeline still produces useful diagnostics.  This is mostly intended for
    # CI runs where the remote cache might be flaky.  Note that the local
    # build can be significantly slower since it has to rebuild mathlib from
    # scratch if lake caches are cold.
    fallback_to_local: bool = True

    # Number of retry attempts for the remote compile (geometric back-off).
    max_retries: int = 8

    def _summarise_units(self, units: List[Dict]) -> tuple[str, bool]:
        """Flatten compilation *units* into a human-readable text log and return
        ``(log, success)`` where *success* is *True* iff no `error` messages
        were reported by the server.
        """
        lines: list[str] = []
        has_error = False
        for u in units:
            for msg in u.get("messages", []):
                sev: str = msg.get("severity", "")
                if sev.lower() == "error":
                    has_error = True
                text = msg.get("text", "")
                pos = f"{msg.get('line', '?')}:{msg.get('col', '?')}"
                lines.append(f"{sev.upper()} @ {pos}: {text}")
        return ("\n".join(lines) if lines else "success"), (not has_error)

    def run(self) -> LeanBuildResult:
        """Upload *lean_file* contents to the remote server and compile.

        To mitigate transient network or service start-up issues (e.g. HTTP
        ``502 Bad Gateway`` right after the Pantograph instance boots), the
        compilation is retried a handful of times with exponential back-off
        before giving up.  All attempts are *serial*—we purposefully avoid
        concurrency here to keep the implementation simple and to not overload
        the freshly-started server.
        """

        cli = self.client or deploy_and_get_client()
        content = self.lean_file.read_text()

        async def _compile_async(cli_: LeanServerClient):
            async with cli_ as open_cli:
                return await open_cli.compile(content)

        last_exc: Exception | None = None
        for attempt in range(self.max_retries):
            try:
                units = asyncio.run(_compile_async(cli))
                log, success = self._summarise_units(units)
                return LeanBuildResult(success, log)
            except Exception as exc:  # pragma: no cover – network errors
                # Keep track of last error for final reporting and retry.
                if isinstance(exc, HTTPStatusError):
                    # Enrich the error with any server-side JSON payload to
                    # avoid the classic "502 Bad Gateway" black box.
                    body = exc.response.text.strip()
                    exc = HTTPStatusError(
                        f"{exc} – body:\n{body[:500]}",
                        request=exc.request,
                        response=exc.response,
                    )
                last_exc = exc
                # Back-off: 1s, 2s, 4s, 8s …
                if attempt < self.max_retries - 1:
                    import time

                    delay = 2**attempt
                    print(
                        f"[LeanRemoteBuildSubagent] Attempt {attempt + 1} failed "
                        f"({exc}). Retrying in {delay}s…"
                    )
                    time.sleep(delay)
                    continue

        # All retries exhausted → optional fallback
        assert last_exc is not None  # for mypy

        if self.fallback_to_local:
            print(
                "[LeanRemoteBuildSubagent] Remote compile exhausted retries – "
                "falling back to local `lake build`."
            )
            try:
                # Delegate to LeanBuildSubagent for local compilation.
                local = LeanBuildSubagent(project_root=Path.cwd()).run()
                # Prefix output so downstream parsers can distinguish.
                prefixed_output = "(local fallback)\n" + local.output
                return LeanBuildResult(local.success, prefixed_output)
            except Exception as exc:
                return LeanBuildResult(
                    False, f"Remote and local compile both failed: {exc}"
                )

        return LeanBuildResult(
            False,
            f"Remote compile failed after {self.max_retries} attempts: {last_exc}",
        )


# --- Translate Page Subagent ---
@dataclass(frozen=True)
class TranslatePageResult:
    """Result of translating a specific PDF page into a Lean file."""

    out_file: Path
    success: bool
    error: Optional[str] = None


@dataclass(frozen=True)
class TranslatePageSubagent:
    """Translate a single *page* of OCR-extracted text into a Lean comment file.

    The current implementation is intentionally *naïve*: it simply copies the
    raw OCR text of the requested page into a Lean block comment so that the
    downstream Verso-based tooling can parse or refine it later.  Page
    detection relies on the form-feed (``\f``) character that most OCR tools
    insert between pages.  If no page separators are found we fall back to a
    fixed line-count heuristic (≈ 60 lines per page).
    """

    txt_path: Path
    page_num: int = 1  # 1-indexed
    out_dir: Optional[Path] = None

    # Lines per page fallback when form-feed delimiters are absent.
    _FALLBACK_LINES_PER_PAGE: int = 60

    def _split_pages(self, text: str) -> list[str]:
        """Return list of page strings."""
        if "\f" in text:
            pages = text.split("\f")
            return [pg.strip() for pg in pages]
        # Fallback: chunk by fixed line count
        lines = text.splitlines()
        pages: list[str] = []
        for i in range(0, len(lines), self._FALLBACK_LINES_PER_PAGE):
            pages.append("\n".join(lines[i : i + self._FALLBACK_LINES_PER_PAGE]))
        return pages

    def run(self) -> TranslatePageResult:
        try:
            text = self.txt_path.read_text(encoding="utf-8", errors="replace")
            pages = self._split_pages(text)

            if not (1 <= self.page_num <= len(pages)):
                return TranslatePageResult(
                    self.txt_path,
                    False,
                    f"page {self.page_num} out of bounds (total {len(pages)})",
                )

            page_text = pages[self.page_num - 1].strip()

            target_dir = self.out_dir or self.txt_path.parent
            target_dir.mkdir(parents=True, exist_ok=True)
            out_file = target_dir / f"Page{self.page_num:04d}.lean"

            lean_content = f"/-\n{page_text}\n-/\n"
            out_file.write_text(lean_content)

            return TranslatePageResult(out_file, True)
        except Exception as exc:
            return TranslatePageResult(self.txt_path, False, str(exc))
