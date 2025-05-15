"""
Subagents for compositional, feedback-driven Lean agent system.
Each subagent is a pure dataclass with a run() method and clear feedback.
Created: 2025-04-15T21:11 UTC
"""

from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Dict
import subprocess
from gaussianspec.lean_server import deploy_and_get_client, LeanServerClient  # type: ignore
import asyncio
from httpx import HTTPStatusError


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