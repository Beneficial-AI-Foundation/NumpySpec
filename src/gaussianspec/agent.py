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
from gaussianspec.subagents import LeanEditResult

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