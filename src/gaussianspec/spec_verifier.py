from __future__ import annotations

"""Utilities for validating Lean functions against their specifications.

This module provides :func:`verify_specs_from_json` which loads a JSON file
containing a list of code snippets (Python + Lean) and checks that the Lean
function together with its specification compiles successfully.  Compilation is
performed via :class:`~gaussianspec.subagents.LeanRemoteBuildSubagent` which
uses a Pantograph Lean server.
"""

from dataclasses import dataclass
from pathlib import Path
from typing import List
import json
import tempfile

from .subagents import LeanRemoteBuildSubagent, LeanBuildResult


@dataclass(frozen=True)
class SpecEvaluation:
    """Result of verifying a single specification."""

    docstring: str
    success: bool
    log: str


def _compile_python(code: str) -> bool:
    """Return ``True`` iff *code* is syntactically valid Python."""
    try:
        compile(code, "<python>", "exec")
        return True
    except SyntaxError:
        return False


def _verify_lean(lean_fn: str, lean_spec: str) -> LeanBuildResult:
    """Compile *lean_fn* and *lean_spec* using the remote build subagent."""
    lean_source = f"import Mathlib\n\n{lean_fn}\n\n{lean_spec}\n"
    with tempfile.TemporaryDirectory() as tmpdir:
        lean_file = Path(tmpdir) / "Spec.lean"
        lean_file.write_text(lean_source)
        result = LeanRemoteBuildSubagent(lean_file=lean_file).run()
    return result


def verify_specs_from_json(json_path: Path) -> List[SpecEvaluation]:
    """Load ``json_path`` and verify each Lean spec entry.

    Parameters
    ----------
    json_path : Path
        Path to a JSON file.  The file must contain a list where each element is
        a mapping with the keys ``docstring``, ``python`` (the Python function as
        a string), ``lean_function`` and ``lean_spec``.

    Returns
    -------
    List[SpecEvaluation]
        One item per entry in the JSON input describing whether verification
        succeeded and including the build log.
    """

    data = json.loads(Path(json_path).read_text())
    results: List[SpecEvaluation] = []
    for item in data:
        doc = item.get("docstring", "")
        py_code = item.get("python", "")
        lean_fn = item.get("lean_function", "")
        lean_spec = item.get("lean_spec", item.get("lean_specification", ""))

        # Validate Python syntax first; report failure early if invalid.
        if not _compile_python(py_code):
            results.append(SpecEvaluation(doc, False, "Invalid Python syntax"))
            continue

        build_res = _verify_lean(lean_fn, lean_spec)
        results.append(SpecEvaluation(doc, build_res.success, build_res.output))

    return results
