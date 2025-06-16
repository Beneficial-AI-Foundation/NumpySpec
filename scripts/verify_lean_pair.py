#!/usr/bin/env python3
"""Verify a Lean implementation file against its specification.

This helper is **stand-alone** and mirrors the high-level logic used by
`scripts/run_constants_verifier.py`, but is generalised to *any* pair of Lean
files instead of the hard-coded numpy constants directory.

Example
-------
```bash
python scripts/verify_lean_pair.py \
       --impl data/constants/numpy_e.lean \
       --spec data/constants/numpy_e_spec.lean
```

The script will upload a combined Lean source (implementation + specification)
for remote compilation via the Pantograph server configured by
:class:`gaussianspec.subagents.LeanRemoteBuildSubagent` and print a coloured
pass/fail summary.  It exits with status code ``0`` on success so it can be
integrated into CI pipelines.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

# Allow `import gaussianspec.*` when the script is executed from the repo root.
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "src"))

from gaussianspec.subagents import LeanRemoteBuildSubagent, LeanBuildResult, LeanBuildSubagent  # type: ignore


# -----------------------------------------------------------------------------
# Utility helpers
# -----------------------------------------------------------------------------

def _read(path: Path) -> str:
    """Return *path* contents as UTF-8 string, raising if the file is missing."""
    if not path.exists():
        raise FileNotFoundError(path)
    return path.read_text(encoding="utf-8")


def _strip_relative_imports(code: str, impl_stem: str) -> str:
    """Remove lines like `import ./foo` that reference *impl_stem*.

    When we concatenate implementation and spec into a *single* Lean file the
    original relative import becomes redundant and, if left in place, causes a
    duplicate declaration error.  We therefore drop any line that imports the
    exact implementation module (either `import ./foo` or `import ./foo as …`).
    Other imports are preserved.
    """
    pattern = re.compile(rf"^\s*import\s+\./{re.escape(impl_stem)}(\s|$)")
    return "\n".join(line for line in code.splitlines() if not pattern.match(line))


def _build_remote(lean_source: str, temp_name: str) -> LeanBuildResult:
    """Compile *lean_source* remotely; return build result."""
    with tempfile.TemporaryDirectory() as td:
        lean_file = Path(td) / f"{temp_name}.lean"
        lean_file.write_text(lean_source, encoding="utf-8")
        return LeanRemoteBuildSubagent(lean_file=lean_file).run()


# -----------------------------------------------------------------------------
# CLI entry-point
# -----------------------------------------------------------------------------

def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Verify a Lean implementation against its specification"
    )
    p.add_argument("--impl", required=True, type=Path, help="Path to implementation .lean file")
    p.add_argument("--spec", required=True, type=Path, help="Path to specification .lean file")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument(
        "--remote",
        action="store_true",
        help="Force remote compilation (Pantograph server). Default is local if possible.",
    )
    mode.add_argument(
        "--local",
        action="store_true",
        help="Force local compilation via `lake build` (ignores remote).",
    )
    p.add_argument(
        "--verbose", "-v", action="store_true", help="Print full build log on success as well"
    )
    return p.parse_args()


def main() -> None:
    args = _parse_args()

    impl_path: Path = args.impl.resolve()
    spec_path: Path = args.spec.resolve()

    print(f"🔍 Verifying Lean spec\n  implementation: {impl_path}\n  specification:  {spec_path}\n")

    impl_code = _read(impl_path)
    spec_code_raw = _read(spec_path)

    # Remove relative import to implementation (if any)
    spec_code = _strip_relative_imports(spec_code_raw, impl_path.stem)

    lean_source = f"""import Mathlib\n\n{impl_code}\n\n{spec_code}\n"""

    def _build_local(src: str) -> LeanBuildResult:  # inline helper to avoid clutter
        """Write *src* to repo root & run `lake build`. Cleans up afterwards."""
        import uuid, subprocess, os, shutil

        tmp_name = f"TmpVerify_{uuid.uuid4().hex[:8]}"
        tmp_file = REPO_ROOT / f"{tmp_name}.lean"
        tmp_file.write_text(src, encoding="utf-8")

        try:
            res = LeanBuildSubagent(project_root=REPO_ROOT).run()
            # Filter log to lines containing the tmp file for clarity
            log = "\n".join(
                ln for ln in res.output.splitlines() if tmp_name in ln or "error:" in ln
            )
            return LeanBuildResult(res.success, log or res.output)
        finally:
            # Clean up the temporary Lean file and any generated .olean artifacts
            try:
                tmp_file.unlink()
                olean = tmp_file.with_suffix(".olean")
                if olean.exists():
                    olean.unlink()
            except Exception:
                pass

    # Decide compilation mode
    compile_remote = args.remote or (not args.local)

    result: LeanBuildResult | None = None

    if compile_remote:
        try:
            result = _build_remote(lean_source, impl_path.stem + "_spec")
        except RuntimeError as exc:
            # Morphcloud not installed or other remote provisioning issue → fallback
            print(f"⚠️  Remote compile unavailable ({exc}). Falling back to local build…")
            result = _build_local(lean_source)
    else:
        result = _build_local(lean_source)

    if result.success:
        print("✅  Verification succeeded")
        if args.verbose:
            print("----- build log (success) -----")
            print(result.output.rstrip())
    else:
        print("❌  Verification FAILED – see log below")
        print("----- build log (failure) -----")
        print(result.output.rstrip())
        sys.exit(1)


if __name__ == "__main__":
    main() 