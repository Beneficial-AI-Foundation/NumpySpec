#!/usr/bin/env python
"""Evaluate a language-model's ability to translate docstrings into Lean code.

Usage
-----
$ ./scripts/evaluate_model.py

The script loads the small *constants* dataset shipped with SpecDraft, asks the
configured model to generate Lean code for each docstring, verifies the
resulting files, and prints a summary table.

Environment variables
---------------------
MODEL_CFG : JSON string (optional)
    Overrides the default model configuration.  Example::

        export MODEL_CFG='{"type": "api", "url": "https://...", ...}'

LEAN_TMP_DIR : path (optional)
    Directory where temporary `.lean` files are written.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Dict, Any

try:
    from rich.console import Console
    from rich.table import Table
except ImportError:  # pragma: no cover – rich is optional for pretty output
    class _Dummy:
        def __getattr__(self, *_):  # type: ignore[override]
            return lambda *args, **kwargs: None

    Console = _Dummy  # type: ignore
    Table = _Dummy  # type: ignore

    def _make_table(*args, **kwargs):  # noqa: D401
        class _Table:
            def add_column(self, *_, **__):
                pass

            def add_row(self, *_, **__):
                pass

        return _Table()

    Table = _make_table  # type: ignore

# Add repository's *src* directory so that `import specdraft` works when the
# script is executed directly.
PROJ_ROOT = Path(__file__).resolve().parents[1]
SRC_DIR = PROJ_ROOT / "src"
if str(SRC_DIR) not in sys.path:
    sys.path.insert(0, str(SRC_DIR))

from specdraft.pipeline.model import generate_lean_file  # noqa: E402
from specdraft.pipeline.verifier import verify_lean_file, VerificationError  # noqa: E402

DATA_JSON = (
    PROJ_ROOT
    / "src/specdraft/data/constants/data.json"
)

console = Console() if callable(Console) else Console


def _load_dataset():
    with DATA_JSON.open("r", encoding="utf8") as fp:
        return json.load(fp)


def _get_model_cfg() -> Dict[str, Any] | None:
    raw = os.getenv("MODEL_CFG")
    if not raw:
        return None
    try:
        return json.loads(raw)
    except json.JSONDecodeError as exc:
        console.print("[red]Invalid MODEL_CFG JSON:[/red]", exc)
        sys.exit(1)


def main() -> None:
    data = _load_dataset()
    model_cfg = _get_model_cfg()

    tmp_root = Path(os.getenv("LEAN_TMP_DIR", "/tmp/specdraft_runs")).expanduser()
    tmp_root.mkdir(parents=True, exist_ok=True)

    table = Table(title="SpecDraft Lean-generation evaluation", show_lines=True)
    table.add_column("Key")
    table.add_column("Lean file")
    table.add_column("Status")

    success = 0
    total = 0

    for key, entry in data.items():
        total += 1
        docstring = entry["doc"]
        # The generator currently only uses the docstring; we *could* also feed
        # the Python reference implementation by reading `entry["python"]`.

        try:
            lean_path = generate_lean_file(docstring, model_cfg=model_cfg, tmp_dir=tmp_root / key)
            verify_lean_file(lean_path)
            table.add_row(key, str(lean_path), "✅ pass")
            success += 1
        except VerificationError as exc:
            table.add_row(key, str(lean_path), f"❌ fail – {exc}")
        except Exception as exc:  # noqa: BLE001
            table.add_row(key, "—", f"❌ exception – {exc}")

    console.print(table)
    console.print(f"[bold]{success}/{total}[/bold] items passed verification.")

    # Exit code 0 ⇔ all passed; 1 otherwise
    sys.exit(0 if success == total else 1)


if __name__ == "__main__":
    main() 