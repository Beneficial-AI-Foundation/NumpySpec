"""Cursor rule utilities – load `.cursor/rules/*.mdc` and provide helpers
for mapping source files to relevant rules.

This module is intentionally **pure** (no side-effects besides reading files)
so it can be imported freely by both local and remote (Morph-based) agents.
"""

from __future__ import annotations

from pathlib import Path
from functools import lru_cache
from typing import Iterable

__all__ = [
    "get_rules_for_file",
    "as_markdown_blocks",
]

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

# Root directory that stores Markdown rule cards.  We resolve relative to the
# *project* root (two levels up from this file – `src/gaussianspec/`).  This
# keeps the helper robust even when called from a vendored location.

_RULES_DIR = Path(__file__).resolve().parents[2] / ".cursor/rules"

# Mapping from *file suffix* → *rule names* (without .mdc extension).
# Automatically extracted by globbing the rules directory. New .mdc files
# matching "*<suffix>.mdc" will be picked up without manual updates.
_RULES_BY_SUFFIX: dict[str, tuple[str, ...]] = {
    suffix: tuple(sorted(p.stem for p in _RULES_DIR.glob(f"*{suffix}.mdc")))
    for suffix in (".lean", ".py")
}


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def _load_rule(rule_name: str) -> str | None:
    """Load *rule_name* (stem only) from `_RULES_DIR`.  Returns `None` if the
    file does not exist (robust to missing optional rules).
    """

    path = _RULES_DIR / f"{rule_name}.mdc"
    try:
        return path.read_text()
    except FileNotFoundError:
        return None


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def get_rules_for_file(file_path: Path | str) -> list[tuple[str, str]]:  # noqa: D401
    """Return **all** `(name, text)` rules that apply to *file_path*.

    The decision is purely extension-based for now but can be extended with
    more sophisticated heuristics (e.g. inspecting shebang, `import` lines)."""

    path = Path(file_path)
    rules: list[tuple[str, str]] = []
    for suffix, rule_names in _RULES_BY_SUFFIX.items():
        if path.suffix == suffix:
            for name in rule_names:
                text = _load_rule(name)
                if text is not None:
                    rules.append((name, text))
    return rules


def as_markdown_blocks(rules: Iterable[tuple[str, str]]) -> str:
    """Convert an iterable of `(name, text)` tuples into a single markdown
    block suitable for inclusion in assistant messages.
    """

    blocks: list[str] = []
    for name, text in rules:
        blocks.append(f"Cursor Rule ({name}):\n```\n{text}\n```\n")
    return "\n".join(blocks)
