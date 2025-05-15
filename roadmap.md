# Verso Integration Roadmap

## Context

GaussianSpec now uses Lean 4.  We want Verso to become the primary documentation engine that morph agents employ when converting *Numerical Recipes in C* into a Lean‐buildable book.  The first incremental milestone is to ingest Chapter 2 (Solution of Linear Equations) **as pure prose** and compile it through Verso.

---

## High-Level Goals

1. Introduce Verso **only** inside the generated sub-project – keep the root Lake project untouched.
2. Provide agents with clear persistent rules for how to search the Verso repo and author content.
3. Replace the ad-hoc `generated/Spec/Spec.lean` pipeline by an agent-driven Verso book.
4. Add Justfile commands to build and refresh the book.
5. Achieve a compiling prose-only Chapter 2 as the first pass.

---

## Directory Layout After This Milestone

```text
/ (root)
 ├─ Justfile               # updated with book targets
 ├─ generated/
 │   ├─ versobook/         # **new** Lake project holding the Verso book
 │   │   ├─ lakefile.lean
 │   │   └─ Book/
 │   │       └─ Chapter2.lean  # created by agents
 │   └─ Numerical_Recipes_in_C_1-149.txt  # OCR source
 └─ .cursor/rules/
     └─ verso-agents.mdc   # persistent agent instructions
```

---

## Detailed Tasks

### 1 — Create `generated/versobook` Lake Project

* `lakefile.lean`:

  ```lean
  package versobook
  require verso from git "https://github.com/leanprover/verso" @ "main"
  ```

* Initial Lean file `Book/Main.lean` can simply `import Verso`.

### 2 — Update Justfile

```make
# Build the prose-only Verso book
build-book:
    cd generated/versobook && lake build Versobook

# Regenerate Chapter 2 via agents
refresh-book:
    uv run src/gaussianspec/build_book_agents.py
```

### 3 — Add Persistent Cursor Rule `verso-agents.mdc`

Key points:

* Agents must `#search @https://github.com/leanprover/verso` for usage samples.
* Use guillemets as raw identifiers to map textbook sections to modules (e.g. `namespace «2»`, `namespace«2».«1»`. `namespace«2.1»` is NOT correct).
* First pass dumps OCR text as prose.
* Divide-and-conquer per section.
* Compilation via `build-book`.

### 4 — Driver Script Stub `src/gaussianspec/build_book_agents.py`

* Reads `generated/Numerical_Recipes_in_C_1-149.txt`.
* Spawns o3 morph agents, each assigned chunk ranges.
* Agents write Verso markdown/Lean into `Book/Chapter2.lean`.


### 5 — Cleanup

* Delete `generated/Spec/Spec.lean` once agents take over.
* Update `CHANGELOG.md` with timestamped entry for this roadmap.

---

## Acceptance Criteria

- `just build-book` completes without errors (Verso compiles).
* `Book/Chapter2.lean` contains Chapter 2 prose subdivided into Verso sections.
* No Lean code authored manually – only agent-generated.
* Root Lake build remains unaffected.

---

## Future Work

* Subsequent passes: insert Lean snippets, exercises, and verified proofs.
* Extend agents to handle images (feed relevant page scans).
* Migrate further chapters iteratively.
* Implement testing harness that ensures Verso book builds in CI.

## Next Up (2025-05-14:22:39)

* Bump versions of all dependencies (Lean toolchain, mathlib, Verso, etc.) so that Verso can be added "with canonical".
* Integrate Verso into the canonical dependency set and verify that `lake build` succeeds end-to-end on the upgraded stack.
* Publish the rendered textbook as a static website served by a lightweight HTTP server (e.g. `python -m http.server` or Caddy) so that a demo link can be shared easily (goal: showcase progress to stakeholders).
* Automate deployment via a `just deploy-site` target and a GitHub Pages workflow.

## Upstream LeanTool Packaging Fix (2025-05-15)

We now rely on LeanTool as an MCP server.  A temporary local patch works but we should upstream a proper fix so that
`leantool` can be consumed as a normal PyPI / git dependency.

**Objective for next agent**: fork + patch LeanTool automatically via the `hub` CLI.

- [ ] Use `hub fork GasStationManager/LeanTool` (creates `<user>/LeanTool` fork).
- [ ] `hub clone <user>/LeanTool` into a throw-away worktree (`.worktrees/leantool-fix`).
- [ ] Apply the minimal packaging fix:
  1. `rm leantool.py` (duplicate top-level module)
  2. Delete the `[tool.poetry] packages = [...]` stanza if present or adjust it to `packages = [{ include = "leantool" }]`.
  3. Commit as `fix: remove duplicate module & let poetry auto-discover package`.
- [ ] Push branch `packaging-fix` and open PR against upstream via `hub pull-request` with title **"Fix wheel build: remove duplicate module file"**.
- [ ] Tag the commit `v0.3.0+packaging-fix` on the fork so our `pyproject.toml` can pin to a stable ref.
- [ ] Amend `pyproject.toml`:
  ```toml
  pantograph>=0.3.1  #→ keep
  leantool @ git+https://github.com/<user>/LeanTool.git@v0.3.0+packaging-fix
  ```
  also add an `uv` git-sha override.
- [ ] Remove `scripts/install_leantool.py`, `scripts/ensure_pantograph_wheel.py` and matching Justfile logic.
- [ ] Run `uv sync` and verify:
  * `leanmcp` console script is on `$PATH`.
  * `just sync` is now a one-liner.
- [ ] Update `CHANGELOG.md` with timestamp and summary.
- [ ] Push branch `lean-tool-cleanup` and open internal PR.

Outcome: reproducible, declarative dependency set; no imperative wheel hacking.

## LeanTool Poetry → UV Migration (2025-05-15:03:51)

The LeanTool fork stored in `.worktrees/leantool-fix` has been migrated off Poetry.

* Replaced the old `[tool.poetry]` section in `pyproject.toml` with a PEP 621 `[project]` table and the Hatchling build backend.
* Declared runtime dependencies inline so they are automatically picked up by `uv`.
* Added console entry-points:
  * `leanmcp` → `leanmcp:main`
  * `leantool-chat` → `cli_chat:main`
  * `leantool-app` → `app:main`
* Minimum supported Python bumped to 3.12 to stay in lock-step with the parent workspace.

Next actions:

- [x] Commit & push branch `packaging-fix` to the LeanTool fork and tag `v0.4.1+uv`.
- [x] Update the root `pyproject.toml` to depend on the new tag.
- [x] Run `uv sync` at the workspace root and ensure `leanmcp` is discoverable on `$PATH`.
- [ ] Remove any Poetry-specific artefacts that may still exist (e.g. lock-files, GitHub workflows).
