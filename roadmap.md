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
