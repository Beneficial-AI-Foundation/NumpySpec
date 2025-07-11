# Pre-/Post-condition (Hoare triple) syntax used in NumpySpec

This short note explains the miniature “Hoare logic” notation that appears in
the Lean files inside `NumpySpec/`.  The notation is provided by
`Std.Do.Triple` from the Lean 4 standard library and is very similar to the
one described in Markus Himmel’s blog post
“[My first verified imperative program](https://markushimmel.de/blog/my-first-verified-imperative-program/)”.
It allows us to attach **pre-conditions** and **post-conditions** to (possibly
imperative) Lean programs written in `do`-notation and to prove **Hoare
triples** of the form *{P} e {Q}*.

---

## 1. The concrete syntax

In the sources you will often find blocks that look like this:

```lean
theorem numpy_add_spec {n : Nat} (x₁ x₂ : Vector Float n) :
    ⦃⌜True⌝⦄                       -- ① pre-condition
    numpy_add x₁ x₂                -- ② program/expression being specified
    ⦃⇓ r =>                       -- ③ introduces the return value `r`
       ∀ i : Fin n, r.get i = x₁.get i + x₂.get i
    ⦄ := by
  -- proof elided
```

Reading the above line by line:

1. `⦃ P ⦄` – opening **curly braces** (`⦃ … ⦄` encoded as `\{{…\}}`) start a
   Hoare triple and contain the *pre-condition* `P`.
2. Next comes the *program* (here `numpy_add x₁ x₂`).  It can be any Lean
   term whose type is monadic – usually `Id α`, `ST σ α`, `EIO ε α`, …
   In `NumpySpec` we mostly use the identity monad `Id` because operations are
   pure.
3. A second pair of braces closes the triple and carries the *post-condition*.
   The keyword `⇓ r =>` (typed as `\⇓`) binds the **result value** of the
   expression so that the remainder of the post-condition may refer to it.

In other words the syntax corresponds 1:1 to the mathematical Hoare triple

    { P }   e   { λ r, Q r }

where `P : Prop`, `e : m α`, and `Q : α → Prop`.

### 1.1 Embedding plain propositions – `⌜ … ⌝`

`Std.Do.Triple` represents assertions as functions on the _state_ of the monad
(`State` for `ST`, *unit* for `Id`, …).  When the assertion is **state
independent** (the common case in `NumpySpec`) we use the quoting brackets
`⌜ P ⌝` to coerce a plain `Prop` into the required type.  For instance

```lean
⦃⌜True⌝⦄      -- no requirements
⦃⌜x ≠ 0⌝⦄     -- pre-condition that x is non-zero
```

### 1.2 Omitting the result

If you are not interested in the return value you can write `⇓ _ =>` or even
`·` (a placeholder variable) – Lean’s binder syntax applies unchanged:

```lean
⦃λ _ ⇒ True⦄    prog ⦃⇓ _ => /* post independent of result */⦄
```

---

## 2. Intuition + connection to the Markus Himmel article

Markus Himmel shows how to verify a small in-place array reversal written in
imperative `do`-notation.  The same underlying API is used here – we merely
apply it to *pure, functional* wrappers around NumPy routines.  The triple
notation hides the plumbing of `Std.Hoare`:

*   `⦃P⦄ e ⦃⇓r => Q⦄` is syntactic sugar for `Triple P (fun r => Q) e`.
*   Theorems such as `Triple.return`, `Triple.bind`, `Triple.assert` allow us
    to prove larger specifications by composition, exactly like the rules in
    classical Hoare logic.

Because most functions in `NumpySpec` are *pure*, the state type of the monad
is trivial and proofs boil down to ordinary reasoning about arithmetic,
vectors, etc.  Nevertheless the same mechanism seamlessly scales to
state-ful code, IO, or exceptions should we need them later.

---

## 3. Cheatsheet

| Goal you want to prove                         | Syntax example |
|------------------------------------------------|----------------|
| Pure function `f : α → β` satisfies `Q`        | `⦃⌜P x⌝⦄ f x ⦃⇓ r => Q x r⦄` |
| Function that may fail, `EIO ε β`              | `⦃P⦄ foo ⦃⇓ r | _ => Q r⦄` |
| Ignore result and only prove termination       | `⦃P⦄ bar ⦃⇓ _ => True⦄` |
| Require asymmetry w.r.t. initial state `s`     | `⦃λ s => P s⦄ … |

---

## 4. Practical tips

* Use `simp` and `dsimp` frequently – many post-conditions collapse to
  straightforward algebra after unfolding definitions.
* Start your proofs with `intro`/`intros` to name arguments, then `simp`, then
  fill the remaining goals with `rw` or `ring`.
* For very small functions you can get away with `by simp`.
* If a function is only a thin wrapper around an existing Lean definition
  consider using `exact` together with an appropriate lemma instead of a fresh
  proof term.

---

_Happy verifying!_
