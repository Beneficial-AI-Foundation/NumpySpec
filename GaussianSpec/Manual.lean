import VersoManual
import generated.Spec.Basic

open Verso Doc
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open generated.Spec

-- This file defines the minimal Verso *manual* that documents GaussianSpec.

#doc (Manual) "Gaussian elimination" =>

%%%
authors := ["GaussianSpec Agents"]
shortTitle := "GaussianSpec"
%%%

Welcome!  This short document introduces our Lean-formalised specification of Gaussian
elimination.  The purpose is two-fold:

1. Provide a public-facing artefact that management can read in a web browser with rich hovers
   and cross-references.
2. Establish the plumbing so that subsequent chapters of the textbook can be added by merely
   writing additional Verso-style `#doc` blocks.

{index}[Gaussian elimination]

# Definition

We define Gaussian elimination as a function that maps a square matrix to another matrix.
At present the implementation is a placeholder – it simply returns the inverse matrix.  The
important part is the *type* signature, which will stay stable as we tighten the
implementation.

```

# Specification

The key lemma we want to expose is that the result of Gaussian elimination is a **left inverse**
of the input matrix whenever the determinant is non-zero.

```

The proof is currently a one-liner `simp` because of our placeholder definition.  Replacing the
implementation will automatically surface any missing proof obligations – this is Lean's
verified feedback loop in action.

# Next Steps

In upcoming iterations we will:

* Replace the placeholder implementation with a bona-fide algorithm.
* Import Chapter 2 of the textbook, fleshing out the narrative and embedding worked examples.
* Add interactive exercises using Verso's `savedLean` blocks.

Stay tuned!

#doc (Manual) "Appendix A — Popcount example" =>

::: example "Popcount"

The function `popcount` returns the number of set bits in a 32-bit
bit-vector.  We present two Lean implementations and (sketch) a proof of
their equivalence.

```

def popcountSpec (x : BitVec 32) : BitVec 32 :=
  (List.range 32).foldl (fun pop i => pop + ((x >>> i) &&& 1)) 0

def popcount (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& BitVec.ofNat 32 0x55555555)
  let x := (x &&& BitVec.ofNat 32 0x33333333) + ((x >>> 2) &&& BitVec.ofNat 32 0x33333333)
  let x := (x + (x >>> 4)) &&& BitVec.ofNat 32 0x0F0F0F0F
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  x &&& BitVec.ofNat 32 0x0000003F

theorem popcount_correct : popcount = popcountSpec := by
  funext x
  -- `bv_decide` solves this, once imported: `bv_decide`
  sorry
```

:::
