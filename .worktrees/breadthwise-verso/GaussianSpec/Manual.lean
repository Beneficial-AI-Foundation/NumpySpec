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

```lean
#check gaussianElimination
```

# Specification

The key lemma we want to expose is that the result of Gaussian elimination is a **left inverse**
of the input matrix whenever the determinant is non-zero.

```lean
#check gaussianElimination_is_left_inverse
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
