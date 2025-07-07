import Lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Grind Tactic Examples

This file contains concrete examples of the `grind` tactic for AI's benefit.

## Overview

The `grind` tactic is a powerful automated theorem prover that can solve goals
using a combination of:
- Equational reasoning
- Congruence closure
- SMT-style reasoning
- E-matching (equality matching)
- Forward reasoning with lemmas marked with `@[grind]`

Think of it as a "workhorse tactic" that can fill in many routine proofs automatically.

## Key Features

1. **Automatic instantiation**: grind can automatically instantiate universally
   quantified lemmas when it finds matching patterns
2. **Congruence closure**: understands that `f x = f y` when `x = y`
3. **Theory reasoning**: has built-in support for arithmetic, arrays, etc.
4. **Forward chaining**: applies lemmas marked with `@[grind]` automatically

-/

namespace GrindExamples

section BasicExamples

/-- Example 1: Basic equality reasoning -/
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind

/-- Example 2: Function congruence -/
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by
  grind

/-- Example 3: Combining hypotheses with arithmetic -/
example (x y z : Nat) (h1 : x + y = 10) (h2 : y = 3) : x + 3 = 10 := by
  grind

/-- Example 4: Simple contradiction detection -/
example (a : Nat) (h1 : a = 5) (h2 : a ≠ 5) : False := by
  grind

end BasicExamples

section ArithmeticReasoning

/-- Example 5: Arithmetic with inequalities -/
example (x y : Nat) (h1 : x < y) (h2 : y < 10) : x < 10 := by
  grind

/-- Example 6: Mixed arithmetic reasoning -/
example (a b c : Nat) (h1 : a + b = c) (h2 : b = 2) (h3 : c = 7) : a = 5 := by
  grind

/-- Example 7: Commutativity and associativity -/
example (x y z : Nat) : x + (y + z) = z + (x + y) := by
  grind

end ArithmeticReasoning

section ConditionalReasoning

/-- Example 8: If-then-else reasoning -/
example (p : Prop) [Decidable p] (a b : Nat) :
  (if p then a else b) = a ∨ (if p then a else b) = b := by
  grind

/-- Example 9: Case analysis with grind -/
example (n : Nat) : n = 0 ∨ n > 0 := by
  grind

end ConditionalReasoning

section ArrayReasoning

/-- Example 10: Array get/set reasoning -/
example (arr : Array Nat) (i : Fin arr.size) (v : Nat) :
  (arr.set i v).get i = v := by
  grind

/-- Example 11: Array size preservation -/
example (arr : Array Nat) (i : Fin arr.size) (v : Nat) :
  (arr.set i v).size = arr.size := by
  simp  -- grind doesn't handle this directly, showing its limitations

end ArrayReasoning

section CustomLemmas

/-- A custom lemma that grind can use -/
@[grind]
theorem double_is_even (n : Nat) : ∃ k, 2 * n = 2 * k := by
  use n

/-- Example 12: Using custom lemmas marked with @[grind] -/
example (x : Nat) : ∃ k, 2 * x = 2 * k := by
  grind

/-- Another custom lemma for grind -/
@[grind]
theorem add_comm_custom (a b : Nat) : a + b = b + a := Nat.add_comm a b

/-- Example 13: grind uses our custom lemmas automatically -/
example (x y : Nat) (h : y + x = 10) : x + y = 10 := by
  grind

end CustomLemmas

section AdvancedExamples

/-- Example 14: Nested function applications -/
example (f g : Nat → Nat) (x : Nat) (h1 : f x = 5) (h2 : g 5 = 10) :
  g (f x) = 10 := by
  grind

/-- Example 15: Existential instantiation -/
example (P : Nat → Prop) (h : ∃ x, P x ∧ x > 5) :
  ∃ y, P y := by
  grind

/-- Example 16: Pattern matching with structures -/
structure Point where
  x : Nat
  y : Nat

example (p q : Point) (h : p.x = q.x ∧ p.y = q.y) : p = q := by
  cases p
  cases q
  grind

end AdvancedExamples

section ComparisonWithOtherTactics

/-- Example 17: Where grind shines vs simp -/
example (f : Nat → Nat) (a b c : Nat) 
  (h1 : f a = b) (h2 : f b = c) (h3 : a = b) : f a = c := by
  -- simp [h1, h2, h3] -- would need careful ordering
  grind  -- handles it automatically

/-- Example 18: Where grind helps vs manual proof -/
example (x y z w : Nat) 
  (h1 : x + y = z) (h2 : z = w) (h3 : y = 2) (h4 : w = 10) : x = 8 := by
  -- Manual proof would need several steps
  -- rw [h3] at h1
  -- rw [h2] at h1
  -- rw [h4] at h1
  -- linarith
  grind  -- does it all at once

end ComparisonWithOtherTactics

section Limitations

/-- Example 19: grind has limits - complex arithmetic -/
example (n : Nat) (h : n > 0) : n * n + 2 * n + 1 = (n + 1) * (n + 1) := by
  -- grind  -- might timeout or fail
  ring  -- better tool for this job

/-- Example 20: grind doesn't do induction -/
theorem nat_induction_example (P : Nat → Prop) 
  (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  -- grind  -- won't work
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hs n ih

end Limitations

section PracticalTips

/-!
## Tips for using grind effectively:

1. **Mark helper lemmas with @[grind]**: This lets grind use them automatically
2. **Use grind for "obvious" steps**: It's great at combining simple facts
3. **Combine with other tactics**: Use grind to simplify before specialized tactics
4. **Set time limits**: `grind (timeout := 5000)` to avoid long waits
5. **Check grind's output**: Use `trace.grind` to see what grind is doing

## When to use grind:

- Combining multiple equality and inequality facts
- Simple arithmetic reasoning
- Propagating equalities through function applications
- Finding simple contradictions
- Instantiating existentials with obvious witnesses

## When NOT to use grind:

- Complex arithmetic (use `ring` or `linarith`)
- Inductive proofs (use `induction`)
- Simplification with many rewrite rules (use `simp`)
- Category theory or advanced algebra (use specialized tactics)

-/

/-- Example 21: Practical combination of tactics -/
example (a b c : Nat) (h1 : a * b = c) (h2 : b = 2) (h3 : a = c / 2) : 
  c = 2 * (c / 2) := by
  -- First use grind to establish basic facts
  have : a * 2 = c := by grind
  -- Then use specialized tactics for the division reasoning
  sorry  -- Would need more careful handling of division

/-- Example 22: Using grind with custom instances -/
class MyRelation (α : Type) where
  rel : α → α → Prop
  rel_trans : ∀ a b c, rel a b → rel b c → rel a c

instance : MyRelation Nat where
  rel := (· ≤ ·)
  rel_trans := Nat.le_trans

@[grind]
theorem MyRelation.trans_lemma {α : Type} [MyRelation α] (a b c : α)
  (h1 : MyRelation.rel a b) (h2 : MyRelation.rel b c) : MyRelation.rel a c :=
  MyRelation.rel_trans a b c h1 h2

example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  have : MyRelation.rel x y := h1
  have : MyRelation.rel y z := h2
  grind

end PracticalTips

end GrindExamples

/-!
## Summary

The `grind` tactic is a powerful addition to Lean 4's tactic library. It excels at:
- Combining multiple simple facts
- Propagating equalities
- Basic arithmetic reasoning
- Using lemmas marked with @[grind]

Think of it as a "smart auto" tactic that can handle many routine proof steps
without requiring manual guidance. It's particularly useful in the middle of proofs
where you need to combine several hypotheses to reach a conclusion.

For AI systems learning to write Lean proofs, grind is an excellent tool to try
when the goal seems "obviously" true from the hypotheses. If grind succeeds, it
saves writing out tedious proof steps. If it fails, you know you need more
sophisticated reasoning.
-/