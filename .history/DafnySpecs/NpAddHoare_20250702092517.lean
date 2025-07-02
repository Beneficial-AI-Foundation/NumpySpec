import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Element-wise addition of two arrays -/
def add (a b : Array Int): Id (Array Int) := do
  let mut res := Array.emptyWithCapacity a.size
  for ha : i in [0:min a.size b.size] do
    have : i < min a.size b.size := by get_elem_tactic
    have : i < a.size := by grind
    have : i < b.size := by grind
    res := res.push (a[i] + b[i])
  return res

theorem add_spec (a b : Array Int) (h : a.size = b.size) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⇓r => r.size = a.size ∧ ∀ i (hi : i < r.size), r[i] = a[i]'(by simp[h]; exact hi) + b[i]'(by simp[h]; exact hi)⦄ := by
  mvcgen [add]
  case inv =>
    exact ⇓ (r, is) =>
      r.size = is.pref.length ∧
      (∀ i (hi : i < r.size), r[i] = a[i]'(by have : i < a.size := by sorry; exact this) + b[i]'(by have : i < b.size := by sorry; exact this))
  case init =>
    simp_all
    constructor
    · rfl
    · intro i hi
      simp at hi
      omega
  case step =>
    intro a' b' h' res rpref x hx suff heq hinv
    simp at hinv
    obtain ⟨hr, hinv⟩ := hinv
    constructor
    · simp[hr]
    · intro i hi
      simp[Array.get_push]
      by_cases h : i < res.size
      · simp[h]
        exact hinv i h
      · simp[h]
        have : i = res.size := by
          simp[hr] at hi
          omega
        subst this
        simp[h'] at hx
        have : x < a'.size := by
          have : x < min a'.size b'.size := hx
          simp[Nat.min_def] at this
          split_ifs at this <;> omega
        have : x < b'.size := by
          have : x < min a'.size b'.size := hx
          simp[Nat.min_def] at this
          split_ifs at this <;> omega
        simp[hr]
        have : x = rpref.length := by
          sorry -- This requires reasoning about the iteration structure
        subst this
        rfl
  case term =>
    simp_all
    intro res ⟨hr, hinv⟩
    constructor
    · simp[h] at hr
      exact hr
    · exact hinv
