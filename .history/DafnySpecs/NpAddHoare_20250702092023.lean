import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

def add (a b : Array Int): Id (Array Int) := do
  let mut res := Array.emptyWithCapacity a.size
  for ha : i in [0:min a.size b.size] do
    have : i < min a.size b.size := by get_elem_tactic
    have : i < a.size := by grind
    have : i < b.size := by grind
    res := res.push (a[i] + b[i])
  return res

@[grind →]
theorem range_elim : List.range' s n = xs ++ i :: ys → i = s + xs.length := by
  intro h
  induction xs generalizing s n
  case nil => cases n <;> simp_all[List.range']
  case cons head tail ih =>
    cases n <;> simp[List.range'] at h
    have := ih h.2
    simp[ih h.2]
    omega

theorem add_spec (a b : Vector Int n) (h : a.size = b.size) :
    ⦃⌜True⌝⦄
    add a b
    ⦃⇓r => ∃ hr : r.size = a.size, ∀ i: Fin a.size, r[i] = a.get i + b.get i⦄ := by
  mvcgen [add]
  case inv => exact ⇓ (r, is) => ∃ hr : r.size = is.pref.length, ∀ i (hr : i < r.size) (ha : i < a.size), r[i] = a.get i + b.get i
  all_goals simp_all; try grind
