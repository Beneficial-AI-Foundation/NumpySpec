import Std.Tactic.Do


open Std.Do

theorem mkFreshNat_spec [Monad m] [WPMonad m sh] :
  ⦃⌜#fst = n ∧ #snd = o⌝⦄
  (mkFreshNat : StateT (Nat × Nat) m Nat)
  ⦃⇓ r => ⌜r = n ∧ #fst = n + 1 ∧ #snd = o⌝⦄
