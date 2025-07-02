import Std.Do
open Std.Do

/--
`Add` is specified *inline*—its post‑condition lives directly in its return type, so we don’t need
an extra `…_spec` theorem.  Because `Vector` already carries its length `n`, the usual equal‑length
requirement is handled by the type checker.

In other words, a call to `Add a b` produces a value `⟨res, h⟩` where `res : Vector Int n` **and**
`h : ∀ i, res[i] = a[i] + b[i]`.  Clients can project either component as needed.
-/

constant Add {n : Nat}
  (a b : Vector Int n) :
  Σ' res : Vector Int n,        -- result vector
    (∀ i : Fin n, res.get i = a.get i + b.get i)
