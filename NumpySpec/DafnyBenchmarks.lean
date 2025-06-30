/-!
# Dafny Numpy Specs (Stubs)

These stubs mirror the Dafny benchmark specifications in the `vericoding` repo
  (see <https://github.com/Beneficial-AI-Foundation/vericoding/tree/main/dafny/benchmarks/numpy_specs>).

For now they contain only *comments* describing the expected behaviour together
with Lean placeholders (`sorry`).  They compile, allowing the rest of the
`lake build` pipeline to succeed.

Each spec will later be replaced by a proper Lean definition plus a proof using
MPL (`Std.Do.Triple`).
-/

namespace NumpySpec.DafnyBenchmarks

/-!
Stub for `sum.dfy`

Dafny spec excerpt:

```dafny
method sum(a: array<int>) returns (s: int)
  ensures s == (* sum of elements in a *)
```
-/

def sum (a : List Int) : Int :=
  -- TODO: implement with fold once verified
  (a.foldl (· + ·) 0)

theorem sum_spec (a : List Int) : sum a = a.foldl (· + ·) 0 := by
  -- trivial proof until we refine the spec
  rfl

/-!
Stub for `prod.dfy`

```dafny
method prod(a: array<int>) returns (p: int)
  ensures p == (* product of elements in a *)
```
-/

def prod (a : List Int) : Int :=
  a.foldl (· * ·) 1

theorem prod_spec (a : List Int) : prod a = a.foldl (· * ·) 1 := by
  rfl

end NumpySpec.DafnyBenchmarks
