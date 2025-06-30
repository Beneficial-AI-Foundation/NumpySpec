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

/-!
Below are additional placeholder stubs corresponding to other Dafny NumPy benchmarks.
They are *not* exhaustive yet (the original suite has about 43), but they
cover the most frequently-used operations so we can start linking Lean proofs
incrementally.  All come with a trivial specification lemma so the file
compiles while signalling the intended contract.
-/

namespace NumpySpec.DafnyBenchmarks

/-! Return the minimum of a non-empty list (`0` if empty, for now). -/
def listMin (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => (x :: xs).foldl (fun acc y => if y < acc then y else acc) x

theorem listMin_spec (xs : List Int) :
    listMin xs =
      match xs with
      | [] => 0
      | x :: xs => (x :: xs).foldl (fun acc y => if y < acc then y else acc) x := by
  cases xs <;> simp[listMin]

/-! Return the maximum of a non-empty list (`0` if empty). -/
def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => (x :: xs).foldl (fun acc y => if y > acc then y else acc) x

theorem listMax_spec (xs : List Int) :
    listMax xs =
      match xs with
      | [] => 0
      | x :: xs => (x :: xs).foldl (fun acc y => if y > acc then y else acc) x := by
  cases xs <;> simp[listMax]

/-! Compute the arithmetic mean as integer division. -/
def listMean (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | _  => (xs.foldl (· + ·) 0) / xs.length

theorem listMean_spec (xs : List Int) :
    listMean xs =
      match xs with
      | [] => 0
      | _  => (xs.foldl (· + ·) 0) / xs.length := by
  cases xs <;> simp[listMean]

/-! Dot product of two lists (truncates to shortest). -/
def dot (a b : List Int) : Int :=
  (List.zip a b).foldl (fun acc (p : Int × Int) => acc + p.fst * p.snd) 0

theorem dot_spec (a b : List Int) :
    dot a b = (List.zip a b).foldl (fun acc p => acc + p.fst * p.snd) 0 := by
  rfl

end NumpySpec.DafnyBenchmarks
