# NumPy Functions Formal Specification Table

This document provides formal specifications for core NumPy functions, focusing on int/rational valued functions that can be exactly verified. The table includes both Dafny and Lean 4 specifications, with particular attention to bitvec support for finite types.

## Core Mathematical Operations

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **np.add** | `method Add(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] + b[i]` | Element-wise addition of two arrays of the same shape. Result has same shape and each element is the sum of corresponding elements. | ✓ | `def add : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector ℤ n` | `fun a b => Vector.zipWith (· + ·) a b` | `BitVec.add` for fixed-width |
| **np.multiply** | `method Multiply(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] * b[i]` | Element-wise multiplication of two arrays. Each result element is the product of corresponding input elements. | ✓ | `def multiply : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector ℤ n` | `fun a b => Vector.zipWith (· * ·) a b` | `BitVec.mul` with overflow handling |
| **np.subtract** | `method Subtract(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] - b[i]` | Element-wise subtraction. Each result element is the difference between corresponding input elements. | ✓ | `def subtract : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector ℤ n` | `fun a b => Vector.zipWith (· - ·) a b` | `BitVec.sub` with underflow handling |
| **np.floor_divide** | `method FloorDivide(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < b.Length ==> b[i] != 0`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] / b[i]` | Element-wise floor division. Each result element is the floor of the division of corresponding elements. | ✓ | `def floor_divide : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector ℤ n` | `fun a b => Vector.zipWith (· / ·) a b` | `BitVec.udiv` and `BitVec.sdiv` |
| **np.mod** | `method Mod(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < b.Length ==> b[i] != 0`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] % b[i]` | Element-wise modulo operation. Each result element is the remainder of division of corresponding elements. | ✓ | `def mod : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector ℤ n` | `fun a b => Vector.zipWith (· % ·) a b` | `BitVec.umod` and `BitVec.smod` |
| **np.power** | `method Power(a: array<int>, b: array<nat>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == Pow(a[i], b[i])` | Element-wise exponentiation. Each result element is the first element raised to the power of the second element. | ✓ | `def power : {n : ℕ} → Vector ℤ n → Vector ℕ n → Vector ℤ n` | `fun a b => Vector.zipWith (· ^ ·) a b` | Requires overflow detection |

## Bitwise Operations

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **np.bitwise_and** | `method BitwiseAnd(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseAnd(a[i], b[i])` | Element-wise bitwise AND operation on integer arrays. | ✓ | `def bitwise_and : {n w : ℕ} → Vector (BitVec w) n → Vector (BitVec w) n → Vector (BitVec w) n` | `fun a b => Vector.zipWith (· &&& ·) a b` | Native `BitVec.and` operation |
| **np.bitwise_or** | `method BitwiseOr(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseOr(a[i], b[i])` | Element-wise bitwise OR operation on integer arrays. | ✓ | `def bitwise_or : {n w : ℕ} → Vector (BitVec w) n → Vector (BitVec w) n → Vector (BitVec w) n` | `fun a b => Vector.zipWith (· ||| ·) a b` | Native `BitVec.or` operation |
| **np.bitwise_xor** | `method BitwiseXor(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseXor(a[i], b[i])` | Element-wise bitwise XOR operation on integer arrays. | ✓ | `def bitwise_xor : {n w : ℕ} → Vector (BitVec w) n → Vector (BitVec w) n → Vector (BitVec w) n` | `fun a b => Vector.zipWith (· ^^^ ·) a b` | Native `BitVec.xor` operation |
| **np.invert** | `method Invert(a: array<int>) returns (res: array<int>)`<br/>`requires a.Length >= 0`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == BitwiseNot(a[i])` | Element-wise bitwise NOT operation on integer array. | ✓ | `def invert : {n w : ℕ} → Vector (BitVec w) n → Vector (BitVec w) n` | `fun a => Vector.map (~~~·) a` | Native `BitVec.not` operation |
| **np.left_shift** | `method LeftShift(a: array<int>, b: array<nat>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < b.Length ==> b[i] < 64`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] << b[i]` | Element-wise left shift of bits. Shift amount must be less than word size. | ✓ | `def left_shift : {n w : ℕ} → Vector (BitVec w) n → Vector ℕ n → Vector (BitVec w) n` | `fun a b => Vector.zipWith (· <<< ·) a b` | `BitVec.shiftLeft` with bounds check |
| **np.right_shift** | `method RightShift(a: array<int>, b: array<nat>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < b.Length ==> b[i] < 64`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] >> b[i]` | Element-wise right shift of bits. Shift amount must be less than word size. | ✓ | `def right_shift : {n w : ℕ} → Vector (BitVec w) n → Vector ℕ n → Vector (BitVec w) n` | `fun a b => Vector.zipWith (· >>> ·) a b` | `BitVec.ushiftRight` for logical |

## Comparison Operations

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **np.equal** | `method Equal(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] == b[i])` | Element-wise equality comparison. Returns boolean array indicating which elements are equal. | ✓ | `def equal : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· = ·) a b` | Direct comparison for `BitVec` |
| **np.not_equal** | `method NotEqual(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] != b[i])` | Element-wise inequality comparison. Returns boolean array indicating which elements are not equal. | ✓ | `def not_equal : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· ≠ ·) a b` | Direct comparison for `BitVec` |
| **np.less** | `method Less(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] < b[i])` | Element-wise less than comparison. Returns boolean array indicating which elements satisfy the condition. | ✓ | `def less : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· < ·) a b` | `BitVec.slt` for signed comparison |
| **np.greater** | `method Greater(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] > b[i])` | Element-wise greater than comparison. Returns boolean array indicating which elements satisfy the condition. | ✓ | `def greater : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· > ·) a b` | `BitVec.slt` with arguments swapped |
| **np.less_equal** | `method LessEqual(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] <= b[i])` | Element-wise less than or equal comparison. | ✓ | `def less_equal : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· ≤ ·) a b` | `BitVec.sle` for signed comparison |
| **np.greater_equal** | `method GreaterEqual(a: array<int>, b: array<int>) returns (res: array<bool>)`<br/>`requires a.Length == b.Length`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == (a[i] >= b[i])` | Element-wise greater than or equal comparison. | ✓ | `def greater_equal : {n : ℕ} → Vector ℤ n → Vector ℤ n → Vector Bool n` | `fun a b => Vector.zipWith (· ≥ ·) a b` | `BitVec.sle` with arguments swapped |

## Array Manipulation

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **np.sum** | `method Sum(a: array<int>) returns (res: int)`<br/>`ensures res == SumArray(a, 0, a.Length)`<br/>`function SumArray(a: array<int>, start: int, end: int): int`<br/>`requires 0 <= start <= end <= a.Length` | Computes the sum of all elements in the array. | ✓ | `def sum : {n : ℕ} → Vector ℤ n → ℤ` | `fun a => a.toList.sum` | Overflow considerations for fixed-width |
| **np.prod** | `method Prod(a: array<int>) returns (res: int)`<br/>`ensures res == ProdArray(a, 0, a.Length)`<br/>`function ProdArray(a: array<int>, start: int, end: int): int`<br/>`requires 0 <= start <= end <= a.Length` | Computes the product of all elements in the array. | ✓ | `def prod : {n : ℕ} → Vector ℤ n → ℤ` | `fun a => a.toList.prod` | Overflow considerations for fixed-width |
| **np.cumsum** | `method CumSum(a: array<int>) returns (res: array<int>)`<br/>`ensures res.Length == a.Length`<br/>`ensures res.Length > 0 ==> res[0] == a[0]`<br/>`ensures forall i :: 1 <= i < a.Length ==> res[i] == res[i-1] + a[i]` | Computes cumulative sum of array elements. Each element is the sum of all previous elements including current. | ✓ | `def cumsum : {n : ℕ} → Vector ℤ n → Vector ℤ n` | `fun a => Vector.scanl (· + ·) 0 a` | Overflow tracking needed |
| **np.cumprod** | `method CumProd(a: array<int>) returns (res: array<int>)`<br/>`ensures res.Length == a.Length`<br/>`ensures res.Length > 0 ==> res[0] == a[0]`<br/>`ensures forall i :: 1 <= i < a.Length ==> res[i] == res[i-1] * a[i]` | Computes cumulative product of array elements. Each element is the product of all previous elements including current. | ✓ | `def cumprod : {n : ℕ} → Vector ℤ n → Vector ℤ n` | `fun a => Vector.scanl (· * ·) 1 a` | Overflow tracking needed |
| **np.max** | `method Max(a: array<int>) returns (res: int)`<br/>`requires a.Length > 0`<br/>`ensures exists i :: 0 <= i < a.Length && res == a[i]`<br/>`ensures forall i :: 0 <= i < a.Length ==> a[i] <= res` | Returns the maximum element in the array. Array must be non-empty. | ✓ | `def max : {n : ℕ} → Vector ℤ (n+1) → ℤ` | `fun a => a.toList.maximum` | `BitVec.smax` for signed max |
| **np.min** | `method Min(a: array<int>) returns (res: int)`<br/>`requires a.Length > 0`<br/>`ensures exists i :: 0 <= i < a.Length && res == a[i]`<br/>`ensures forall i :: 0 <= i < a.Length ==> res <= a[i]` | Returns the minimum element in the array. Array must be non-empty. | ✓ | `def min : {n : ℕ} → Vector ℤ (n+1) → ℤ` | `fun a => a.toList.minimum` | `BitVec.smin` for signed min |

## Advanced Operations

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **np.gcd** | `method GCD(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> GCDInt(a[i], b[i]) == res[i]` | Element-wise greatest common divisor. Computes GCD of corresponding elements in two arrays. | ✓ | `def gcd : {n : ℕ} → Vector ℕ n → Vector ℕ n → Vector ℕ n` | `fun a b => Vector.zipWith Nat.gcd a b` | Extended Euclidean for `BitVec` |
| **np.lcm** | `method LCM(a: array<int>, b: array<int>) returns (res: array<int>)`<br/>`requires a.Length == b.Length`<br/>`requires forall i :: 0 <= i < a.Length ==> a[i] >= 0 && b[i] >= 0`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> LCMInt(a[i], b[i]) == res[i]` | Element-wise least common multiple. Computes LCM of corresponding elements in two arrays. | ✓ | `def lcm : {n : ℕ} → Vector ℕ n → Vector ℕ n → Vector ℕ n` | `fun a b => Vector.zipWith Nat.lcm a b` | May require arbitrary precision |
| **np.abs** | `method Abs(a: array<int>) returns (res: array<int>)`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] == AbsInt(a[i])`<br/>`ensures forall i :: 0 <= i < a.Length ==> res[i] >= 0` | Element-wise absolute value. Returns array with absolute values of input elements. | ✓ | `def abs : {n : ℕ} → Vector ℤ n → Vector ℕ n` | `fun a => Vector.map Int.natAbs a` | Special handling for `BitVec` min value |
| **np.sign** | `method Sign(a: array<int>) returns (res: array<int>)`<br/>`ensures res.Length == a.Length`<br/>`ensures forall i :: 0 <= i < a.Length ==> `<br/>`  (a[i] > 0 ==> res[i] == 1) &&`<br/>`  (a[i] == 0 ==> res[i] == 0) &&`<br/>`  (a[i] < 0 ==> res[i] == -1)` | Element-wise sign function. Returns -1, 0, or 1 depending on sign of each element. | ✓ | `def sign : {n : ℕ} → Vector ℤ n → Vector (Fin 3) n` | `fun a => Vector.map Int.sign a` | Sign bit extraction for `BitVec` |

## Helper Functions and Predicates

| Function | Formal spec (Dafny) | Informal spec | Auto-informalized | Auto-formalized type signatures (Lean) | Lean implementation | Bitvec considerations |
|----------|---------------------|---------------|-------------------|----------------------------------------|-------------------|----------------------|
| **ValidArray** | `predicate ValidArray<T>(a: array<T>)`<br/>`{ a.Length >= 0 }` | Predicate that checks if an array is valid (non-negative length). | ✓ | `def ValidArray : {α : Type} {n : ℕ} → Vector α n → Prop` | `fun _ => True` | Always true for `Vector` |
| **SameShape** | `predicate SameShape<T,U>(a: array<T>, b: array<U>)`<br/>`{ a.Length == b.Length }` | Predicate that checks if two arrays have the same shape (length). | ✓ | `def SameShape : {α β : Type} {n : ℕ} → Vector α n → Vector β n → Prop` | `fun _ _ => True` | Always true for same-indexed `Vector` |
| **AllPositive** | `predicate AllPositive(a: array<int>)`<br/>`{ forall i :: 0 <= i < a.Length ==> a[i] > 0 }` | Predicate that checks if all elements in an integer array are positive. | ✓ | `def AllPositive : {n : ℕ} → Vector ℤ n → Prop` | `fun a => ∀ x ∈ a.toList, x > 0` | Check all bits for `BitVec` interpretation |
| **AllNonNegative** | `predicate AllNonNegative(a: array<int>)`<br/>`{ forall i :: 0 <= i < a.Length ==> a[i] >= 0 }` | Predicate that checks if all elements in an integer array are non-negative. | ✓ | `def AllNonNegative : {n : ℕ} → Vector ℤ n → Prop` | `fun a => ∀ x ∈ a.toList, x ≥ 0` | Sign bit check for `BitVec` |

## Addenda: Dafny BitString Functions in Lean 4

Based on the provided Dafny specification, here are the equivalent Lean 4 implementations using `BitVec`:

| Dafny Function | Lean 4 Equivalent | Implementation |
|----------------|-------------------|----------------|
| **Add** | `BitVec.add` | `def bitstring_add {n : ℕ} : BitVec n → BitVec n → BitVec n := BitVec.add` |
| **Mul** | `BitVec.mul` | `def bitstring_mul {n : ℕ} : BitVec n → BitVec n → BitVec n := BitVec.mul` |
| **Sub** | `BitVec.sub` | `def bitstring_sub {n : ℕ} : BitVec n → BitVec n → BitVec n := BitVec.sub` |
| **DivMod** | `BitVec.udiv`/`BitVec.umod` | `def bitstring_divmod {n : ℕ} (a b : BitVec n) : BitVec n × BitVec n := (BitVec.udiv a b, BitVec.umod a b)` |
| **Compare** | `BitVec.ult`/`BitVec.slt` | `def bitstring_compare {n : ℕ} (a b : BitVec n) : Int := if a < b then -1 else if a = b then 0 else 1` |
| **ModExp** | Custom implementation | `def bitstring_modexp {n : ℕ} : BitVec n → BitVec n → BitVec n → BitVec n := sorry -- requires implementation` |
| **ValidBitString** | Type constraint | `BitVec n` type automatically ensures validity |
| **Str2Int** | `BitVec.toNat` | `def bitstring_to_nat {n : ℕ} : BitVec n → ℕ := BitVec.toNat` |
| **Int2Str** | `BitVec.ofNat` | `def nat_to_bitstring (n : ℕ) {w : ℕ} : BitVec w := BitVec.ofNat w n` |

## Verification Properties

All functions in this specification satisfy the following general properties:

1. **Type Safety**: Input and output types are strictly enforced
2. **Bounds Checking**: Array access is bounds-safe through dependent types
3. **Overflow Behavior**: Clearly specified for fixed-width operations
4. **Precondition Satisfaction**: All operations check necessary preconditions
5. **Postcondition Guarantees**: All operations guarantee specified postconditions

## Notes on Lean 4 BitVec Integration

Lean 4's `BitVec` type provides excellent support for finite bit vectors with:

- **Compile-time width checking**: `BitVec n` ensures bit width `n` at type level
- **Overflow behavior**: Well-defined semantics for arithmetic operations
- **Efficient operations**: Native support for bitwise and arithmetic operations
- **Proof automation**: Integration with Lean's proof automation for verification
- **Decidable equality**: Built-in support for decidable operations

This makes it ideal for formally verifying NumPy-like operations on finite integer types.