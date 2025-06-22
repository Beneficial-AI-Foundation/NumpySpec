# Standard Array Operations

This library implements element-wise arithmetic operations on arrays in Lean 4 with formal specifications.

## Operations Implemented

### Basic Arithmetic Operations

1. **Element-wise Addition** (`Array.add`)
   - Adds corresponding elements of two arrays
   - Requires arrays to have the same size
   - Example: `#[1, 2, 3].add #[4, 5, 6] = #[5, 7, 9]`

2. **Element-wise Subtraction** (`Array.sub`)
   - Subtracts corresponding elements of two arrays
   - Requires arrays to have the same size
   - Example: `#[10, 20, 30].sub #[1, 2, 3] = #[9, 18, 27]`

3. **Element-wise Multiplication** (`Array.mul`)
   - Multiplies corresponding elements of two arrays
   - Requires arrays to have the same size
   - Example: `#[2, 3, 4].mul #[10, 20, 30] = #[20, 60, 120]`

4. **Element-wise Division and Modulo** (`Array.divMod`)
   - Returns a pair of arrays: (quotients, remainders)
   - Requires arrays to have the same size
   - Example: `#[20, 35].divMod #[3, 5] = (#[6, 7], #[2, 0])`

### Array Creation

5. **Zeros Array** (`Array.zeros`)
   - Creates an array filled with zero values
   - Takes the desired size as parameter
   - Example: `Array.zeros 5 = #[0, 0, 0, 0, 0]`

### Additional Operations

6. **Scalar Multiplication** (`Array.scalarMul`)
   - Multiplies each element by a scalar value
   - Example: `#[1, 2, 3].scalarMul 10 = #[10, 20, 30]`

7. **Element-wise Negation** (`Array.neg`)
   - Negates each element in the array
   - Example: `#[1, -2, 3].neg = #[-1, 2, -3]`

## Specifications

Each operation comes with formal specifications proving:
- **Size preservation**: Operations preserve the size of arrays
- **Correctness**: Each element in the result is computed correctly

For example:
```lean
theorem Array.add_size [Add α] (xs ys : Array α) (h : xs.size = ys.size) :
    (xs.add ys).size = xs.size

theorem Array.add_get [Add α] (xs ys : Array α) (h : xs.size = ys.size) (i : Fin xs.size) :
    (xs.add ys)[i] = xs[i] + ys[i]
```

## Building and Running

1. Make sure you have Lean 4 installed
2. Navigate to the project directory
3. Build the project:
   ```bash
   lake build
   ```
4. Run the tests:
   ```bash
   lake env lean --run Main.lean
   ```

## Example Usage

```lean
import StdArrayOperation

def example_usage : IO Unit := do
  let a := #[1, 2, 3, 4]
  let b := #[5, 6, 7, 8]
  
  -- Element-wise operations
  let sum := a.add b           -- #[6, 8, 10, 12]
  let diff := b.sub a          -- #[4, 4, 4, 4]
  let prod := a.mul b          -- #[5, 12, 21, 32]
  
  -- Create array of zeros
  let zeros := Array.zeros 10  -- #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  
  -- Scalar multiplication
  let scaled := a.scalarMul 3  -- #[3, 6, 9, 12]
  
  IO.println s!"Results: sum={sum}, diff={diff}, prod={prod}"
```

## Type Requirements

The operations work with any type that supports the required mathematical operations:
- `Add α` for addition
- `Sub α` for subtraction
- `Mul α` for multiplication
- `Div α` and `Mod α` for division and modulo
- `Zero α` for creating zero arrays
- `Neg α` for negation

This means the operations work with `Nat`, `Int`, `Float`, and any custom types that implement these type classes.

## Error Handling

Operations that require arrays to have the same size will panic if the sizes don't match. The error message includes the actual sizes for debugging:
```
Array.add: size mismatch 3 ≠ 2
```