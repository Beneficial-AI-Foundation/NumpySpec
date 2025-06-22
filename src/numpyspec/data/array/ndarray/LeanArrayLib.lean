-- This module serves as the root of the `LeanArrayLib` library.
-- Import modules here that should be built as part of the library.
import LeanArrayLib.Basic

/-!
# LeanArrayLib - A Type-Safe Multi-Dimensional Array Library for Lean 4

This library provides a foundation for working with multi-dimensional arrays in Lean 4,
with a focus on type safety and compile-time bounds checking.

## Key Features

- **Type-safe indexing**: Array bounds are checked at compile time using dependent types
- **Multi-dimensional support**: Easily work with 1D, 2D, and higher-dimensional arrays
- **Flexible layouts**: Currently supports row-major layout with extensibility for others
- **Memory efficiency**: Thin wrapper around Lean's ByteArray for performance
- **Extensible element types**: Currently supports UInt8, easily extended to other types

## Architecture

The library is organized into several modules:

- `Memory`: Low-level buffer management and element encoding/decoding
- `Layout`: Multi-dimensional array layout computation (strides, shapes)
- `Index`: Type class for converting multi-dimensional indices to linear positions
- `LeanArray`: High-level array type combining all components

## Usage Example

```lean
-- Create a 1D array
let arr1d := LeanArray.fromList [1, 2, 3, 4, 5]
let elem := arr1d[2]  -- Access element at index 2

-- Create a 2D array (2×3 matrix)
let arr2d : LeanArray UInt8 (Fin 2 × Fin 3) 6 := ...
let elem := arr2d[(1, 2)]  -- Access element at row 1, column 2
```

## Future Extensions

- Support for more element types (Int32, Float, etc.)
- Additional layout options (column-major, custom strides)
- Array operations (map, fold, slice, reshape)
- SIMD optimizations for numerical computations
-/
