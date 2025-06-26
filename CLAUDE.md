# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working with this repository.

## Lean 4 Naming Conventions

- **`snake_case`**: Theorems, lemmas (`add_comm`, `lt_of_succ_le`)
- **`UpperCamelCase`**: Types, structures, classes (`Nat`, `LinearOrder`)
- **`lowerCamelCase`**: Functions, definitions (`toString`, `mapFilter`)
- **Variables**: `α β γ` (types), `x y z` (elements), `h` (hypotheses), `m n` (naturals), `f g` (functions)

## NumpySpec Project

**Goal**: Port numpy functionality to Lean 4 with formal verification.

**Core Components**:
- `NumpySpec.lean`, `NumpySpec/`: Core linear algebra definitions
- `BignumLean.lean`: Numerical types for safe arithmetic
- Focus: Matrix operations, Gaussian elimination, numpy-compatible API

## Development Commands

**IMPORTANT**: Use `just` instead of Makefile for all build tasks. Just is more convenient, safe and is a more modern replacement of makefile

**IMPORTANT**: Use notation type classes in Lean 4 when available. This could prevent replicated implimentation and simplify the code. Overall, diencourage unecessary implimentation.

```bash
# Build project
just build

# Run tests
just test

# Clean build artifacts
just clean

# Build and test
just all
```

## Numpy Port Roadmap

1. **Matrix Types**: Dense matrices (`Matrix m n α`), Sparse matrices (`SparseMatrix α`)
2. **Core Operations**: Matrix multiplication, transpose, LU decomposition, solve, determinant
3. **Verification Strategy**: Separate spec (proofs) from exec (efficient implementation)
4. **API Design**: Numpy-compatible with 0-based indexing, operator overloading

## Lean Development Guidelines

- Imports MUST come before any syntax elements
- Set `autoImplicit = false` in lakefile
- Use `uv` for Python (not pip), `just` for builds (not make)
- Use `rg`/`fd` instead of grep/find
- Prefer Vector > Array > List for data structures
- Use named holes (`?foo`) for incremental development

## Key Resources

- **Lean 4 Reference**: https://lean-lang.org/doc/reference/latest/
- **Mathlib Manual**: https://leanprover-community.github.io/mathlib-manual/html-multi/Guides/

## Design Principles

- **Correctness First**: Formal verification before optimization
- **Type Safety**: Use Lean's type system to prevent errors
- **Functional Style**: You are a functional programmer


## Common Lean Pitfalls

### Essential Issues to Avoid

- **Automatic implicit parameters**: Set `autoImplicit = false` to avoid typos becoming implicit parameters
- **Mathlib cache**: Run `lake exe cache get` to avoid hour-long builds
- **Use `let` not `have` for data**: `let x := value` preserves definitional equality
- **Prefer `a < b` over `b > a`**: Mathlib convention
- **Division by 0**: In Lean, `n / 0 = 0`
- **Natural subtraction**: `5 - 7 = 0` (truncates at 0)
- **Float**: Avoid for proofs, use `Rat` or `Real` instead