# Numeric-Only Synthesis Tasks (Batch 5)

This batch focuses exclusively on numeric types (Int, Nat, Float) without any string manipulation.

## Summary

- **Total Tasks**: 20 numeric-only synthesis tasks
- **Types Used**: Int, Nat, Float (no strings, chars, or text)
- **PR**: Batch 5 (to be created)

## Tasks Included

### Arithmetic Operations
1. **SynthesisTask77** - Check if divisible by 11
2. **SynthesisTask406** - Check if integer is odd
3. **SynthesisTask58** - Check if two integers have opposite signs
4. **SynthesisTask435** - Get last digit of integer (n % 10)
5. **SynthesisTask89** - Find closest smaller integer (n-1)
6. **SynthesisTask227** - Find minimum of three integers
7. **SynthesisTask432** - Calculate median of two lengths

### Geometric Calculations
8. **SynthesisTask17** - Calculate square perimeter (4 * side)
9. **SynthesisTask85** - Calculate sphere surface area (4πr²)
10. **SynthesisTask82** - Calculate sphere volume (4/3πr³)
11. **SynthesisTask14** - Calculate triangular prism volume
12. **SynthesisTask574** - Calculate cylinder surface area (2πr(r+h))

### Number Sequences
13. **SynthesisTask135** - Calculate nth hexagonal number
14. **SynthesisTask59** - Calculate nth octagonal number
15. **SynthesisTask268** - Calculate star number (6n(n-1)+1)
16. **SynthesisTask279** - Calculate nth decagonal number (4n²-3n)

### Unit Conversions
17. **SynthesisTask606** - Convert degrees to radians
18. **SynthesisTask264** - Calculate dog years (7 * human years)

### Prime Checking
19. **SynthesisTask3** - Check if number is non-prime (composite)

## Implementation Notes

- All functions use `sorry` as placeholders
- Float constants used for π (3.14159265358979323846)
- Consistent use of Lean 4 numeric types:
  - `Int` for signed integers
  - `Nat` for natural numbers
  - `Float` for floating-point calculations