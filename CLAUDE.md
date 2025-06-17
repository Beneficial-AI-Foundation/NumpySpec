# Claude Development Guidelines for GaussianSpec

This document provides tool references and development guidelines for Claude when working on the GaussianSpec project.

## Project Overview

GaussianSpec is a cloud-native Lean 4 research playground for formally specifying Gaussian elimination. The project uses:
- **Lean 4** for formal verification
- **MorphCloud/Pantograph** for remote compilation
- **Python pipeline** for OCR and automation
- **Automated theorem proving tools** for proof assistance

## Available Tools

### LeanHammer

LeanHammer is an automated theorem proving (ATP) tool for Lean 4 that helps automate proof search, particularly useful for the linear algebra proofs in this project.

#### Installation

LeanHammer is already configured as a dependency in `lakefile.toml`:

```toml
[[require]]
name = "LeanHammer"
git = "https://github.com/JOSHCLUNE/LeanHammer"
rev = "main"
```

To install external ATP tools (optional but recommended for full functionality):

```bash
# Ubuntu/Debian
sudo apt-get install eprover vampire

# macOS  
brew install eprover vampire

# Using conda/mamba
conda install -c conda-forge eprover vampire
```

#### Usage Examples

##### Basic Usage

```lean
import LeanHammer

-- Use in simple proofs
example (h : P → Q) (hp : P) : Q := by
  hammer
```

##### Matrix Theory Applications

For GaussianSpec's linear algebra context:

```lean
import LeanHammer
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Det

-- Automated proof of matrix properties
theorem matrix_mul_assoc (A B C : Matrix n n ℝ) : 
  (A * B) * C = A * (B * C) := by
  hammer

-- Use in Gaussian elimination context
theorem det_nonzero_implies_invertible (A : Matrix n n ℝ) 
  (h : Matrix.det A ≠ 0) : IsUnit A := by
  hammer
```

##### Integration with Gaussian Elimination Proofs

```lean
-- Main theorem with hammer assistance
theorem gaussianElimination_is_left_inverse (A : Matrix n n ℝ) 
  (hA : IsUnit (Matrix.det A)) : 
  gaussianElimination A * A = 1 := by
  -- Use hammer for preliminary steps
  have h1 : Matrix.det A ≠ 0 := by
    hammer
  -- Continue with domain-specific reasoning
  sorry -- Main proof body
```

##### Premise Selection

```lean
-- Let hammer choose relevant lemmas automatically
example (A B : Matrix n n ℝ) (h : A * B = 1) : 
  Matrix.det A * Matrix.det B = 1 := by
  hammer [Matrix.det_mul] -- Provide specific hint if needed
```

#### Configuration Options

```lean
-- Set timeout (default usually 30 seconds)
set_option hammer.timeout 60

-- Enable/disable specific ATP tools
set_option hammer.vampire true
set_option hammer.eprover true
set_option hammer.z3 false

-- Adjust verbosity
set_option hammer.verbose true
```

#### Best Practices

1. **Start Simple**: Use hammer on straightforward goals before complex ones
2. **Provide Hints**: Include relevant lemmas when hammer struggles
3. **Combine Strategies**: Use hammer with other tactics like `simp`, `ring`, etc.
4. **Timeout Management**: Set reasonable timeouts to avoid long waits
5. **Proof Readability**: Consider simplifying hammer-generated proofs for clarity

#### Troubleshooting

**Common Issues:**

1. **Timeout**: Increase timeout or break down the goal
```lean
set_option hammer.timeout 120
```

2. **Missing ATP Tools**: Install external provers or disable them
```lean
set_option hammer.eprover false  -- if E prover not installed
```

3. **Complex Goals**: Provide more context or break into smaller steps
```lean
-- Instead of hammer on complex goal
example : complex_goal := by
  have h1 : intermediate_step := by hammer
  have h2 : another_step := by hammer  
  -- combine h1, h2 manually
```

#### Integration with GaussianSpec Workflow

For the automated agent pipeline:

```python
# In src/gaussianspec/agent.py - potential integration
def try_hammer_tactic(goal_state):
    """Try using hammer for automated proof search."""
    lean_code = f"""
theorem auto_goal : {goal_state} := by
  hammer
"""
    return lean_code
```

### Other Automation Tools

#### Built-in Lean 4 Tactics

Complement LeanHammer with these built-in automation tools:

- **`omega`**: Linear arithmetic over integers
- **`norm_num`**: Numerical computation  
- **`simp`**: Simplification with lemma databases
- **`ring`**: Ring arithmetic normalization
- **`field_simp`**: Field arithmetic simplification
- **`polyrith`**: Polynomial arithmetic

#### Usage in Matrix Context

```lean
-- Combine different automation approaches
example (A : Matrix n n ℝ) (h : Matrix.det A = 5) : 
  Matrix.det A ≠ 0 := by
  norm_num [h]  -- Use norm_num for numerical reasoning

example (a b : ℝ) : a + b = b + a := by
  ring  -- Use ring for algebraic manipulation
```

## Development Workflow

### Proof Development Strategy

1. **Start with Hammer**: Try automated proof search first
2. **Manual Decomposition**: Break complex goals into smaller parts  
3. **Hybrid Approach**: Combine automation with manual reasoning
4. **Verification**: Use cloud pipeline for fast iteration

### Testing Automation

```lean
-- Create test cases for automation effectiveness
example : 1 + 1 = 2 := by hammer  -- Should work instantly
example : ∀ n : ℕ, n + 0 = n := by hammer  -- Should find proof
```

## Cloud Integration

The project uses MorphCloud for remote compilation. Hammer tools work seamlessly with the cloud pipeline:

```bash
# Test hammer functionality remotely
just pipeline --remote --lean-file GaussianSpec.lean --edit "example : P → P := by hammer"
```

## Contributing Guidelines

When adding new automation tools or enhancing hammer usage:

1. **Document Configuration**: Add any new options to this file
2. **Provide Examples**: Include practical usage examples
3. **Test Integration**: Verify compatibility with cloud pipeline
4. **Update Dependencies**: Keep lakefile.toml current

## Performance Considerations

- **Timeout Settings**: Balance thorough search vs. development speed
- **Selective Usage**: Don't use hammer on trivial goals that simpler tactics handle
- **Resource Monitoring**: Be mindful of ATP tool resource usage in cloud environment

## References

- [LeanHammer Repository](https://github.com/JOSHCLUNE/LeanHammer)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [MorphCloud Documentation](https://pypi.org/project/morphcloud/)