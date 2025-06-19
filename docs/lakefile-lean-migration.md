# Lakefile.lean Migration Notes

## Overview

We've migrated from `lakefile.toml` to `lakefile.lean` for type safety and better control over build configuration. The new setup provides a workspace-like structure similar to Cargo workspaces.

## Key Features

### 1. Type-Checked Configuration
Unlike TOML, lakefile.lean provides compile-time type checking:
```lean
leanOptions := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`autoImplicit, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.missingDocs, true⟩
]
```

### 2. Unified Multi-Library Setup
- **Main library**: `GaussianSpec` with standard source structure
- **Generated library**: `Generated` with custom `srcDir`
- Both managed from a single lakefile

### 3. Glob-Based Module Inclusion
```lean
globs := #[.andSubmodules `GaussianSpec]  -- Include module and all submodules
globs := #[.submodules `Spec]              -- Include only submodules
```

### 4. Custom Build Targets
- `allLibs`: Builds all libraries in parallel
- `generated`: Builds only the generated code
- Can be extended with more targets as needed

### 5. Dependency Management
Dependencies are declared in order (important for avoiding recompilation):
1. `verso` - Documentation generation
2. `Hammer` - Theorem proving automation (before mathlib!)
3. `mathlib` - Mathematical library

## Usage

```bash
# Build default target (main executable)
lake build

# Build all libraries
lake build allLibs

# Build only generated code
lake build generated

# Build specific library
lake build GaussianSpec
```

## Benefits Over TOML

1. **Type Safety**: Errors caught at compile time, not runtime
2. **Programmatic Control**: Can use Lean's full programming capabilities
3. **Better IDE Support**: Full autocomplete and type checking
4. **Extensibility**: Easy to add complex build logic
5. **Single Source of Truth**: All build configuration in one typed file

## Future Extensions

The lakefile.lean structure allows for:
- Conditional compilation based on environment
- Dynamic dependency resolution
- Custom build scripts and code generation
- Integration with external build systems