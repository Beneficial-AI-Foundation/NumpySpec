# GaussianSpec Claude Guidelines

## Canonical Typeclasses for Mathematical Properties

### Associativity and Commutativity

When working with mathematical operations that require proofs of associativity or commutativity, **always use the following canonical typeclasses from Lean's standard library**:

#### **Std.Associative** - The canonical typeclass for associativity proofs

```lean
-- Use this for operations that satisfy: (a * b) * c = a * (b * c)
instance [Std.Associative op] : Std.Associative op where
  assoc := -- proof that op is associative
```

**Usage Guidelines:**
- Use `Std.Associative` for any binary operation that needs to be proven associative
- This is the standard way to denote associativity proofs in GaussianSpec
- Prefer this over custom associativity definitions or ad-hoc proofs

#### **Std.Commutative** - The canonical typeclass for commutativity proofs

```lean
-- Use this for operations that satisfy: a * b = b * a
instance [Std.Commutative op] : Std.Commutative op where
  comm := -- proof that op is commutative
```

**Usage Guidelines:**
- Use `Std.Commutative` for any binary operation that needs to be proven commutative
- This is the standard way to denote commutativity proofs in GaussianSpec
- Prefer this over custom commutativity definitions or ad-hoc proofs

### Matrix Operations Context

In the context of GaussianSpec's matrix operations and Gaussian elimination:

1. **Matrix Multiplication**: When proving properties about matrix multiplication, use `Std.Associative` for associativity proofs
2. **Scalar Operations**: For commutative scalar operations on matrix elements, use `Std.Commutative`
3. **Composition Laws**: When proving that certain matrix transformations are associative, leverage `Std.Associative`

### Best Practices

1. **Consistency**: Always use these canonical typeclasses rather than defining custom ones
2. **Interoperability**: Using standard typeclasses ensures compatibility with mathlib and other Lean libraries
3. **Documentation**: When implementing instances, document which mathematical property is being established
4. **Proof Reuse**: Leverage existing instances where possible rather than duplicating proofs

### Examples

```lean
-- Good: Using canonical typeclass
instance : Std.Associative Matrix.mul where
  assoc := matrix_mul_assoc

-- Good: Using canonical typeclass  
instance : Std.Commutative Nat.add where
  comm := Nat.add_comm

-- Avoid: Custom definitions when standard ones exist
-- def MyAssoc (op : α → α → α) : Prop := ∀ a b c, op (op a b) c = op a (op b c)
```

## Development Workflow

When implementing mathematical operations in GaussianSpec:

1. **Identify Required Properties**: Determine if the operation needs associativity, commutativity, or both
2. **Use Canonical Typeclasses**: Implement instances of `Std.Associative` and/or `Std.Commutative` as needed
3. **Leverage Standard Library**: Check if instances already exist in mathlib before implementing custom ones
4. **Document Proofs**: Clearly document which mathematical theorems support your typeclass instances

This approach ensures consistency, maintainability, and interoperability across the GaussianSpec codebase.