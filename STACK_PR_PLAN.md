# Stack PR Plan for NumPy Documentation Extraction

## Current State
- Branch: `dev-hantao-autonumpy`
- Main commit: `517477f` - Extract comprehensive NumPy documentation with source code
- This is a massive commit with 9600+ additions and 3400+ deletions

## Proposed Stack Structure

### PR 1: Clean up DafnySpecs and old files
```bash
# Create branch for cleanup
git checkout -b cleanup-dafnyspecs 885bf10
git cherry-pick 92acf4f  # Delete unnecessary files
# Cherry-pick only the DafnySpecs deletion from 517477f
```

### PR 2: Core array operations
- Array creation operations
- Array manipulation operations
- Indexing and slicing operations
```bash
git checkout -b numpy-core-arrays cleanup-dafnyspecs
# Add only array_creation/, array_manipulation/, indexing_slicing/
```

### PR 3: Mathematical and statistical functions
- Mathematical functions
- Statistics operations
- Logic functions
```bash
git checkout -b numpy-math-stats numpy-core-arrays
# Add mathematical_functions/, statistics/, logic_functions/
```

### PR 4: Specialized numerical operations
- Linear algebra operations
- FFT operations
- Polynomial operations
- Random number generation
```bash
git checkout -b numpy-specialized numpy-math-stats
# Add linear_algebra/, fft/, polynomial/, random/
```

### PR 5: Utility and support operations
- String operations
- Datetime support
- Data type routines
- I/O operations
- Sorting and searching
- Bitwise operations
- Set operations
```bash
git checkout -b numpy-utilities numpy-specialized
# Add remaining directories
```

### PR 6: Infrastructure and typing
- Masked arrays
- Testing utilities
- Typing support
- Constants
- Universal functions (ufuncs)
- Update EXTRACTION_STATUS.md
```bash
git checkout -b numpy-infrastructure numpy-utilities
# Add ma/, testing/, typing/, constants/, ufuncs/
```

## Manual Steps Without stack-pr

1. First, create a backup branch:
```bash
git checkout -b backup-dev-hantao-autonumpy
git checkout dev-hantao-autonumpy
```

2. Reset to before the big commit:
```bash
git reset --hard 885bf10
```

3. Create separate commits for each logical group:
```bash
# Cleanup commit
git checkout 517477f -- DafnySpecs/
git rm -r DafnySpecs/
git commit -m "chore: remove obsolete DafnySpecs directory"

# Core arrays
git checkout 517477f -- web_utils/full_numpy/array_creation/
git checkout 517477f -- web_utils/full_numpy/array_manipulation/
git checkout 517477f -- web_utils/full_numpy/indexing_slicing/
git add web_utils/full_numpy/array_creation/
git add web_utils/full_numpy/array_manipulation/
git add web_utils/full_numpy/indexing_slicing/
git commit -m "feat: add core NumPy array operations documentation"

# Continue for other groups...
```

## Alternative: Use gh CLI directly

Once authenticated with `gh auth login`:

```bash
# Install stack-pr dependencies
gh auth login
export PATH="/Users/louhantao/.local/bin:$PATH"

# Then use stack-pr
stack-pr submit
```

## Benefits of Splitting

1. **Easier Review**: Each PR is focused on a specific domain
2. **Clearer History**: Logical progression of additions
3. **Parallel Review**: Different reviewers can handle different PRs
4. **Faster Merge**: Smaller PRs can be merged incrementally
5. **Better Testing**: Can test each component separately