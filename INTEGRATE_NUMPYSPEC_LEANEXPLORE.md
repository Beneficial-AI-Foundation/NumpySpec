# Integrating NumpySpec with lean-explore

This guide explains how to build NumpySpec into the lean-explore database so you can search and cite NumpySpec functions using the lean-explore MCP tool.

## Prerequisites

1. lean-explore cloned at `../lean-explore` (relative to NumpySpec)
2. Lean 4 toolchain installed
3. Python with `uv` or `pip` installed

## Integration Steps

### 1. Automatic Setup

Run the provided setup script:

```bash
chmod +x setup-numpyspec-in-leanexplore.sh
./setup-numpyspec-in-leanexplore.sh
```

This script will:
1. Verify lean-explore configuration (NumpySpec is already added as a dependency)
2. Build the extractor tools with NumpySpec included
3. Extract declarations from NumpySpec
4. Populate the database with NumpySpec declarations
5. Set up the Python environment

### 2. Configure MCP to Use the New Database

After running the setup script, configure your MCP settings to use the new database:

1. Update the lean-explore config.yml to use the new database:
   ```yaml
   database:
     url: "sqlite:///data/lean_explore_with_numpy.db"
   ```

2. Or set the environment variable:
   ```bash
   export LEAN_EXPLORE_DB_URL="sqlite:///path/to/lean-explore/data/lean_explore_with_numpy.db"
   ```

### 3. Generate Search Index (Optional but Recommended)

For better search performance, generate embeddings and build the FAISS index:

```bash
cd ../lean-explore
python scripts/generate_embeddings.py --database-url sqlite:///data/lean_explore_with_numpy.db
python scripts/build_faiss_index.py --database-url sqlite:///data/lean_explore_with_numpy.db
```

## Using lean-explore MCP with NumpySpec

Once configured, you can use the lean-explore MCP tools to search NumpySpec functions:

### Available MCP Tools:

1. **`mcp__leanexploreRemote__search`** - Search for declarations by query
   ```
   Example: Search for "numpy add" or "matrix multiplication"
   ```

2. **`mcp__leanexploreRemote__get_by_id`** - Get specific declarations by ID

3. **`mcp__leanexploreRemote__get_dependencies`** - Get dependencies of a declaration

### Example Usage in Code:

When implementing a new NumPy function, first search if it exists:

```python
# Search for existing numpy absolute value implementation
results = mcp__leanexploreRemote__search(
    query="numpy absolute value abs",
    package_filters=["NumpySpec"]
)
```

## Troubleshooting

### Build Errors

If the extractor build fails:
1. Ensure NumpySpec builds successfully: `lake build`
2. Check that the relative path in lakefile.lean is correct: `../../NumpySpec`

### Database Population Errors

If database population fails:
1. Check that declarations_with_numpy.jsonl was created
2. Try running with verbose mode: `python scripts/populate_db.py --verbose`

### Search Not Finding NumpySpec Functions

1. Verify the database contains NumpySpec entries:
   ```bash
   sqlite3 ../lean-explore/data/lean_explore_with_numpy.db \
     "SELECT COUNT(*) FROM declarations WHERE module LIKE 'NumpySpec%';"
   ```

2. Regenerate the search index if needed

## Manual Steps (if automatic setup fails)

1. **Build the extractor:**
   ```bash
   cd ../lean-explore/extractor
   lake build
   ```

2. **Extract declarations:**
   ```bash
   lake exe extractDeclarations > ../data/declarations_with_numpy.jsonl
   ```

3. **Populate database:**
   ```bash
   cd ../lean-explore
   python scripts/populate_db.py \
     --declarations-file data/declarations_with_numpy.jsonl \
     --database-url sqlite:///data/lean_explore_with_numpy.db \
     --drop-tables
   ```

## Benefits

With NumpySpec integrated into lean-explore:
- Avoid reimplementing existing functions
- Find related implementations quickly
- Understand dependencies between functions
- Maintain consistency across the codebase