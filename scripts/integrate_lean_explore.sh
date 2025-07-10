#!/bin/bash
# Script to integrate NumpySpec with lean-explore database

set -e

NUMPYSPEC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_EXPLORE_DIR="$NUMPYSPEC_DIR/../lean-explore"

echo "=== Integrating NumpySpec with lean-explore ==="
echo "NumpySpec directory: $NUMPYSPEC_DIR"
echo "lean-explore directory: $LEAN_EXPLORE_DIR"

# Step 1: Build the extractor with NumpySpec dependency
echo -e "\n[1/5] Building lean-explore extractor with NumpySpec..."
cd "$LEAN_EXPLORE_DIR/extractor"
lake build

# Step 2: Run the declaration extractor
echo -e "\n[2/5] Extracting declarations from NumpySpec..."
lake exe extractDeclarations > "$LEAN_EXPLORE_DIR/data/declarations.jsonl"

# Step 3: Run the AST extractor
echo -e "\n[3/5] Extracting AST information..."
lake exe extractAST > "$LEAN_EXPLORE_DIR/data/ast_data.json"

# Step 4: Populate the database
echo -e "\n[4/5] Populating database with NumpySpec declarations..."
cd "$LEAN_EXPLORE_DIR"
python scripts/populate_db.py \
    --declarations-file data/declarations.jsonl \
    --dependencies-file data/dependencies.jsonl \
    --database-url sqlite:///data/lean_explore_data.db

# Step 5: Generate embeddings and build search index
echo -e "\n[5/5] Generating embeddings and building search index..."
python scripts/generate_embeddings.py
python scripts/build_faiss_index.py

echo -e "\n=== Integration complete! ==="
echo "You can now search NumpySpec functions using lean-explore."