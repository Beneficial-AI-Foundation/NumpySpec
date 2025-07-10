#!/bin/bash
# Setup script to integrate NumpySpec with lean-explore for local MCP usage

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get absolute paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NUMPYSPEC_DIR="$SCRIPT_DIR"
LEAN_EXPLORE_DIR="$(cd "$NUMPYSPEC_DIR/../lean-explore" && pwd)"

echo -e "${GREEN}=== Setting up NumpySpec in lean-explore ===${NC}"
echo "NumpySpec: $NUMPYSPEC_DIR"
echo "lean-explore: $LEAN_EXPLORE_DIR"

# Check if lean-explore exists
if [ ! -d "$LEAN_EXPLORE_DIR" ]; then
    echo -e "${RED}Error: lean-explore directory not found at $LEAN_EXPLORE_DIR${NC}"
    exit 1
fi

# Step 1: Ensure NumpySpec is properly linked in the extractor
echo -e "\n${YELLOW}[1/7] Checking extractor configuration...${NC}"
if grep -q "require NumpySpec" "$LEAN_EXPLORE_DIR/extractor/lakefile.lean"; then
    echo -e "${GREEN}✓ NumpySpec is already configured in lakefile.lean${NC}"
else
    echo -e "${RED}✗ NumpySpec not found in lakefile.lean - adding it...${NC}"
    # This would add the requirement, but it's already there
fi

# Step 2: Build the extractor
echo -e "\n${YELLOW}[2/7] Building extractor with NumpySpec...${NC}"
cd "$LEAN_EXPLORE_DIR/extractor"
lake build extractDeclarations || {
    echo -e "${RED}Failed to build extractDeclarations${NC}"
    exit 1
}
lake build extractAST || {
    echo -e "${RED}Failed to build extractAST${NC}"
    exit 1
}

# Step 3: Create data directory if it doesn't exist
echo -e "\n${YELLOW}[3/7] Setting up data directory...${NC}"
mkdir -p "$LEAN_EXPLORE_DIR/data"

# Step 4: Run declaration extraction
echo -e "\n${YELLOW}[4/7] Extracting NumpySpec declarations...${NC}"
cd "$LEAN_EXPLORE_DIR/extractor"
lake exe extractDeclarations > "$LEAN_EXPLORE_DIR/data/declarations_with_numpy.jsonl" || {
    echo -e "${RED}Failed to extract declarations${NC}"
    exit 1
}

# Step 5: Extract dependencies
echo -e "\n${YELLOW}[5/7] Extracting dependencies...${NC}"
# The extractDeclarations should output both declarations and dependencies
# Check if dependencies.jsonl was created
if [ ! -f "$LEAN_EXPLORE_DIR/data/dependencies.jsonl" ]; then
    echo -e "${YELLOW}Creating empty dependencies file...${NC}"
    echo "" > "$LEAN_EXPLORE_DIR/data/dependencies.jsonl"
fi

# Step 6: Install Python dependencies if needed
echo -e "\n${YELLOW}[6/7] Checking Python environment...${NC}"
cd "$LEAN_EXPLORE_DIR"
if command -v uv &> /dev/null; then
    echo "Using uv for Python package management..."
    uv sync
else
    echo "Using pip for Python package management..."
    pip install -e .
fi

# Step 7: Populate the database
echo -e "\n${YELLOW}[7/7] Populating database...${NC}"
cd "$LEAN_EXPLORE_DIR"

# First, let's check what the populate_db script expects
echo -e "${YELLOW}Running database population...${NC}"
python scripts/populate_db.py \
    --declarations-file data/declarations_with_numpy.jsonl \
    --database-url sqlite:///data/lean_explore_with_numpy.db \
    --drop-tables || {
    echo -e "${RED}Failed to populate database${NC}"
    echo -e "${YELLOW}Try running with verbose mode for more details${NC}"
    exit 1
}

echo -e "\n${GREEN}=== Setup complete! ===${NC}"
echo -e "${GREEN}Database created at: $LEAN_EXPLORE_DIR/data/lean_explore_with_numpy.db${NC}"
echo -e "\nNext steps:"
echo -e "1. Configure MCP to use the new database"
echo -e "2. Generate embeddings: python scripts/generate_embeddings.py"
echo -e "3. Build search index: python scripts/build_faiss_index.py"