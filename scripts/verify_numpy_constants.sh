#!/bin/bash
# Verify numpy constants Lean specifications

set -e  # Exit on error

# Get the directory where this script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Path to the constants directory
CONSTANTS_DIR="${PROJECT_ROOT}/data/constants"
JSON_FILE="data.json"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${YELLOW}NumPy Constants Lean Specification Verifier${NC}"
echo "============================================="
echo

# Check if constants directory exists
if [ ! -d "$CONSTANTS_DIR" ]; then
    echo -e "${RED}Error: Constants directory not found: $CONSTANTS_DIR${NC}"
    exit 1
fi

# Check if data.json exists
if [ ! -f "$CONSTANTS_DIR/$JSON_FILE" ]; then
    echo -e "${RED}Error: JSON file not found: $CONSTANTS_DIR/$JSON_FILE${NC}"
    exit 1
fi

# Activate Python virtual environment if it exists
if [ -f "$PROJECT_ROOT/.venv/bin/activate" ]; then
    echo "Activating Python virtual environment..."
    source "$PROJECT_ROOT/.venv/bin/activate"
elif [ -f "$PROJECT_ROOT/venv/bin/activate" ]; then
    echo "Activating Python virtual environment..."
    source "$PROJECT_ROOT/venv/bin/activate"
fi

# Run the verifier
echo "Running verifier on: $CONSTANTS_DIR"
echo "Using JSON file: $JSON_FILE"
echo

# Check if we should run in verbose mode
VERBOSE_FLAG=""
if [ "$1" == "--verbose" ] || [ "$1" == "-v" ]; then
    VERBOSE_FLAG="--verbose"
fi

# Execute the Python script
python3 "$SCRIPT_DIR/run_verifier.py" "$CONSTANTS_DIR" --json-file "$JSON_FILE" $VERBOSE_FLAG

# Capture exit code
EXIT_CODE=$?

# Display result
echo
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}✅ All specifications verified successfully!${NC}"
else
    echo -e "${RED}❌ Some specifications failed verification.${NC}"
    echo -e "Run with ${YELLOW}--verbose${NC} flag for detailed output."
fi

exit $EXIT_CODE 