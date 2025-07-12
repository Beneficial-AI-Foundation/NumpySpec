#!/bin/bash
# Run the parallel spec builder

# Default values
OUTPUT_DIR="agent_outputs_$(date +%Y%m%d_%H%M%S)"
WORKERS=5
START_DIR=""
LIMIT=""
DRY_RUN=""

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --start-dir)
            START_DIR="$2"
            shift 2
            ;;
        --workers)
            WORKERS="$2"
            shift 2
            ;;
        --limit)
            LIMIT="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN="--dry-run"
            shift
            ;;
        --help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  --start-dir DIR     Start from a specific directory (e.g., 'polynomial/chebyshev')"
            echo "  --workers N         Number of parallel workers (default: 5)"
            echo "  --limit N           Process only N files"
            echo "  --output-dir DIR    Directory for outputs (default: timestamped)"
            echo "  --dry-run           Show what would be processed without running"
            echo "  --help              Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Build command
CMD="python3 spec_pipeline/build_specs_parallel.py --output-dir \"$OUTPUT_DIR\" --workers $WORKERS"

if [ ! -z "$START_DIR" ]; then
    CMD="$CMD --start-dir \"$START_DIR\""
fi

if [ ! -z "$LIMIT" ]; then
    CMD="$CMD --limit $LIMIT"
fi

if [ ! -z "$DRY_RUN" ]; then
    CMD="$CMD $DRY_RUN"
fi

echo "Running parallel spec builder..."
echo "Output directory: $OUTPUT_DIR"
echo "Workers: $WORKERS"
echo ""

# Execute the command
eval $CMD

