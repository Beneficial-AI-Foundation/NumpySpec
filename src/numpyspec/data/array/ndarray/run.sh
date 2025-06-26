#!/bin/bash
# run.sh - A wrapper script to use instead of just while just is not available
# Usage: ./run.sh [command]

set -e

case "$1" in
    "" | "build")
        echo "Building..."
        lake build
        ;;
    "test")
        echo "=== Running All Tests ==="
        echo ""
        echo "--- LeanArrayLib Tests ---"
        ./.lake/build/bin/testexe
        echo ""
        echo "--- NDArray Tests ---"
        ./.lake/build/bin/ndtest
        ;;
    "test-lean")
        echo "=== Running LeanArrayLib Tests ==="
        ./.lake/build/bin/testexe
        ;;
    "test-nd")
        echo "=== Running NDArray Tests ==="
        ./.lake/build/bin/ndtest
        ;;
    "clean")
        lake clean
        ;;
    "test-direct")
        echo "=== Running tests directly with Lean ==="
        echo ""
        echo "--- LeanArrayLib Tests ---"
        lake env lean Test.lean
        echo ""
        echo "--- NDArray Tests ---"
        lake env lean NDArrayTest.lean
        ;;
    "help")
        echo "Available commands:"
        echo "  ./run.sh build       - Build all executables (default)"
        echo "  ./run.sh test        - Run all tests"
        echo "  ./run.sh test-lean   - Run only LeanArrayLib tests"
        echo "  ./run.sh test-nd     - Run only NDArray tests"
        echo "  ./run.sh test-direct - Run tests directly without building executables"
        echo "  ./run.sh clean       - Clean build artifacts"
        echo "  ./run.sh help        - Show this help message"
        ;;
    *)
        echo "Unknown command: $1"
        echo "Run './run.sh help' for available commands"
        exit 1
        ;;
esac