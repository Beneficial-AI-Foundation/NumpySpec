#!/bin/bash

# Test script for verifying numpy constants Lean implementations and specifications
# This script runs the verification process on the constants data to ensure 
# Lean code and specifications are properly aligned.

set -e  # Exit on any error

# Script location and paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
CONSTANTS_DIR="$PROJECT_ROOT/data/constants"
STRUCTURE_VERIFIER="$SCRIPT_DIR/verify_constants_structure.py"
FULL_VERIFIER="$SCRIPT_DIR/run_constants_verifier_local.py"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_status() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

print_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check if conda environment is activated
check_environment() {
    print_status "Checking environment..."
    
    # Set up elan/lean path
    if [[ -d "/home/hantao/.elan/bin" ]]; then
        export PATH="/home/hantao/.elan/bin:$PATH"
        print_success "Added elan/lean to PATH"
    fi
    
    if [[ -z "$CONDA_DEFAULT_ENV" ]]; then
        print_warning "No conda environment detected. Attempting to activate 'spec' environment..."
        
        # Try to activate conda environment
        if command -v conda >/dev/null 2>&1; then
            eval "$(conda shell.bash hook)"
            conda activate spec 2>/dev/null || {
                print_error "Failed to activate conda environment 'spec'"
                print_error "Please run: conda activate spec"
                exit 1
            }
        else
            print_error "Conda not found. Please ensure conda is installed and 'spec' environment exists."
            exit 1
        fi
    else
        print_success "Conda environment '$CONDA_DEFAULT_ENV' is active"
    fi
    
    # # Check if lean is available
    # if command -v lean >/dev/null 2>&1; then
    #     local lean_version=$(lean --version | head -1)
    #     print_success "Lean found: $lean_version"
    # else
    #     print_warning "Lean not found in PATH. Some verification modes may not work."
    # fi
}

# Check if required files exist
check_files() {
    print_status "Checking required files..."
    
    if [[ ! -f "$STRUCTURE_VERIFIER" ]]; then
        print_error "Structure verifier script not found: $STRUCTURE_VERIFIER"
        exit 1
    fi
    
    if [[ ! -f "$FULL_VERIFIER" ]]; then
        print_error "Full verifier script not found: $FULL_VERIFIER"
        exit 1
    fi
    
    if [[ ! -d "$CONSTANTS_DIR" ]]; then
        print_error "Constants directory not found: $CONSTANTS_DIR"
        exit 1
    fi
    
    if [[ ! -f "$CONSTANTS_DIR/data.json" ]]; then
        print_error "Constants data file not found: $CONSTANTS_DIR/data.json"
        exit 1
    fi
    
    print_success "All required files found"
}

# List available constants
list_constants() {
    print_status "Available constants to verify:"
    
    # Extract constant names from JSON
    python3 -c "
import json
with open('$CONSTANTS_DIR/data.json') as f:
    data = json.load(f)
for i, (name, info) in enumerate(data.items(), 1):
    print(f'  {i}. {name}')
    print(f'     Files: {info[\"python\"]}, {info[\"lean\"]}, {info[\"spec\"]}')
"
    echo
}

# Run the verification
run_verification() {
    local mode="$1"
    local verbose_flag="$2"
    
    print_status "Starting verification of numpy constants..."
    print_status "Mode: $mode"
    echo "=" * 70
    
    # Change to project root to ensure proper imports
    cd "$PROJECT_ROOT"
    
    # Choose verifier based on mode
    local verifier_script=""
    local extra_args=""
    
    case "$mode" in
        "structure")
            verifier_script="$STRUCTURE_VERIFIER"
            print_status "Running structure verification (file existence and basic syntax)..."
            ;;
        "syntax")
            verifier_script="$FULL_VERIFIER"
            extra_args="--syntax-only"
            print_status "Running Lean syntax verification (requires Lean installation)..."
            ;;
        "full")
            verifier_script="$FULL_VERIFIER"
            extra_args="--full-build"
            print_status "Running full Lean compilation (requires Lean + mathlib)..."
            ;;
        *)
            print_error "Unknown verification mode: $mode"
            return 1
            ;;
    esac
    
    # Run the verification
    if python3 "$verifier_script" "$CONSTANTS_DIR" --json-file data.json $verbose_flag $extra_args; then
        echo
        print_success "Verification completed successfully!"
        return 0
    else
        echo
        print_error "Verification failed! Some constants have issues."
        return 1
    fi
}

# Show usage information
show_usage() {
    echo "Usage: $0 [OPTIONS]"
    echo
    echo "Test numpy constants Lean implementations and specifications alignment."
    echo
    echo "Options:"
    echo "  -m, --mode MODE      Verification mode: structure, syntax, or full (default: structure)"
    echo "  -v, --verbose        Show detailed build logs for all constants"
    echo "  -l, --list          List available constants without running verification"
    echo "  -h, --help          Show this help message"
    echo
    echo "Verification Modes:"
    echo "  structure           Check file structure and basic syntax (fast, no Lean required)"
    echo "  syntax              Check Lean syntax (requires Lean installation)"
    echo "  full                Full Lean compilation (requires Lean + mathlib setup)"
    echo
    echo "Examples:"
    echo "  $0                          # Run structure verification"
    echo "  $0 --mode syntax            # Run Lean syntax verification"
    echo "  $0 --mode full --verbose    # Run full verification with detailed logs"
    echo "  $0 --list                   # List available constants"
    echo
}

# Main execution
main() {
    echo "🔍 Numpy Constants Lean Verification Test"
    echo "========================================"
    
    # Default options
    local mode="structure"
    local verbose=""
    
    # Parse command line arguments
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_usage
                exit 0
                ;;
            -l|--list)
                check_files
                list_constants
                exit 0
                ;;
            -v|--verbose)
                verbose="--verbose"
                shift
                ;;
            -m|--mode)
                mode="$2"
                if [[ ! "$mode" =~ ^(structure|syntax|full)$ ]]; then
                    print_error "Invalid mode: $mode. Use structure, syntax, or full."
                    show_usage
                    exit 1
                fi
                shift 2
                ;;
            *)
                print_error "Unknown option: $1"
                show_usage
                exit 1
                ;;
        esac
    done
    
    # Run the verification process
    check_environment
    check_files
    list_constants
    
    if run_verification "$mode" "$verbose"; then
        print_success "All tests passed! 🎉"
        
        # Show next steps based on mode
        case "$mode" in
            "structure")
                echo
                print_status "Next steps:"
                echo "  • For Lean syntax verification: $0 --mode syntax"
                echo "  • For full compilation: $0 --mode full"
                ;;
            "syntax")
                echo
                print_status "Next steps:"
                echo "  • For full compilation with mathlib: $0 --mode full"
                ;;
        esac
        
        exit 0
    else
        print_error "Some tests failed! ❌"
        echo
        print_status "Troubleshooting:"
        case "$mode" in
            "structure")
                echo "  • Check that all referenced files exist"
                echo "  • Verify Python syntax with: python3 -m py_compile <file>"
                echo "  • Check Lean file structure manually"
                ;;
            "syntax")
                echo "  • Ensure Lean 4 is installed: lean --version"
                echo "  • Check individual files: lean --check <file>"
                echo "  • Verify network connectivity for Lean dependencies"
                ;;
            "full")
                echo "  • Ensure mathlib is properly installed"
                echo "  • Check lake build works in a test project"
                echo "  • Verify all imports are correct"
                ;;
        esac
        echo
        print_status "For detailed error logs, run with --verbose"
        exit 1
    fi
}

# Run main function with all arguments
main "$@"
