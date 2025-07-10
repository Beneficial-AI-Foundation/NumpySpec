#!/bin/bash
# Wrapper script to run the spec builder with common options

# Default values
OUTPUT_FILE="spec_pipeline/spec_build_results_$(date +%Y%m%d_%H%M%S).json"
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
        --limit)
            LIMIT="$2"
            shift 2
            ;;
        --dry-run)
            DRY_RUN="--dry-run"
            shift
            ;;
        --output)
            OUTPUT_FILE="$2"
            shift 2
            ;;
        --help)
            echo "Usage: $0 [OPTIONS]"
            echo "Options:"
            echo "  --start-dir DIR   Start from a specific directory (e.g., 'polynomial/chebyshev')"
            echo "  --limit N         Process only N files"
            echo "  --dry-run         Show what would be processed without running"
            echo "  --output FILE     Specify output JSON file (default: timestamped)"
            echo "  --help            Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Build command
CMD="python3 build_specs.py --output $OUTPUT_FILE"

if [ ! -z "$START_DIR" ]; then
    CMD="$CMD --start-dir \"$START_DIR\""
fi

if [ ! -z "$LIMIT" ]; then
    CMD="$CMD --limit $LIMIT"
fi

if [ ! -z "$DRY_RUN" ]; then
    CMD="$CMD $DRY_RUN"
fi

echo "Running spec builder..."
echo "Command: $CMD"
echo "Output will be saved to: $OUTPUT_FILE"
echo ""

# Execute the command
eval $CMD

# claude -p "Build the spec of 'NumpySpec/polynomial/chebyshev/chebvander3d.lean' using the doc and the source code provided in itself. Go to NumpySpec/PIPELINE.md for detailed instructions. Make sure to read the whole file and follow the instructions, especially the important notices for agents: 1. **Ensure Compilability**: Make sure the file is compilable after adding the specs. Always verify compilation with lake build or use the Lean LSP MCP tools to check for errors. 2. **One Function Per File**: Make only one target function (def) and one spec (theorem) per file, the function name of the def function should be the same as the name of the target function. This keeps specifications modular and manageable. 3. **Use Vector Instead of Array**: Make sure to use Vector instead of Array in all specifications. This is crucial for the type-safe approach we're taking. 4. **Write to File**: Make sure you actually write the generated specification into the file using the Write tool. Don't just generate the specification without saving it. 5. **Try to Write Sufficiently Detailed Specifications**: The specifications should be detailed enough to be used as a guide for the implementation. Normally, the spec should contain sanity checks and actual (mathematical) properties of the function. Remember, write only one function and one spec that is aligned with the sanity and mathematical properties of the function, and the specs should be more than trivial." \
# --mcp-config .mcp.json \
# --allowedTools mcp__lean-lsp-mcp__lean_build, mcp__lean-lsp-mcp__lean_file_contents, mcp__lean-lsp-mcp__lean_diagnostic_messages, mcp__lean-lsp-mcp__lean_goal, mcp__lean-lsp-mcp__lean_term_goal, mcp__lean-lsp-mcp__lean_hover_info, mcp__lean-lsp-mcp__lean_completions, mcp__lean-lsp-mcp__lean_declaration_file, mcp__lean-lsp-mcp__lean_multi_attempt, mcp__lean-lsp-mcp__lean_run_code, mcp__lean-lsp-mcp__lean_leansearch, mcp__lean-lsp-mcp__lean_loogle, mcp__lean-lsp-mcp__lean_state_search, mcp__lean-lsp-mcp__lean_hammer_premise, ListMcpResourcesTool, ReadMcpResourceTool, mcp__browsermcp__browser_navigate, mcp__browsermcp__browser_go_back, mcp__browsermcp__browser_go_forward, mcp__browsermcp__browser_snapshot, mcp__browsermcp__browser_click, mcp__browsermcp__browser_hover, mcp__browsermcp__browser_type, mcp__browsermcp__browser_select_option, mcp__browsermcp__browser_press_key, mcp__browsermcp__browser_wait, mcp__browsermcp__browser_get_console_logs, mcp__browsermcp__browser_screenshot \
# --verbose \
# --output-format stream-json \
# --allowedTools "Bash(mkdir:*)" "mcp__browsermcp__browser_navigate" "mcp__browsermcp__browser_click" "Bash(rm:*)" "WebFetch(domain:raw.githubusercontent.com)" "Bash(export:*)" "WebFetch(domain:numpy.org)" "mcp__browsermcp__browser_press_key" "mcp__browsermcp__browser_snapshot" "mcp__browsermcp__browser_type" "WebFetch(domain:github.com)" "Bash(curl:*)" "WebFetch(domain:github.com)" "Bash(python3:*)" "Bash(ls:*)""Bash(git add:*)""Bash(find:*)" "Bash(uv pip:*)""Bash(uv sync:*)""Bash(elan which:*)" "Bash(just setup:*)" "Bash(lake:*)" "Bash(uv run:*)" "Bash(rg:*)" "mcp__lean-lsp-mcp__lean_diagnostic_messages" "Bash(elan toolchain install:*)" "mcp__lean-lsp-mcp__lean_hover_info" "mcp__lean-lsp-mcp__lean_build" "mcp__lean-lsp-mcp__lean_goal" "Bash(od:*)" "Bash(grep:*)" "mcp__lean-lsp-mcp__lean_completions" "mcp__lean-lsp-mcp__lean_declaration_file" "mcp__lean-lsp-mcp__lean_multi_attempt" "mcp__lean-lsp-mcp__lean_leansearch" "Bash(mv:*)" "Bash(python:*)" "Bash(for:*)" "Bash(do echo \"Building $file...\")" "Bash(echo \"Failed: $file\")" "Bash(done)" "mcp__lean-lsp-mcp__lean_file_contents" "Bash(cat:*)" "Bash(jq:*)" "Bash(chmod:*)" "Bash(uv add:*)" "Bash(jq:*)" "Bash(claude:*)" "Bash(chmod:*)" "Bash(./update_all_numpy_code.sh)" "Bash(do echo -e \"\\n--- $file ---\")" "Bash(git commit:*)" "Bash(*)" "Read(*)" "Edit(./*)" "WebFetch(domain:numpy.org)" "WebFetch(domain:github.com)" "WebFetch(domain:raw.githubusercontent.com)" "Bash(source:*)" "WebFetch(domain:api.github.com)" "Bash(sed:*)" "Bash(git checkout:*)" "Bash(pipx install:*)" "Bash(uv tool install:*)" "Bash(stack-pr view:*)" "Bash(brew install:*)" "Bash(gh auth:*)" "Bash(gh pr list:*)" "Bash(pip install:*)" "Bash(gh pr view:*)" "Bash(git cherry-pick:*)" "Bash(git reset:*)" "Bash(stack-pr submit:*)" "Bash(gh pr create:*)" "Bash(git push:*)" "Bash(git pull:*)" "Bash(git branch:*)" "Bash(git rev-parse:*)" "Bash(do)" "Bash(echo:*)" "Bash(echo)" "Bash(git stash:*)" "Bash(git fetch:*)" "Bash(touch:*)" "Edit(**/*)" "Edit(NumpySpec/**/*)" "Write(NumpySpec/**/*)" "Bash" "Read" "Write" "Edit"