#!/usr/bin/env bash
# NumpySpec runner script for Codex environments

set -euo pipefail

# Activate Python environment
if [ -d .venv ]; then
    source .venv/bin/activate
fi

# Ensure PATH includes Lean tools
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"
export PYTHONPATH="${PYTHONPATH:-}:src"

case "${1:-help}" in
    build)
        echo "🔨 Building Lean project..."
        lake build
        ;;
    test)
        echo "🧪 Running tests..."
        uv run -m pytest -v
        ;;
    train)
        echo "🏋️ Training RL agent..."
        uv run -m numpyspec.rl_trainer
        ;;
    server)
        echo "🖥️ Starting Lean server..."
        uv run -m numpyspec.lean_server
        ;;
    edit)
        echo "✏️ Starting edit subagent..."
        uv run -m numpyspec.subagents edit "${@:2}"
        ;;
    clean)
        echo "🧹 Cleaning build artifacts..."
        lake clean
        rm -rf .cache logs/*.log
        ;;
    info)
        echo "📊 System information:"
        echo "Python: $(python --version 2>&1)"
        echo "Lean: $(lean --version 2>&1)"
        echo "Lake: $(lake --version 2>&1)"
        echo "UV: $(uv --version 2>&1)"
        ;;
    *)
        echo "NumpySpec - Formally verified numpy operations"
        echo ""
        echo "Usage: ./run.sh [command] [args...]"
        echo ""
        echo "Commands:"
        echo "  build   - Build the Lean project"
        echo "  test    - Run all tests"
        echo "  train   - Train the RL agent"
        echo "  server  - Start Lean server interface"
        echo "  edit    - Run edit subagent"
        echo "  clean   - Clean build artifacts"
        echo "  info    - Show system information"
        echo "  help    - Show this help"
        ;;
esac