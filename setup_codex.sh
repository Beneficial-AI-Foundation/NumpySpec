#!/usr/bin/env bash
# Setup script for GaussianSpec to work with Codex
# This script installs all necessary dependencies and configures the environment

set -euo pipefail

echo "🚀 Setting up GaussianSpec for Codex..."

# 1. Check for Python 3.12+
if ! command -v python3 >/dev/null; then
    echo "❌ Python 3 not found. Please install Python 3.12 or later."
    exit 1
fi

PYTHON_VERSION=$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')
if [[ $(echo "$PYTHON_VERSION < 3.12" | bc) -eq 1 ]]; then
    echo "❌ Python $PYTHON_VERSION found, but 3.12+ is required."
    exit 1
fi
echo "✅ Python $PYTHON_VERSION detected"

# 2. Install uv if not present
if ! command -v uv >/dev/null; then
    echo "📦 Installing uv (Python package manager)..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$PATH"
fi
echo "✅ uv is installed"

# 3. Install Lean toolchain (elan) if not present
if ! command -v elan >/dev/null; then
    echo "📦 Installing elan (Lean toolchain manager)..."
    curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
        bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
    export PATH="$HOME/.elan/bin:$PATH"
fi
echo "✅ elan is installed"

# 4. Install project dependencies
echo "📦 Installing Python dependencies..."
uv sync

# 5. Build Lean dependencies
echo "🔨 Building Lean project..."
lake build

# 6. Create .env file if it doesn't exist
if [ ! -f .env ]; then
    echo "📝 Creating .env file..."
    cat > .env << 'EOF'
# Environment variables for GaussianSpec
# Add your API keys and configuration here

# MorphCloud API key (optional, for remote compilation)
# MORPH_API_KEY=your_api_key_here

# HuggingFace token (optional, for model access)
# HF_TOKEN=your_token_here

# LiteLLM configuration (optional)
# LITELLM_API_KEY=your_key_here
EOF
    echo "⚠️  Please edit .env and add any necessary API keys"
fi

# 7. Verify installation
echo ""
echo "🔍 Verifying installation..."
echo "Python: $(python3 --version)"
echo "uv: $(uv --version)"
echo "lake: $(lake --version)"
echo "lean: $(lean --version)"

# 8. Run a quick test
echo ""
echo "🧪 Running quick test..."
if uv run -m pytest -q --tb=short tests/test_basic.py 2>/dev/null; then
    echo "✅ Basic tests passed"
else
    echo "⚠️  Some tests failed - this may be expected if API keys are not configured"
fi

echo ""
echo "✨ Setup complete! GaussianSpec is ready for use with Codex."
echo ""
echo "Next steps:"
echo "1. Edit .env file with any necessary API keys"
echo "2. Run 'just test' to verify full test suite"
echo "3. Run 'just train' to train the RL agent"
echo ""
echo "For more information, see README.md and CLAUDE.md"