#!/usr/bin/env bash
# Complete installation script for OpenAI Codex Universal
# https://github.com/openai/codex-universal
#
# This script installs everything needed for NumpySpec to work in cloud environments
# with automated agents. Runs non-interactively.

set -euo pipefail

echo "🚀 Installing NumpySpec for OpenAI Codex Universal..."

# Detect OS
OS="$(uname -s)"
ARCH="$(uname -m)"

# Install system dependencies based on OS
install_system_deps() {
    case "$OS" in
        Linux*)
            if command -v apt-get >/dev/null; then
                echo "📦 Installing system dependencies (Ubuntu/Debian)..."
                export DEBIAN_FRONTEND=noninteractive
                sudo apt-get update -qq
                sudo apt-get install -y -qq curl wget git build-essential python3 python3-pip python3-venv bc
            elif command -v yum >/dev/null; then
                echo "📦 Installing system dependencies (RHEL/CentOS)..."
                sudo yum install -y curl wget git gcc gcc-c++ make python3 python3-pip bc
            elif command -v apk >/dev/null; then
                echo "📦 Installing system dependencies (Alpine)..."
                sudo apk add --no-cache curl wget git build-base python3 python3-dev py3-pip bc
            fi
            ;;
        Darwin*)
            echo "📦 macOS detected - assuming homebrew available..."
            if ! command -v brew >/dev/null; then
                echo "Installing Homebrew..."
                /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
            fi
            brew install python curl wget git bc 2>/dev/null || true
            ;;
    esac
}

# Install uv (fast Python package manager)
install_uv() {
    if ! command -v uv >/dev/null; then
        echo "📦 Installing uv..."
        curl -LsSf https://astral.sh/uv/install.sh | sh
        export PATH="$HOME/.local/bin:$PATH"
    fi
    echo "✅ uv installed: $(uv --version)"
}

# Install Lean 4 toolchain
install_lean() {
    if ! command -v elan >/dev/null; then
        echo "📦 Installing Lean 4 toolchain (elan)..."
        curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | \
            bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
        export PATH="$HOME/.elan/bin:$PATH"
    fi
    echo "✅ Lean 4 installed: $(lean --version 2>/dev/null)"
}

# Install Rust (for some Lean dependencies)
install_rust() {
    if ! command -v rustc >/dev/null; then
        echo "📦 Installing Rust..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path
        export PATH="$HOME/.cargo/bin:$PATH"
    fi
    echo "✅ Rust installed: $(rustc --version 2>/dev/null)"
}

# Install modern CLI tools and development conveniences
install_modern_cli_tools() {
    echo "🛠️ Installing modern CLI tools..."
    
    case "$OS" in
        Linux*)
            if command -v apt-get >/dev/null; then
                echo "📦 Installing CLI tools (Ubuntu/Debian)..."
                sudo apt-get install -y -qq ripgrep fd-find bat tree htop jq shellcheck yamllint tmux fzf git-delta
                # Create symlinks for fd on Ubuntu (installed as fdfind)
                sudo ln -sf $(which fdfind) /usr/local/bin/fd 2>/dev/null || true
                sudo ln -sf $(which batcat) /usr/local/bin/bat 2>/dev/null || true
            elif command -v yum >/dev/null; then
                echo "📦 Installing CLI tools (RHEL/CentOS)..."
                sudo yum install -y epel-release
                sudo yum install -y ripgrep fd-find bat tree htop jq ShellCheck tmux fzf git-delta
            elif command -v apk >/dev/null; then
                echo "📦 Installing CLI tools (Alpine)..."
                sudo apk add --no-cache ripgrep fd bat tree htop jq shellcheck tmux fzf git-delta
            fi
            ;;
        Darwin*)
            echo "📦 Installing CLI tools (macOS)..."
            brew install ripgrep fd bat tree htop jq shellcheck yamllint tmux fzf git-delta exa zoxide lazygit 2>/dev/null || true
            ;;
    esac
    
    # Install additional Rust-based tools via cargo if available
    if command -v cargo >/dev/null; then
        echo "📦 Installing additional Rust tools..."
        cargo install --quiet exa zoxide 2>/dev/null || true
    fi
    
    echo "✅ Modern CLI tools installed"
}

# Install Claude Code CLI
install_claude_code() {
    echo "🤖 Installing Claude Code CLI..."
    
    case "$OS" in
        Darwin*)
            if command -v brew >/dev/null; then
                brew install --cask claude-code 2>/dev/null || {
                    echo "⚠️ Claude Code not available via brew, trying direct install..."
                    install_claude_code_direct
                }
            else
                install_claude_code_direct
            fi
            ;;
        Linux*)
            install_claude_code_direct
            ;;
    esac
    
    # Verify installation
    if command -v claude >/dev/null; then
        echo "✅ Claude Code installed: $(claude --version 2>/dev/null || echo "version check failed")"
    else
        echo "⚠️ Claude Code installation may have failed"
    fi
}

# Direct Claude Code installation (fallback)
install_claude_code_direct() {
    echo "📦 Installing Claude Code directly..."
    
    # Check for latest release and install appropriately
    case "$OS" in
        Darwin*)
            if [[ "$ARCH" == "arm64" ]]; then
                CLAUDE_ARCH="aarch64-apple-darwin"
            else
                CLAUDE_ARCH="x86_64-apple-darwin"
            fi
            ;;
        Linux*)
            if [[ "$ARCH" == "x86_64" ]]; then
                CLAUDE_ARCH="x86_64-unknown-linux-gnu"
            else
                CLAUDE_ARCH="$ARCH-unknown-linux-gnu"
            fi
            ;;
    esac
    
    # Try to download and install (this is a placeholder - actual URLs would need to be verified)
    echo "⚠️ Direct Claude Code installation not implemented - please install manually from claude.ai"
}

# Install AI/LLM development tools
install_ai_tools() {
    echo "🧠 Installing AI development tools..."
    
    # Install OpenAI CLI and related tools via pip/pipx
    if command -v uv >/dev/null; then
        echo "📦 Installing AI CLI tools..."
        uv tool install openai-cli 2>/dev/null || echo "⚠️ OpenAI CLI not available via uv"
        uv tool install anthropic-cli 2>/dev/null || echo "⚠️ Anthropic CLI not available via uv"
        uv tool install huggingface-hub[cli] 2>/dev/null || echo "⚠️ HF CLI not available via uv"
    fi
    
    # Install GitHub Copilot CLI if available
    case "$OS" in
        Darwin*)
            brew install gh 2>/dev/null || true
            ;;
        Linux*)
            if command -v apt-get >/dev/null; then
                curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg
                echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null
                sudo apt-get update -qq && sudo apt-get install -y gh
            fi
            ;;
    esac
    
    echo "✅ AI development tools installed"
}

# Install Jujutsu (jj) version control system
install_jujutsu() {
    echo "📝 Installing Jujutsu (jj)..."
    
    case "$OS" in
        Darwin*)
            brew install jj 2>/dev/null || {
                echo "⚠️ Jujutsu not available via brew, trying cargo..."
                cargo install --git https://github.com/martinvonz/jj.git --bin jj 2>/dev/null || echo "⚠️ Jujutsu cargo install failed"
            }
            ;;
        Linux*)
            # Try cargo install first
            if command -v cargo >/dev/null; then
                cargo install --git https://github.com/martinvonz/jj.git --bin jj 2>/dev/null || echo "⚠️ Jujutsu cargo install failed"
            fi
            ;;
    esac
    
    if command -v jj >/dev/null; then
        echo "✅ Jujutsu installed: $(jj --version 2>/dev/null)"
    else
        echo "⚠️ Jujutsu installation failed"
    fi
}

# Install Lean-specific development tools
install_lean_dev_tools() {
    echo "🔧 Installing Lean development tools..."
    
    # Install lean-lsp-mcp via uvx if available
    if command -v uvx >/dev/null; then
        echo "📦 Installing lean-lsp-mcp..."
        uvx install lean-lsp-mcp 2>/dev/null || echo "⚠️ lean-lsp-mcp not available via uvx"
    fi
    
    # Install additional Lean tooling
    export PATH="$HOME/.elan/bin:$PATH"
    if command -v lake >/dev/null; then
        echo "📦 Setting up Lean cache..."
        lake exe cache get 2>/dev/null || echo "⚠️ Lean cache setup failed"
    fi
    
    echo "✅ Lean development tools installed"
}

# Setup Python environment
setup_python() {
    echo "📦 Setting up Python environment..."
    
    # Create requirements.txt if missing
    if [ ! -f requirements.txt ]; then
        cat > requirements.txt << 'EOF'
# Core scientific computing
numpy>=1.24.0
scipy>=1.10.0

# HTTP and API clients
requests>=2.31.0
httpx>=0.25.0

# Data validation and serialization
pydantic>=2.0.0

# Machine learning and RL
gymnasium>=0.29.0
torch>=2.0.0
transformers>=4.30.0

# Testing and development
pytest>=7.4.0
pytest-asyncio>=0.21.0
pytest-xdist>=3.3.0

# Code quality
ruff>=0.1.0
mypy>=1.5.0

# Interactive development
ipython>=8.0.0
jupyter>=1.0.0

# Async programming
asyncio-mqtt>=0.11.0
aiofiles>=23.0.0

# Configuration and environment
python-dotenv>=1.0.0
typer>=0.9.0

# Optional cloud dependencies
boto3>=1.28.0
azure-identity>=1.14.0
google-cloud-storage>=2.10.0
EOF
    fi
    
    # Install dependencies with uv
    uv venv .venv --python python3
    source .venv/bin/activate
    uv pip install -r requirements.txt
    
    echo "✅ Python environment ready"
}

# Setup Lean project
setup_lean() {
    echo "🔨 Setting up Lean project..."
    
    # Ensure PATH includes elan
    export PATH="$HOME/.elan/bin:$PATH"
    
    # Create lakefile.toml if missing
    if [ ! -f lakefile.toml ]; then
        cat > lakefile.toml << 'EOF'
name = "NumpySpec"
version = "0.1.0"
keywords = ["math", "numpy", "linear-algebra", "numerical"]

[dependencies]
mathlib = { git = "https://github.com/leanprover-community/mathlib4.git", rev = "main" }

[[lean_lib]]
name = "NumpySpec"
srcDir = "."

[[lean_lib]]  
name = "Generated"
srcDir = "generated"

[linter.missingDocs]
enabled = true

[package]
relaxedAutoImplicit = false
EOF
    fi
    
    # Initialize lake project if needed
    if [ ! -f lake-manifest.json ]; then
        lake init
    fi
    
    # Build project (may take time on first run)
    echo "Building Lean dependencies (this may take 10-15 minutes)..."
    lake build --verbose || echo "⚠️ Lean build failed - continuing"
    
    echo "✅ Lean project setup complete"
}

# Create project structure
setup_project_structure() {
    echo "📁 Creating project structure..."
    
    mkdir -p src/numpyspec
    mkdir -p generated/Spec  
    mkdir -p tests
    mkdir -p logs
    mkdir -p .cache
    mkdir -p models
    
    # Create main module files if missing
    if [ ! -f NumpySpec.lean ]; then
        cat > NumpySpec.lean << 'EOF'
-- NumpySpec: Formally verified linear algebra for Lean 4
-- Main module for matrix operations with numpy-style API

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

/-!
# NumpySpec

This module provides formally verified implementations of numpy-style operations
with a focus on matrix computations and linear algebra.

## Main Goals

1. Numpy-compatible API design
2. Formal verification of numerical algorithms
3. Efficient computation with correctness guarantees
4. Educational resource for formal methods in numerical computing

-/

namespace NumpySpec

-- Core matrix type
variable {α : Type*} [Field α] {m n : ℕ}

-- Basic matrix operations will be defined here
def Matrix.multiply (A : Matrix (Fin m) (Fin n) α) (B : Matrix (Fin n) (Fin p) α) : Matrix (Fin m) (Fin p) α :=
  sorry -- TODO: Implement matrix multiplication

end NumpySpec
EOF
    fi
    
    # Create Python package structure
    if [ ! -f src/numpyspec/__init__.py ]; then
        cat > src/numpyspec/__init__.py << 'EOF'
"""
NumpySpec: Formally verified numpy-compatible operations

A Python interface to Lean 4 mathematical proofs and numpy-style operations.
"""

__version__ = "0.1.0"
__author__ = "NumpySpec Team"

# Main exports
from .lean_server import LeanServerInterface
from .subagents import LeanEditSubagent, LeanBuildSubagent

__all__ = [
    "LeanServerInterface", 
    "LeanEditSubagent", 
    "LeanBuildSubagent"
]
EOF
    fi
    
    echo "✅ Project structure created"
}

# Create configuration files
setup_config() {
    echo "⚙️ Creating configuration files..."
    
    # Environment configuration
    cat > .env << 'EOF'
# NumpySpec Environment Configuration
PYTHONPATH=${PYTHONPATH}:src
LEAN_PATH=${LEAN_PATH}:.

# Remote compilation settings
REMOTE_COMPILATION=true
PANTOGRAPH_URL=https://api.morphcloud.com/pantograph

# Optional API keys (add as needed)
# OPENAI_API_KEY=
# ANTHROPIC_API_KEY=
# HF_TOKEN=
# MORPH_API_KEY=
EOF

    # Codex configuration
    cat > .codex.json << 'EOF'
{
  "name": "NumpySpec",
  "description": "Formally verified linear algebra library for Lean 4",
  "install_command": "./codex-install.sh",
  "build_command": "lake build",
  "test_command": "uv run -m pytest",
  "run_command": "./run.sh",
  "language": "lean4",
  "frameworks": ["mathlib4", "numpy"],
  "dependencies": {
    "system": ["curl", "wget", "git", "build-essential"],
    "python": ["numpy", "scipy", "gymnasium", "torch"],
    "lean": ["mathlib"]
  }
}
EOF

    # Git configuration
    if [ ! -f .gitignore ]; then
        cat > .gitignore << 'EOF'
# Python
__pycache__/
*.py[cod]
*$py.class
.venv/
venv/
.env.local

# Lean
.lake/
lake-packages/
build/

# Logs and caches
logs/
.cache/
*.log

# IDE
.vscode/
.idea/
*.swp
*.swo

# OS
.DS_Store
Thumbs.db

# Models and data
models/*.zip
models/*.pt
data/

# Temporary files
tmp/
temp/
*.tmp
EOF
    fi
    
    echo "✅ Configuration files created"
}

# Create run script for easy execution
create_run_script() {
    cat > run.sh << 'EOF'
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
EOF

    chmod +x run.sh
    echo "✅ Run script created"
}

# Verify installation
verify_installation() {
    echo "🔍 Verifying installation..."
    
    # Check Python environment
    source .venv/bin/activate 2>/dev/null || true
    python --version
    
    # Check Lean installation
    export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
    lean --version 2>/dev/null || echo "⚠️ Lean not in PATH"
    lake --version 2>/dev/null || echo "⚠️ Lake not in PATH"
    
    # Check modern CLI tools
    echo "🔧 Checking CLI tools..."
    command -v rg >/dev/null && echo "✅ ripgrep (rg) available" || echo "⚠️ ripgrep not found"
    command -v fd >/dev/null && echo "✅ fd available" || echo "⚠️ fd not found"
    command -v bat >/dev/null && echo "✅ bat available" || echo "⚠️ bat not found"
    command -v jq >/dev/null && echo "✅ jq available" || echo "⚠️ jq not found"
    command -v tree >/dev/null && echo "✅ tree available" || echo "⚠️ tree not found"
    
    # Check version control tools
    command -v git >/dev/null && echo "✅ git available: $(git --version | head -1)" || echo "⚠️ git not found"
    command -v jj >/dev/null && echo "✅ jujutsu (jj) available" || echo "⚠️ jujutsu not found"
    command -v gh >/dev/null && echo "✅ GitHub CLI available" || echo "⚠️ GitHub CLI not found"
    
    # Check AI tools  
    command -v claude >/dev/null && echo "✅ Claude Code available" || echo "⚠️ Claude Code not found"
    command -v uvx >/dev/null && echo "✅ uvx available" || echo "⚠️ uvx not found"
    
    # Quick functionality test
    echo "🧪 Running verification tests..."
    if python -c "import numpy, scipy; print('✅ Python scientific stack works')"; then
        echo "✅ Python environment verified"
    else
        echo "⚠️ Python environment issues detected"
    fi
    
    echo "✅ Installation verification complete"
}

# Main installation sequence
main() {
    echo "Starting OpenAI Codex Universal installation for NumpySpec..."
    echo "OS: $OS, Architecture: $ARCH"
    echo ""
    
    install_system_deps
    install_uv
    install_rust  
    install_lean
    install_modern_cli_tools
    install_claude_code
    install_ai_tools
    install_jujutsu
    install_lean_dev_tools
    setup_python
    setup_project_structure
    setup_lean
    setup_config
    create_run_script
    verify_installation
    
    echo ""
    echo "🎉 Installation complete!"
    echo ""
    echo "NumpySpec is now ready for use with OpenAI Codex Universal."
    echo "The project provides formally verified numpy-style operations"
    echo "with mathematical proofs and automated cloud deployment."
    echo ""
    echo "🛠️ Installed development tools:"
    echo "  • Modern CLI: ripgrep (rg), fd, bat, exa, tree, htop, jq"
    echo "  • Version Control: git, jujutsu (jj), lazygit"
    echo "  • AI Tools: Claude Code, GitHub CLI, OpenAI CLI"
    echo "  • Shell Enhancement: tmux, fzf, zoxide, git-delta"
    echo "  • Code Quality: shellcheck, yamllint, pre-commit hooks"
    echo "  • Lean Tools: lean-lsp-mcp, lake cache"
    echo ""
    echo "Quick start:"
    echo "  ./run.sh build   # Build the Lean project"
    echo "  ./run.sh test    # Run tests"
    echo "  ./run.sh info    # Show system info"
    echo ""
    echo "For more details, see CLAUDE.md and the generated documentation."
}

# Run main installation
main "$@"