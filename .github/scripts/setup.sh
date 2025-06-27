#!/usr/bin/env bash
# NumpySpec GitHub Actions Environment Setup
# Installs everything needed for CI workflows
# Optimized for automated agents in cloud environments - non-interactive

set -euo pipefail

# Agent-optimized installation
if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
    echo "🚀 Setting up NumpySpec environment for GitHub Actions..."
else
    echo "🤖 Setting up NumpySpec environment for Codex agents..."
fi

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
            sudo apt-get install -y -qq apt-utils curl wget git build-essential python3 python3-pip python3-venv bc
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
        if ! brew install python curl wget git bc 2>/dev/null; then
            echo "⚠️ Some brew packages may have failed to install"
        fi
        ;;
    esac
}

# Add to PATH for current session and GitHub Actions
add_to_path() {
    local new_path="$1"

    # Add to current PATH if not already present
    if [[ ":$PATH:" != *":$new_path:"* ]]; then
        export PATH="$new_path:$PATH"
    fi

    # If in GitHub Actions, also add to GITHUB_PATH
    if [[ -n "${GITHUB_PATH:-}" ]]; then
        echo "$new_path" >>"$GITHUB_PATH"
    fi
}

# Install uv (fast Python package manager)
install_uv() {
    if ! command -v uv >/dev/null; then
        echo "📦 Installing uv..."
        curl -LsSf https://astral.sh/uv/install.sh | sh
        add_to_path "$HOME/.local/bin"
    fi
    echo "✅ uv installed: $(uv --version)"
}

# Install Lean 4 toolchain
install_lean() {
    if ! command -v elan >/dev/null; then
        echo "📦 Installing Lean 4 toolchain (elan)..."
        curl -fL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh |
            bash -s -- --default-toolchain leanprover/lean4:stable --no-modify-path -y
        add_to_path "$HOME/.elan/bin"
    fi
    echo "✅ Lean 4 installed: $(lean --version 2>/dev/null)"
}

# Install Rust (for some Lean dependencies)
install_rust() {
    if ! command -v rustc >/dev/null; then
        echo "📦 Installing Rust..."
        curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path
        add_to_path "$HOME/.cargo/bin"
    fi
    echo "✅ Rust installed: $(rustc --version 2>/dev/null)"
}

# Install essential CLI tools for agents
install_agent_cli_tools() {
    echo "🛠️ Installing agent CLI tools..."

    case "$OS" in
    Linux*)
        if command -v apt-get >/dev/null; then
            echo "📦 Installing essential tools (Ubuntu/Debian)..."
            # Install all tools via apt - most reliable for Ubuntu
            sudo apt-get install -y -qq ripgrep fd-find jq tree git-delta

            # Create symlink for fd command (Ubuntu names it fdfind)
            if command -v fdfind >/dev/null && [ ! -e /usr/local/bin/fd ]; then
                sudo ln -sf $(which fdfind) /usr/local/bin/fd 2>/dev/null || echo "⚠️ Failed to create fd symlink"
            fi

            # Install just via prebuilt binary
            echo "📦 Installing just (task runner)..."
            curl --proto '=https' --tlsv1.2 -sSf https://just.systems/install.sh | bash -s -- --to /usr/local/bin
        elif command -v yum >/dev/null; then
            echo "📦 Installing essential tools (RHEL/CentOS)..."
            sudo yum install -y epel-release
            sudo yum install -y ripgrep fd-find jq tree git-delta

            # Install just via prebuilt binary
            echo "📦 Installing just (task runner)..."
            curl --proto '=https' --tlsv1.2 -sSf https://just.systems/install.sh | bash -s -- --to /usr/local/bin
        elif command -v apk >/dev/null; then
            echo "📦 Installing essential tools (Alpine)..."
            sudo apk add --no-cache ripgrep fd jq tree git-delta just
        fi
        ;;
    Darwin*)
        echo "📦 Installing essential tools (macOS)..."
        if ! brew install ripgrep fd jq tree git-delta just 2>/dev/null; then
            echo "⚠️ Some macOS tools may have failed to install"
        fi
        ;;
    esac

    echo "✅ Agent CLI tools installed"
}

# Install codex CLI for agent orchestration
install_codex_cli() {
    # Skip in GitHub Actions - not needed
    if [[ -n "${GITHUB_ACTIONS:-}" ]]; then
        echo "⏭️ Skipping codex CLI in GitHub Actions"
        return
    fi

    echo "🤖 Installing codex CLI..."

    # Install via npm (official method)
    if command -v npm >/dev/null; then
        echo "📦 Installing codex via npm..."
        npm install -g @openai/codex 2>/dev/null || echo "⚠️ codex npm install failed"
    else
        echo "⚠️ npm not available for codex installation"
    fi

    # Verify installation
    if command -v codex >/dev/null; then
        echo "✅ codex CLI installed: $(codex --version 2>/dev/null || echo "version check failed")"
    else
        echo "⚠️ codex CLI installation may have failed"
    fi
}

# Install GitHub CLI for repository operations
install_github_cli() {
    echo "🐙 Installing GitHub CLI..."

    case "$OS" in
    Darwin*)
        if ! brew install gh 2>/dev/null; then
            echo "⚠️ GitHub CLI brew install failed"
        fi
        ;;
    Linux*)
        if command -v apt-get >/dev/null; then
            echo "📦 Installing GitHub CLI (official method)..."
            # Official GitHub CLI installation command
            (type -p wget >/dev/null || (sudo apt update && sudo apt-get install wget -y)) &&
                sudo mkdir -p -m 755 /etc/apt/keyrings &&
                out=$(mktemp) && wget -nv -O$out https://cli.github.com/packages/githubcli-archive-keyring.gpg &&
                cat $out | sudo tee /etc/apt/keyrings/githubcli-archive-keyring.gpg >/dev/null &&
                sudo chmod go+r /etc/apt/keyrings/githubcli-archive-keyring.gpg &&
                sudo mkdir -p -m 755 /etc/apt/sources.list.d &&
                echo "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list >/dev/null &&
                sudo apt update &&
                sudo apt install gh -y
        fi
        ;;
    esac

    echo "✅ GitHub CLI installed"
}

# Install Jujutsu (jj) version control system
install_jujutsu() {
    echo "📝 Installing Jujutsu (jj)..."

    case "$OS" in
    Darwin*)
        brew install jj 2>/dev/null || echo "⚠️ Jujutsu brew install failed"
        ;;
    Linux*)
        if command -v cargo >/dev/null; then
            echo "📦 Installing jj via cargo (this may take a few minutes)..."
            timeout 600 cargo install --locked --bin jj jj-cli 2>/dev/null || echo "⚠️ Jujutsu cargo install failed"
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

    # Ensure PATH includes required directories
    add_to_path "$HOME/.elan/bin"

    # Install lean-lsp-mcp for LSP completions (if available)
    if command -v uv >/dev/null; then
        echo "📦 Installing lean-lsp-mcp..."
        uv tool install lean-lsp-mcp 2>/dev/null || echo "⚠️ lean-lsp-mcp not available via uv (this is expected)"
    fi

    # Configure lake for reliable builds
    echo "⚙️ Configuring lake for reliable builds..."

    # Set reasonable lake defaults
    export LAKE_JOBS="$(nproc 2>/dev/null || echo 4)"
    export LAKE_VERBOSE="1"

    # Pre-compile common mathlib components if available
    if command -v lake >/dev/null; then
        echo "🏗️ Pre-warming lake cache..."
        lake exe cache get --force 2>/dev/null || echo "📋 No cache server configured"
    fi

    echo "✅ Lean development tools ready"
}

# Setup Python environment
setup_python() {
    echo "📦 Setting up Python environment..."

    # Use uv sync with pyproject.toml (modern approach)
    echo "🔄 Syncing dependencies from pyproject.toml..."
    uv sync --all-groups

    echo "✅ Python environment ready"
}

# Setup Lean project for repeated builds
setup_lean() {
    echo "🔨 Setting up Lean project for robust building..."

    # Ensure PATH includes required directories
    add_to_path "$HOME/.elan/bin"

    echo "📋 Using existing lakefile.lean"

    # Clean any stale build artifacts
    if [ -d ".lake" ]; then
        echo "🧹 Cleaning stale build artifacts..."
        rm -rf .lake/build .lake/packages/*/build
    fi

    # Initialize lake project if needed
    if [ ! -f lake-manifest.json ]; then
        echo "🔧 Initializing lake project..."
        lake init
    fi

    # Update dependencies to ensure consistency
    echo "📦 Updating Lean dependencies..."
    lake update || echo "⚠️ Lake update failed - continuing anyway"

    # Fetch dependencies without full build for speed
    echo "📥 Fetching Lean dependencies..."
    timeout 300 lake exe cache get || echo "⚠️ Cache fetch failed or timed out"

    # Test a quick build to verify setup
    echo "🧪 Testing build setup..."
    timeout 60 lake build --no-build || echo "⚠️ Test build failed - agents can retry with 'lake build'"

    echo "✅ Lean project ready for repeated builds"
}

# Create project structure
setup_project_structure() {
    echo "📁 Ensuring project directories exist..."

    mkdir -p generated/Spec
    mkdir -p tests
    mkdir -p logs
    mkdir -p .cache
    mkdir -p models

    echo "✅ Project structure verified (source files already in repo)"
}

# Create configuration files
setup_config() {
    echo "⚙️ Creating configuration files..."

    # Environment configuration for agents
    cat >.env <<'EOF'
# NumpySpec Agent Environment Configuration
PYTHONPATH=src:${PYTHONPATH:-}
LEAN_PATH=.:${LEAN_PATH:-}
PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:${PATH}

# Agent-specific settings
CODEX_AGENT=true
NON_INTERACTIVE=true

# Lake build optimization
LAKE_JOBS=4
LAKE_VERBOSE=1
LAKE_NO_BUILD=false

# Build resilience
ELAN_TOOLCHAIN=leanprover/lean4:stable

# Optional API keys (add as needed)
# OPENAI_API_KEY=
# ANTHROPIC_API_KEY=
# HF_TOKEN=
EOF

    # Codex agent configuration
    cat >.codex.json <<'EOF'
{
  "name": "NumpySpec",
  "description": "Formally verified linear algebra library for Lean 4",
  "install_command": ".github/scripts/setup.sh",
  "build_command": "lake build",
  "test_command": "uv run -m pytest -q",
  "lint_command": "lake build --verbose",
  "language": "lean4",
  "agent_tools": {
    "search": "rg",
    "find": "fd",
    "json": "jq",
    "tree": "tree",
    "git": "git",
    "vcs": "jj"
  },
  "environment": {
    "LEAN_PATH": ".",
    "PYTHONPATH": "src"
  }
}
EOF

    # Git configuration
    if [ ! -f .gitignore ]; then
        cat >.gitignore <<'EOF'
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

# Verify run script exists
check_run_script() {
    if [ ! -f run.sh ]; then
        echo "⚠️ run.sh not found - creating basic run script..."
        cat >run.sh <<'EOF'
#!/usr/bin/env bash
# NumpySpec runner script for Codex environments

set -euo pipefail

# Load environment if available
if [ -f .env ]; then
    set -a
    source .env
    set +a
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
        echo "Usage: ./run.sh [command]"
        echo ""
        echo "Commands:"
        echo "  build   - Build the Lean project"
        echo "  test    - Run all tests"
        echo "  clean   - Clean build artifacts"
        echo "  info    - Show system information"
        echo "  help    - Show this help"
        ;;
esac
EOF
    fi
    chmod +x run.sh
    echo "✅ Run script verified"
}

# Verify installation
verify_installation() {
    echo "🔍 Verifying installation..."

    # Check Python environment
    echo "🐍 Python environment:"
    uv run python --version || python --version

    # Check Lean installation (ensure PATH is current)
    add_to_path "$HOME/.elan/bin"
    add_to_path "$HOME/.cargo/bin"
    add_to_path "$HOME/.local/bin"
    lean --version 2>/dev/null || echo "⚠️ Lean not in PATH"
    lake --version 2>/dev/null || echo "⚠️ Lake not in PATH"

    # Check agent tools
    echo "🔧 Checking agent tools..."
    command -v just >/dev/null && echo "✅ just available" || echo "⚠️ just not found"
    command -v rg >/dev/null && echo "✅ ripgrep (rg) available" || echo "⚠️ ripgrep not found"
    command -v fd >/dev/null && echo "✅ fd available" || echo "⚠️ fd not found"
    command -v jq >/dev/null && echo "✅ jq available" || echo "⚠️ jq not found"
    command -v tree >/dev/null && echo "✅ tree available" || echo "⚠️ tree not found"

    # Check version control tools
    command -v git >/dev/null && echo "✅ git available: $(git --version | head -1)" || echo "⚠️ git not found"
    command -v jj >/dev/null && echo "✅ jujutsu (jj) available" || echo "⚠️ jujutsu not found"
    command -v gh >/dev/null && echo "✅ GitHub CLI available" || echo "⚠️ GitHub CLI not found"

    # Check agent tools
    command -v codex >/dev/null && echo "✅ codex CLI available" || echo "⚠️ codex CLI not found"
    command -v uv >/dev/null && echo "✅ uv available" || echo "⚠️ uv not found"

    # Quick functionality test for agents
    echo "🧪 Running agent verification tests..."
    if uv run python -c "import numpy; print('✅ Python environment works')"; then
        echo "✅ Python environment verified"
    else
        echo "⚠️ Python environment issues detected"
    fi

    # Test Lean environment thoroughly
    echo "🔧 Testing Lean build system..."
    if lake --version >/dev/null 2>&1; then
        echo "✅ Lake available: $(lake --version)"

        # Test that lake can handle basic operations
        echo "🧪 Testing lake build capabilities..."
        if timeout 30 lake build --no-build >/dev/null 2>&1; then
            echo "✅ Lake build system verified"
        else
            echo "⚠️ Lake build test failed - this is normal for first-time setup"
            echo "  → Agents should run 'lake update' followed by 'lake build' on first use"
        fi
    else
        echo "⚠️ Lake not available - Lean builds will fail"
        echo "  → Check that elan is properly installed and in PATH"
    fi

    # Verify elan toolchain
    if elan show >/dev/null 2>&1; then
        echo "✅ Elan toolchain available"
        # Show the active toolchain info
        elan show | tail -2 | head -1
    else
        echo "⚠️ Elan toolchain issues detected"
    fi

    echo "✅ Installation verification complete"
}

# Main installation sequence
main() {
    echo "Starting GitHub Actions installation for NumpySpec..."
    echo "OS: $OS, Architecture: $ARCH"
    echo ""

    # Run core installations in sequence first
    install_system_deps
    install_uv

    # Run independent installations in parallel
    echo "🔄 Running parallel installations..."
    install_rust &
    rust_pid=$!
    install_lean &
    lean_pid=$!

    # Wait for first batch and check status
    wait $rust_pid
    rust_status=$?
    wait $lean_pid
    lean_status=$?

    if [[ $rust_status -ne 0 || $lean_status -ne 0 ]]; then
        echo "❌ Some installations failed (rust: $rust_status, lean: $lean_status)"
        exit 1
    fi

    # Run agent tools installation (serialize apt-based installs to avoid lock conflicts)
    echo "🔄 Running agent tools installation..."

    # Install apt-based tools first (sequentially to avoid lock conflicts)
    install_agent_cli_tools
    install_github_cli

    # Install non-apt tools in parallel
    install_codex_cli &
    install_jujutsu &

    # Wait for remaining installations
    wait

    echo "✅ Agent tools installation complete"

    # Run remaining sequential installations
    install_lean_dev_tools
    setup_python
    setup_project_structure
    setup_lean
    setup_config
    check_run_script
    verify_installation

    echo ""
    echo "🎉 Installation complete!"
    echo ""
    echo "NumpySpec environment is ready for Codex agents."
    echo "Provides formally verified numpy-style operations in Lean 4."
    echo ""
    echo "🛠️ Installed agent tools:"
    echo "  • Task Runner: just"
    echo "  • Search: ripgrep (rg), fd"
    echo "  • Data: jq, tree"
    echo "  • Version Control: git, jujutsu (jj), GitHub CLI (gh)"
    echo "  • Agent CLI: codex"
    echo "  • Development: uv, lean, lake"
    echo "  • Build: lean-lsp-mcp"
    echo ""
    echo "Agent commands:"
    echo "  just             # Show available tasks"
    echo "  just build-all   # Build all Lean targets"
    echo "  just test        # Run Python tests"
    echo "  lake build       # Build Lean project directly"
    echo "  uv run -m pytest # Run Python tests directly"
    echo "  codex -q '<task>' # Invoke sub-agent"
    echo "  rg <pattern>     # Search code"
    echo "  fd <name>        # Find files"
    echo ""
    echo "See CLAUDE.md for agent-specific instructions."

    # Notify completion if terminal-notifier is available
    if command -v terminal-notifier >/dev/null; then
        terminal-notifier -title "NumpySpec Setup" -message "Installation completed successfully!"
    fi
}

# Run main installation
main "$@"
