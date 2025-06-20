#!/usr/bin/env bash
set -euo pipefail

# Install script for GaussianSpec - compatible with OpenAI Codex and other automated environments
# This script configures the environment for both local and remote development
# Run this first: ./install.sh

echo "🚀 Installing GaussianSpec..."

# Check for required tools
check_command() {
    if ! command -v "$1" &> /dev/null; then
        echo "❌ $1 is required but not installed."
        echo "   Please install it and run this script again."
        exit 1
    fi
}

# Minimal requirements check
check_command python3
check_command curl

# Create virtual environment if it doesn't exist
if [ ! -d ".venv" ]; then
    echo "📦 Creating Python virtual environment..."
    python3 -m venv .venv
fi

# Activate virtual environment
echo "🔧 Activating virtual environment..."
source .venv/bin/activate

# Install Python dependencies
echo "📚 Installing Python dependencies..."
pip install --upgrade pip
pip install -r requirements.txt 2>/dev/null || {
    # Create minimal requirements if missing
    cat > requirements.txt << EOF
# Core dependencies
requests>=2.31.0
pydantic>=2.0.0
gymnasium>=0.29.0
numpy>=1.24.0
pytest>=7.4.0

# Development tools
ruff>=0.1.0
ipython>=8.0.0
EOF
    pip install -r requirements.txt
}

# Setup Lean 4 (if available)
if command -v lake &> /dev/null; then
    echo "🔨 Building Lean project..."
    lake build || echo "⚠️  Lean build failed - continuing setup"
else
    echo "ℹ️  Lean 4 not found - skipping Lean build"
fi

# Create necessary directories
mkdir -p generated/Spec
mkdir -p logs
mkdir -p .cache

# Create environment file for mobile access
cat > .env << EOF
# GaussianSpec Environment Configuration
PYTHONPATH=\${PYTHONPATH}:src
LEAN_PATH=\${LEAN_PATH}:.
REMOTE_COMPILATION=true
PANTOGRAPH_URL=https://api.morphcloud.com/pantograph
EOF

# Create a simple test script
cat > test_setup.py << 'EOF'
#!/usr/bin/env python3
"""Test that the setup completed successfully."""
import sys
try:
    from gaussianspec.subagents import LeanEditSubagent
    from gaussianspec.lean_server import LeanServerInterface
    print("✅ Python imports working")
    
    # Test basic functionality
    agent = LeanEditSubagent()
    print("✅ Subagent system initialized")
    
    print("\n🎉 Setup completed successfully!")
    print("You can now use this project with Codex or develop locally.")
    sys.exit(0)
except Exception as e:
    print(f"❌ Setup test failed: {e}")
    sys.exit(1)
EOF

chmod +x test_setup.py

# Run the test
echo "🧪 Testing setup..."
python test_setup.py

# Create mobile-friendly run script
cat > run.sh << 'EOF'
#!/usr/bin/env bash
# Quick run script for mobile development
source .venv/bin/activate 2>/dev/null || true
export PYTHONPATH="${PYTHONPATH}:src"

case "${1:-help}" in
    edit)
        python -m gaussianspec.subagents edit "${@:2}"
        ;;
    build)
        python -m gaussianspec.subagents build "${@:2}"
        ;;
    train)
        python -m gaussianspec.train "${@:2}"
        ;;
    server)
        python -m gaussianspec.lean_server "${@:2}"
        ;;
    *)
        echo "Usage: ./run.sh [edit|build|train|server] [args...]"
        echo "  edit   - Run the Lean edit subagent"
        echo "  build  - Run the build subagent (local or remote)"
        echo "  train  - Train the RL agent"
        echo "  server - Start the Lean server interface"
        ;;
esac
EOF

chmod +x run.sh

echo ""
echo "📱 Installation complete! The project is now ready for:"
echo "   - Local development: ./run.sh [command]"
echo "   - Mobile development via Codex"
echo "   - Remote compilation via Pantograph servers"
echo ""
echo "Next steps:"
echo "   ./run.sh edit    # Edit Lean files"
echo "   ./run.sh build   # Build the project"
echo "   ./run.sh train   # Train the RL agent"