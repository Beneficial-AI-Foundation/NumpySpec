#!/usr/bin/env bash
# Thin wrapper for GitHub Actions to call codex-install.sh

set -euo pipefail

# Set GitHub Actions environment flag
export GITHUB_ACTIONS=true

# Ensure we're in the repo root
cd "$(dirname "$0")/../.."

# Make the main script executable
chmod +x codex-install.sh

# Run the main installation script
./codex-install.sh