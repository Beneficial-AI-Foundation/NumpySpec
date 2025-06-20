#!/usr/bin/env bash
# codex-install.sh – bootstrap script expected by the open-source Codex CLI
#
# The Codex CLI looks for a file called `codex-install.sh` at the repository
# root and executes it in a fresh (often containerised) environment to install
# all project dependencies.  We already ship `setup_codex.sh`, which does the
# heavy lifting.  To avoid code duplication we simply delegate to that script
# if it is present, otherwise we fall back to the more general `install.sh`.
#
# The delegation keeps maintenance easy – any future changes only need to be
# made in one place.

set -euo pipefail

echo "🚀 Starting Codex installation…"

# If a dedicated Codex setup script exists, use it.
if [[ -f "setup_codex.sh" ]]; then
  echo "🔗 Found setup_codex.sh – forwarding…"
  exec bash "setup_codex.sh" "$@"
fi

# Otherwise fall back to the generic install.sh that ships with the repo.
if [[ -f "install.sh" ]]; then
  echo "🔗 setup_codex.sh not found, falling back to install.sh…"
  exec bash "install.sh" "$@"
fi

# If neither script is available, print an error so the CI job fails clearly.
echo "❌ Neither setup_codex.sh nor install.sh were found.  Cannot continue!"
exit 1
