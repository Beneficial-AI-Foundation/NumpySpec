# MCP (Model Context Protocol) Setup for NumpySpec

This document explains how to set up Lean-related MCP tools for collaborators.

## Available Lean MCP Tools

### 1. lean-lsp-mcp
Provides LSP (Language Server Protocol) integration for Lean 4:
- Build project and restart LSP
- Get file contents with line annotations
- Get diagnostic messages
- Get proof goals and term goals
- Get hover information
- Find code completions
- Search declarations
- Run code snippets
- Search theorems via leansearch.net

### 2. leanexplore MCP
Provides advanced Lean theorem search capabilities:
- Search Lean statement groups
- Get statements by ID
- Get dependencies between statements
- Both API and local search variants

## Installation

### Installation for Lean-lsp-mcp
1. Install `uv` (Python package manager):
   ```bash
   curl -LsSf https://astral.sh/uv/install.sh | sh
   ```

2. Install the MCP servers:
   ```bash
   pip install lean-lsp-mcp
   lean-lsp-mcp --help  # Test installation
   ```

### Installation for leanexplore
1. Use pypi to install leanexplore:
   ```bash
   pip install leanexplore
   leanexplore --help  # Test installation
   ```

2. Set up Local or API backend:
   - Local backend (Corresponding to `leanexploreLocal` in `mcp-config.json`):
     ```bash
     leanexplore mcp serve --backend local
     ```
   - API backend (Corresponding to `leanexploreAPI` in `mcp-config.json`): Get API key from [leanexplore](https://leanexplore.net/api)
     ```bash
     leanexplore mcp serve --backend api --api-key __your_api_key__
     ```

3. Change the mcp-config.json corresponingly:
    - Change the `command` field to the path of the leanexplore executable (You can use `which leanexplore` to get the path).
    - If you use the API backend, you need to change the `api-key` field to your API key.

## Configuration

### For VS Code / Cursor

1. Copy the provided `mcp-config.json` to `.cursor/mcp.json` or `.vscode/mcp.json`:
   ```bash
   mkdir -p .cursor
   cp mcp-config.json .cursor/mcp.json
   ```

2. Update the `LEAN_PROJECT_PATH` in the config to point to your project root.

### For Claude Desktop App

On macOS/Linux, add to `~/.config/claude/claude_desktop_config.json`:
  ```json
  {
    "mcpServers": {
      "lean-lsp": {
        "command": "uvx",
        "args": ["lean-lsp-mcp"],
        "env": {}
      }
    }
  }
  ```

## Usage in Claude

Once configured, Claude will have access to these Lean tools:

- `mcp__lean-lsp__lean_build` - Build the project
- `mcp__lean-lsp__lean_goal` - Check proof goals
- `mcp__lean-lsp__lean_hover_info` - Get type information
- `mcp__lean-lsp__lean_completions` - Get code completions
- `mcp__leanexploreAPI__search` - Search Lean theorems
- And many more...

## Troubleshooting

1. **MCP server not starting**: Check that `uvx` is in your PATH
2. **Lean project not found**: Ensure `LEAN_PROJECT_PATH` is absolute
3. **Permission errors**: The `.claude/settings.local.json` files can restrict which MCP tools are allowed

## Project-Specific Settings

The project includes example permission settings in:
- `src/numpyspec/data/array/stdarray/.claude/settings.local.json`
- `src/numpyspec/data/array/ndarray/.claude/settings.local.json`

These demonstrate how to allow/deny specific MCP tools at a directory level.