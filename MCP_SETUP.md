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

### Prerequisites
1. Install `uv` (Python package manager):
   ```bash
   curl -LsSf https://astral.sh/uv/install.sh | sh
   ```

2. Install the MCP servers:
   ```bash
   uvx lean-lsp-mcp --help  # Test installation
   uvx mcp-leanexplore --help  # Test installation
   ```

## Configuration

### For VS Code / Cursor

1. Copy the provided `mcp-config.json` to `.cursor/mcp.json` or `.vscode/mcp.json`:
   ```bash
   mkdir -p .cursor
   cp mcp-config.json .cursor/mcp.json
   ```

2. Update the `LEAN_PROJECT_PATH` in the config to point to your project root.

### For Claude Desktop App

1. On macOS/Linux, add to `~/.config/claude/claude_desktop_config.json`:
   ```json
   {
     "mcpServers": {
       "lean-lsp": {
         "command": "uvx",
         "args": ["lean-lsp-mcp"],
         "env": {
           "LEAN_PROJECT_PATH": "/path/to/NumpySpec"
         }
       }
     }
   }
   ```

2. On Windows, add to `%APPDATA%\Claude\claude_desktop_config.json`

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

## Environment Variables

You can also set these environment variables:
- `LEAN_PROJECT_PATH`: Path to the Lean project
- `LAKE_BUILD_DIR`: Custom build directory for Lake

## Project-Specific Settings

The project includes example permission settings in:
- `src/numpyspec/data/array/stdarray/.claude/settings.local.json`
- `src/numpyspec/data/array/ndarray/.claude/settings.local.json`

These demonstrate how to allow/deny specific MCP tools at a directory level.