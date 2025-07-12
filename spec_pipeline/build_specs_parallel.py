#!/usr/bin/env python3
"""
Script to build specifications for all Lean files in NumpySpec subdirectories.
Uses Claude API to process files in parallel and stores agent outputs.
"""

import os
import json
import subprocess
from pathlib import Path
from datetime import datetime
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import multiprocessing
import shutil
import tempfile

def find_lean_files(base_dir, start_dir=None):
    """Find all .lean files in subdirectories (not in root directory)."""
    lean_files = []
    base_path = Path(base_dir)
    
    # If start_dir is specified, use it as the starting point
    if start_dir:
        search_path = base_path / start_dir
        if not search_path.exists():
            print(f"Error: Directory {search_path} does not exist")
            return []
    else:
        search_path = base_path
    
    # Walk through all subdirectories
    for root, dirs, files in os.walk(search_path):
        root_path = Path(root)
        
        # Skip if this is the base NumpySpec directory itself
        if root_path == base_path:
            continue
            
        # Process all .lean files in subdirectories
        for file in files:
            if file.endswith('.lean'):
                file_path = root_path / file
                # Get relative path from NumpySpec directory
                relative_path = file_path.relative_to(base_path.parent)
                lean_files.append(str(relative_path))
    
    return sorted(lean_files)

def create_prompt(file_path):
    """Create the prompt for Claude with the specific file path."""
    return f"""Build the spec of '{file_path}' using the doc and the source code provided in itself. Go to NumpySpec/PIPELINE.md for detailed instructions. Make sure to read the whole file and follow the instructions, especially the important notices for agents: 1. **Ensure Compilability**: Make sure the file is compilable after adding the specs. Always verify compilation with lake build or use the Lean LSP MCP tools to check for errors. 2. **One Function Per File**: Make only one target function (def) and one spec (theorem) per file, the function name of the def function should be the same as the name of the target function. This keeps specifications modular and manageable. 3. **Use Vector Instead of Array**: Make sure to use Vector instead of Array in all specifications. This is crucial for the type-safe approach we're taking. 4. **Write to File**: Make sure you actually write the generated specification into the file using the Write tool. Don't just generate the specification without saving it. 5. **Try to Write Sufficiently Detailed Specifications**: The specifications should be detailed enough to be used as a guide for the implementation. Normally, the spec should contain sanity checks and actual (mathematical) properties of the function. Remember, write only one function and one spec that is aligned with the sanity and mathematical properties of the function, and the specs should be more than trivial."""

def process_single_file(args):
    """Process a single file - this will be run in parallel."""
    file_path, output_dir = args
    
    prompt = create_prompt(file_path)
    
    # Create a temporary config file for this session
    temp_config = None
    temp_config_path = None
    
    try:
        # Copy the base .mcp.json to a temporary file with unique name
        base_config_path = Path('.mcp.json')
        if base_config_path.exists():
            # Create a unique config file name based on process ID and file
            safe_filename = file_path.replace('/', '_').replace('.lean', '')
            temp_config_name = f'.claude-session-{os.getpid()}-{safe_filename}.json'
            temp_config_path = Path(temp_config_name)
            
            # Copy the config file
            shutil.copy2(base_config_path, temp_config_path)
            config_arg = str(temp_config_path)
        else:
            # Fall back to default if no base config exists
            config_arg = ".mcp.json"
        
        cmd = ['claude', '-p', prompt, "--config", config_arg, "--allowedTools",  "mcp__lean-lsp-mcp__lean_build, mcp__lean-lsp-mcp__lean_file_contents, mcp__lean-lsp-mcp__lean_diagnostic_messages, mcp__lean-lsp-mcp__lean_goal, mcp__lean-lsp-mcp__lean_term_goal, mcp__lean-lsp-mcp__lean_hover_info, mcp__lean-lsp-mcp__lean_completions, mcp__lean-lsp-mcp__lean_declaration_file, mcp__lean-lsp-mcp__lean_multi_attempt, mcp__lean-lsp-mcp__lean_run_code, mcp__lean-lsp-mcp__lean_leansearch, mcp__lean-lsp-mcp__lean_loogle, mcp__lean-lsp-mcp__lean_state_search, mcp__lean-lsp-mcp__lean_hammer_premise, ListMcpResourcesTool, ReadMcpResourceTool, mcp__browsermcp__browser_navigate, mcp__browsermcp__browser_go_back, mcp__browsermcp__browser_go_forward, mcp__browsermcp__browser_snapshot, mcp__browsermcp__browser_click, mcp__browsermcp__browser_hover, mcp__browsermcp__browser_type, mcp__browsermcp__browser_select_option, mcp__browsermcp__browser_press_key, mcp__browsermcp__browser_wait, mcp__browsermcp__browser_get_console_logs, mcp__browsermcp__browser_screenshot", "--verbose", "--output-format", "stream-json", "--allowedTools", "\"Bash(mkdir:*)\" \"mcp__browsermcp__browser_navigate\" \"mcp__browsermcp__browser_click\" \"Bash(rm:*)\" \"WebFetch(domain:raw.githubusercontent.com)\" \"Bash(export:*)\" \"WebFetch(domain:numpy.org)\" \"mcp__browsermcp__browser_press_key\" \"mcp__browsermcp__browser_snapshot\" \"mcp__browsermcp__browser_type\" \"WebFetch(domain:github.com)\" \"Bash(curl:*)\" \"WebFetch(domain:github.com)\" \"Bash(python3:*)\" \"Bash(ls:*)\"\"Bash(git add:*)\"\"Bash(find:*)\" \"Bash(uv pip:*)\"\"Bash(uv sync:*)\"\"Bash(elan which:*)\"\"Bash(just setup:*) \"\"Bash(lake:*) \"\"Bash(uv run:*) \"\"Bash(rg:*) \"\"mcp__lean-lsp-mcp__lean_diagnostic_messages \"\"Bash(elan toolchain install:*) \"\"mcp__lean-lsp-mcp__lean_hover_info \"\"mcp__lean-lsp-mcp__lean_build \"\"mcp__lean-lsp-mcp__lean_goal \"\"Bash(od:*) \"\"Bash(grep:*) \"\"mcp__lean-lsp-mcp__lean_completions \"\"mcp__lean-lsp-mcp__lean_declaration_file \"\"mcp__lean-lsp-mcp__lean_multi_attempt \"\"mcp__lean-lsp-mcp__lean_leansearch \"\"Bash(mv:*) \"\"Bash(python:*) \"\"Bash(for:*) \"\"Bash(do echo \"Building $file...\") \"\"Bash(echo \"Failed: $file\") \"\"Bash(done) \"\"mcp__lean-lsp-mcp__lean_file_contents \"\"Bash(cat:*) \"\"Bash(jq:*) \"\"Bash(chmod:*) \"\"Bash(uv add:*) \"\"Bash(jq:*) \"\"Bash(claude:*) \"\"Bash(chmod:*) \"\"Bash(./update_all_numpy_code.sh) \"\"Bash(do echo -e \"\\n--- $file ---\") \"\"Bash(git commit:*) \"\"Bash(*) \"\"Read(*) \"\"Edit(./*) \"\"WebFetch(domain:numpy.org) \"\"WebFetch(domain:github.com) \"\"WebFetch(domain:raw.githubusercontent.com) \"\"Bash(source:*) \"\"WebFetch(domain:api.github.com) \"\"Bash(sed:*) \"\"Bash(git checkout:*) \"\"Bash(pipx install:*) \"\"Bash(uv tool install:*) \"\"Bash(stack-pr view:*) \"\"Bash(brew install:*) \"\"Bash(gh auth:*) \"\"Bash(gh pr list:*) \"\"Bash(pip install:*) \"\"Bash(gh pr view:*) \"\"Bash(git cherry-pick:*) \"\"Bash(git reset:*) \"\"Bash(stack-pr submit:*) \"\"Bash(gh pr create:*) \"\"Bash(git push:*) \"\"Bash(git pull:*) \"\"Bash(git branch:*) \"\"Bash(git rev-parse:*) \"\"Bash(do) \"\"Bash(echo:*) \"\"Bash(echo) \"\"Bash(git stash:*) \"\"Bash(git fetch:*) \"\"Bash(touch:*) \"\"Edit(**/*) \"\"Edit(NumpySpec/**/*) \"\"Write(NumpySpec/**/*) \"\"Bash \"\"Read \"\"Write \"\"Edit"]
        
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout
        )
        
        # Save the output
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Create a safe filename
        safe_filename = file_path.replace('/', '_').replace('.lean', '_output.txt')
        output_file = output_path / safe_filename
        
        # Save the full output
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write(f"File: {file_path}\n")
            f.write(f"Timestamp: {datetime.now().isoformat()}\n")
            f.write(f"Return code: {result.returncode}\n")
            f.write(f"{'='*80}\n\n")
            f.write("=== STDOUT ===\n")
            f.write(result.stdout)
            f.write("\n\n=== STDERR ===\n")
            f.write(result.stderr)
        
        return {
            'file': file_path,
            'success': result.returncode == 0,
            'output_file': str(output_file),
            'timestamp': datetime.now().isoformat()
        }
        
    except subprocess.TimeoutExpired:
        return {
            'file': file_path,
            'success': False,
            'error': 'Timeout exceeded (10 minutes)',
            'timestamp': datetime.now().isoformat()
        }
    except Exception as e:
        return {
            'file': file_path,
            'success': False,
            'error': str(e),
            'timestamp': datetime.now().isoformat()
        }
    finally:
        # Clean up temporary config file
        if temp_config_path and temp_config_path.exists():
            try:
                temp_config_path.unlink()
            except:
                pass  # Ignore cleanup errors

def main():
    parser = argparse.ArgumentParser(description='Build specifications for Lean files using Claude in parallel')
    parser.add_argument('--start-dir', type=str, help='Starting directory within NumpySpec (e.g., "polynomial/chebyshev")')
    parser.add_argument('--output-dir', type=str, default='agent_outputs', help='Directory to store agent outputs')
    parser.add_argument('--workers', type=int, default=5, help='Number of parallel workers (default: 5)')
    parser.add_argument('--limit', type=int, help='Limit number of files to process')
    parser.add_argument('--dry-run', action='store_true', help='Show files that would be processed without running')
    
    args = parser.parse_args()
    
    # Base directory (parent of spec_pipeline)
    base_dir = Path(__file__).parent.parent / 'NumpySpec'
    
    # Find all lean files in subdirectories
    lean_files = find_lean_files(base_dir, args.start_dir)
    
    if not lean_files:
        print("No Lean files found in subdirectories")
        return
    
    print(f"Found {len(lean_files)} Lean files to process")
    
    # Apply limit if specified
    if args.limit:
        lean_files = lean_files[:args.limit]
        print(f"Limited to {len(lean_files)} files")
    
    # Dry run - just show what would be processed
    if args.dry_run:
        print("\nFiles that would be processed:")
        for file in lean_files:
            print(f"  - {file}")
        return
    
    print(f"Processing with {args.workers} parallel workers...")
    print(f"Outputs will be saved to: {args.output_dir}/")
    
    # Process files in parallel
    start_time = datetime.now()
    results = []
    
    # Prepare arguments for parallel processing
    process_args = [(file, args.output_dir) for file in lean_files]
    
    # Use ProcessPoolExecutor for true parallelism
    with ProcessPoolExecutor(max_workers=args.workers) as executor:
        # Submit all tasks
        future_to_file = {executor.submit(process_single_file, arg): arg[0] 
                          for arg in process_args}
        
        # Process completed tasks as they finish
        completed = 0
        for future in as_completed(future_to_file):
            file_path = future_to_file[future]
            completed += 1
            
            try:
                result = future.result()
                results.append(result)
                
                if result['success']:
                    print(f"[{completed}/{len(lean_files)}] ✓ {file_path}")
                else:
                    error_msg = result.get('error', 'Failed')
                    print(f"[{completed}/{len(lean_files)}] ✗ {file_path}: {error_msg}")
                    
            except Exception as exc:
                print(f"[{completed}/{len(lean_files)}] ✗ {file_path}: Exception: {exc}")
                results.append({
                    'file': file_path,
                    'success': False,
                    'error': str(exc),
                    'timestamp': datetime.now().isoformat()
                })
    
    end_time = datetime.now()
    duration = (end_time - start_time).total_seconds()
    
    # Save summary
    summary = {
        'metadata': {
            'start_time': start_time.isoformat(),
            'end_time': end_time.isoformat(),
            'duration_seconds': duration,
            'total_files': len(lean_files),
            'workers': args.workers,
            'output_directory': args.output_dir
        },
        'results': results
    }
    
    summary_file = Path(args.output_dir) / 'processing_summary.json'
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)
    
    # Print final summary
    successful = sum(1 for r in results if r['success'])
    failed = len(results) - successful
    
    print(f"\n{'='*50}")
    print(f"COMPLETED:")
    print(f"  Total files: {len(results)}")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Total time: {duration:.1f} seconds")
    print(f"  Outputs saved to: {args.output_dir}/")
    print(f"  Summary saved to: {summary_file}")
    print(f"{'='*50}")

if __name__ == '__main__':
    # Required for multiprocessing on some systems
    multiprocessing.set_start_method('spawn', force=True)
    main()