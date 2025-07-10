#!/usr/bin/env python3
"""
Script to build specifications for all Lean files in NumpySpec subdirectories.
Uses Claude API to process each file and stores the full agent responses.
"""

import os
import json
import subprocess
import sys
from pathlib import Path
from datetime import datetime
import time
import argparse

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
    return f"""Build the spec of '{file_path}' using the doc and the source code provided in itself. Go to NumpySpec/PIPELINE.md for detailed instructions. Make sure the file is compilable after adding the specs. Make only one target function (def) and one spec (theorem) per file. Make sure to read the whole file and follow the instructions. Make sure to use Vector instead of Array."""

def run_claude_agent(file_path, prompt):
    """Run Claude agent with the given prompt and return the full response."""
    try:
        # Using claude CLI with -p flag for project mode
        # We'll capture the full output which contains Claude's response
        # claude -p "prompt" --mcp-config .mcp.json --allowedTools "mcp__permissions__approve" --permission-prompt-tool mcp__permissions__approve
        cmd = ['claude', '-p', prompt, '--mcp-config', '.mcp.json', '--allowedTools', 'mcp__permissions__approve', '--permission-prompt-tool', 'mcp__permissions__approve']
        
        print(f"Processing: {file_path}")
        print(f"Running command: {' '.join(cmd)}")
        
        # Run the command and capture output
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout per file (specs can take time)
        )
        
        # Store the full agent response
        agent_response = {
            'success': result.returncode == 0,
            'full_response': result.stdout,  # This contains Claude's full response
            'stderr': result.stderr,
            'return_code': result.returncode,
            'response_length': len(result.stdout)
        }
        
        # Try to extract key information from the response if possible
        if result.stdout:
            # Check if the response mentions any errors or success
            response_lower = result.stdout.lower()
            agent_response['mentions_error'] = 'error' in response_lower
            agent_response['mentions_success'] = any(word in response_lower for word in ['success', 'completed', 'done'])
            agent_response['mentions_sorry'] = 'sorry' in response_lower
            
            # Get first few lines as preview
            lines = result.stdout.strip().split('\n')
            agent_response['preview'] = '\n'.join(lines[:5]) + ('...' if len(lines) > 5 else '')
        
        return agent_response
        
    except subprocess.TimeoutExpired:
        return {
            'success': False,
            'error': 'Timeout exceeded (10 minutes)',
            'full_response': '',
            'stderr': '',
            'response_length': 0
        }
    except Exception as e:
        return {
            'success': False,
            'error': str(e),
            'full_response': '',
            'stderr': '',
            'response_length': 0
        }

def save_agent_response(file_path, response, output_dir):
    """Save the individual agent response to a separate file."""
    # Create output directory if it doesn't exist
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    # Create a safe filename from the lean file path
    safe_filename = file_path.replace('/', '_').replace('.lean', '_response.txt')
    response_file = output_path / safe_filename
    
    # Save the full response
    with open(response_file, 'w', encoding='utf-8') as f:
        f.write(f"File: {file_path}\n")
        f.write(f"Timestamp: {datetime.now().isoformat()}\n")
        f.write(f"{'='*80}\n\n")
        f.write(response.get('full_response', ''))
    
    return str(response_file)

def main():
    parser = argparse.ArgumentParser(description='Build specifications for Lean files using Claude')
    parser.add_argument('--start-dir', type=str, help='Starting directory within NumpySpec (e.g., "polynomial/chebyshev")')
    parser.add_argument('--output', type=str, default='spec_build_results.json', help='Output JSON file for results summary')
    parser.add_argument('--responses-dir', type=str, default='agent_responses', help='Directory to store individual agent responses')
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
    
    # Results storage
    results = {
        'metadata': {
            'start_time': datetime.now().isoformat(),
            'total_files': len(lean_files),
            'base_directory': str(base_dir),
            'start_directory': args.start_dir,
            'responses_directory': args.responses_dir
        },
        'files': {}
    }
    
    # Process each file
    for i, file_path in enumerate(lean_files, 1):
        print(f"\n[{i}/{len(lean_files)}] Processing: {file_path}")
        
        # Create prompt
        prompt = create_prompt(file_path)
        
        # Run Claude agent
        start_time = time.time()
        result = run_claude_agent(file_path, prompt)
        end_time = time.time()
        
        # Save individual response
        response_file = save_agent_response(file_path, result, args.responses_dir)
        
        # Store result summary (not the full response to keep JSON manageable)
        results['files'][file_path] = {
            'timestamp': datetime.now().isoformat(),
            'duration_seconds': end_time - start_time,
            'prompt': prompt,
            'response_file': response_file,
            'success': result['success'],
            'response_length': result.get('response_length', 0),
            'preview': result.get('preview', ''),
            'mentions_error': result.get('mentions_error', False),
            'mentions_success': result.get('mentions_success', False),
            'error': result.get('error', None)
        }
        
        # Save intermediate results after each file
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)
        
        # Status update
        if result['success']:
            print(f"  ✓ Success (took {end_time - start_time:.1f}s, response: {result['response_length']} chars)")
            print(f"  → Response saved to: {response_file}")
        else:
            print(f"  ✗ Failed: {result.get('error', 'Unknown error')}")
        
        # Small delay between requests to avoid rate limiting
        if i < len(lean_files):
            time.sleep(2)
    
    # Final summary
    results['metadata']['end_time'] = datetime.now().isoformat()
    
    successful = sum(1 for f in results['files'].values() if f['success'])
    failed = len(results['files']) - successful
    
    print(f"\n{'='*50}")
    print(f"SUMMARY:")
    print(f"  Total files processed: {len(results['files'])}")
    print(f"  Successful: {successful}")
    print(f"  Failed: {failed}")
    print(f"  Results summary saved to: {args.output}")
    print(f"  Individual responses saved to: {args.responses_dir}/")
    print(f"{'='*50}")
    
    # Save final results
    with open(args.output, 'w') as f:
        json.dump(results, f, indent=2)

if __name__ == '__main__':
    main()