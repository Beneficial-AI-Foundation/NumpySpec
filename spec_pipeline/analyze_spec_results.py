#!/usr/bin/env python3
"""
Script to analyze the results from build_specs.py
"""

import json
import sys
from pathlib import Path
from collections import defaultdict

def analyze_results(json_file):
    """Analyze the results from the spec building process."""
    
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    print(f"Analysis of spec building results from: {json_file}")
    print(f"{'='*60}")
    
    # Basic statistics
    total_files = len(data['files'])
    successful = 0
    failed = 0
    errors_by_type = defaultdict(int)
    
    # Analyze each file
    for file_path, file_data in data['files'].items():
        result = file_data['result']
        if result['success']:
            successful += 1
        else:
            failed += 1
            error = result.get('error', 'Unknown error')
            if 'stderr' in result and result['stderr']:
                error = result['stderr'][:100] + '...' if len(result['stderr']) > 100 else result['stderr']
            errors_by_type[error] += 1
    
    # Print summary
    print(f"\nSUMMARY:")
    print(f"  Total files: {total_files}")
    print(f"  Successful: {successful} ({successful/total_files*100:.1f}%)")
    print(f"  Failed: {failed} ({failed/total_files*100:.1f}%)")
    
    # Time analysis
    total_duration = sum(f['duration_seconds'] for f in data['files'].values())
    avg_duration = total_duration / total_files if total_files > 0 else 0
    
    print(f"\nTIMING:")
    print(f"  Total time: {total_duration/60:.1f} minutes")
    print(f"  Average time per file: {avg_duration:.1f} seconds")
    
    # Error analysis
    if errors_by_type:
        print(f"\nERROR TYPES:")
        for error, count in sorted(errors_by_type.items(), key=lambda x: x[1], reverse=True):
            print(f"  {count}x: {error}")
    
    # Failed files list
    if failed > 0:
        print(f"\nFAILED FILES:")
        for file_path, file_data in data['files'].items():
            if not file_data['result']['success']:
                print(f"  - {file_path}")
                if 'error' in file_data['result']:
                    print(f"    Error: {file_data['result']['error']}")
    
    # Successful files by directory
    success_by_dir = defaultdict(list)
    for file_path, file_data in data['files'].items():
        if file_data['result']['success']:
            dir_path = str(Path(file_path).parent)
            success_by_dir[dir_path].append(file_path)
    
    if success_by_dir:
        print(f"\nSUCCESSFUL FILES BY DIRECTORY:")
        for dir_path in sorted(success_by_dir.keys()):
            files = success_by_dir[dir_path]
            print(f"  {dir_path}: {len(files)} files")

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python analyze_spec_results.py <results.json>")
        sys.exit(1)
    
    analyze_results(sys.argv[1])