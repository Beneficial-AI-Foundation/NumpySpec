#!/usr/bin/env python3
"""Parse numpy dependency graph SVG directly to extract dependencies."""

import re
from collections import defaultdict, deque

def parse_svg_graph(svg_file):
    """Parse SVG file to extract nodes and edges."""
    nodes = set()
    edges = []
    
    with open(svg_file, 'r') as f:
        content = f.read()
    
    # Find all node definitions
    node_pattern = r'<g id="node\d+" class="node">.*?<title>(.*?)</title>'
    for match in re.finditer(node_pattern, content, re.DOTALL):
        node_name = match.group(1)
        if node_name and node_name != 'G':
            nodes.add(node_name)
    
    # Find all edge definitions
    edge_pattern = r'<g id="edge\d+" class="edge">.*?<title>(.*?)&#45;&gt;(.*?)</title>'
    for match in re.finditer(edge_pattern, content, re.DOTALL):
        source = match.group(1)
        target = match.group(2)
        if source and target:
            edges.append((source, target))
    
    return list(nodes), edges

def build_dependency_graph(edges):
    """Build adjacency lists for the dependency graph."""
    # dependencies[A] = set of modules that A depends on
    dependencies = defaultdict(set)
    # dependents[A] = set of modules that depend on A
    dependents = defaultdict(set)
    # all_nodes includes nodes that may only appear in edges
    all_nodes = set()
    
    for source, target in edges:
        dependencies[source].add(target)
        dependents[target].add(source)
        all_nodes.add(source)
        all_nodes.add(target)
    
    return dependencies, dependents, all_nodes

def topological_sort_with_levels(nodes, dependencies):
    """Perform topological sort and group by dependency levels."""
    # Calculate in-degree for each node
    in_degree = {node: len(dependencies.get(node, set())) for node in nodes}
    
    # Start with nodes that have no dependencies
    current_level = [node for node in nodes if in_degree[node] == 0]
    levels = []
    processed = set()
    
    while current_level:
        levels.append(sorted(current_level))
        next_level = []
        
        for node in current_level:
            processed.add(node)
            # Check all nodes to see if this was their last dependency
            for other_node in nodes:
                if node in dependencies.get(other_node, set()) and other_node not in processed:
                    in_degree[other_node] -= 1
                    if in_degree[other_node] == 0:
                        next_level.append(other_node)
        
        current_level = next_level
    
    return levels

def analyze_module_categories(nodes):
    """Categorize modules by their names and paths."""
    categories = defaultdict(list)
    
    for node in nodes:
        parts = node.split('_')
        
        # Skip test modules for main analysis
        if 'test' in node.lower():
            categories['testing'].append(node)
            continue
            
        # Core numpy modules
        if node == 'numpy' or node == 'numpy_version':
            categories['root'].append(node)
        elif node.startswith('numpy__core') or node.startswith('numpy_core'):
            categories['core'].append(node)
        elif node.startswith('numpy__typing'):
            categories['typing'].append(node)
        elif node.startswith('numpy_linalg'):
            categories['linalg'].append(node)
        elif node.startswith('numpy_fft'):
            categories['fft'].append(node)
        elif node.startswith('numpy_random'):
            categories['random'].append(node)
        elif node.startswith('numpy_polynomial'):
            categories['polynomial'].append(node)
        elif node.startswith('numpy_lib'):
            categories['lib'].append(node)
        elif node.startswith('numpy_ma'):
            categories['masked_arrays'].append(node)
        elif node.startswith('numpy_f2py'):
            categories['f2py'].append(node)
        elif node.startswith('numpy__'):
            categories['internal'].append(node)
        else:
            categories['other'].append(node)
    
    return dict(categories)

def main():
    print("Parsing numpy dependency graph...")
    svg_file = '/Users/louhantao/Desktop/code/semester_6.5/draft/numpy_graph.svg'
    
    nodes, edges = parse_svg_graph(svg_file)
    print(f"Found {len(nodes)} modules and {len(edges)} dependencies")
    
    dependencies, dependents, all_nodes = build_dependency_graph(edges)
    
    # Include all nodes from edges in our analysis
    all_nodes_list = sorted(all_nodes.union(nodes))
    
    print("\n" + "="*80)
    print("DEPENDENCY ANALYSIS")
    print("="*80)
    
    # Find modules with no dependencies (good starting points)
    no_deps = [node for node in all_nodes_list if len(dependencies.get(node, [])) == 0]
    print(f"\nModules with no dependencies ({len(no_deps)}):")
    for i, node in enumerate(sorted(no_deps)[:15], 1):
        print(f"  {i:2d}. {node}")
    if len(no_deps) > 15:
        print(f"  ... and {len(no_deps) - 15} more")
    
    # Find most depended-upon modules
    print("\nMost depended-upon modules:")
    dep_counts = [(node, len(dependents.get(node, []))) for node in all_nodes_list]
    dep_counts.sort(key=lambda x: x[1], reverse=True)
    for i, (node, count) in enumerate(dep_counts[:15], 1):
        if count > 0:
            print(f"  {i:2d}. {node}: {count} modules depend on it")
    
    # Perform topological sort with levels
    print("\n" + "="*80)
    print("DEPENDENCY LEVELS (Topological Sort)")
    print("="*80)
    
    levels = topological_sort_with_levels(all_nodes_list, dependencies)
    
    for i, level in enumerate(levels[:10]):  # Show first 10 levels
        print(f"\nLevel {i} ({len(level)} modules):")
        for j, node in enumerate(sorted(level)[:10], 1):
            deps = list(dependencies.get(node, []))[:3]
            if deps:
                print(f"  {j:2d}. {node} <- depends on: {', '.join(deps)}")
            else:
                print(f"  {j:2d}. {node} <- no dependencies")
        if len(level) > 10:
            print(f"  ... and {len(level) - 10} more")
    
    # Analyze categories
    print("\n" + "="*80)
    print("MODULE CATEGORIES")
    print("="*80)
    
    categories = analyze_module_categories(all_nodes_list)
    
    # Define priority order for implementation
    priority_categories = [
        'root', 'core', 'typing', 'internal', 'lib', 
        'linalg', 'fft', 'random', 'polynomial', 
        'masked_arrays', 'other', 'f2py', 'testing'
    ]
    
    for cat in priority_categories:
        if cat in categories and categories[cat]:
            modules = categories[cat]
            print(f"\n{cat.upper()} ({len(modules)} modules):")
            # Sort by dependency count (fewer dependencies first)
            modules_with_deps = [(m, len(dependencies.get(m, []))) for m in modules]
            modules_with_deps.sort(key=lambda x: x[1])
            
            for i, (module, dep_count) in enumerate(modules_with_deps[:8], 1):
                print(f"  {i}. {module} ({dep_count} dependencies)")
            
            if len(modules) > 8:
                print(f"  ... and {len(modules) - 8} more")
    
    # Generate implementation order
    print("\n" + "="*80)
    print("RECOMMENDED IMPLEMENTATION ORDER")
    print("="*80)
    
    print("""
Based on the dependency analysis, here's the recommended order for porting NumPy to Lean:

PHASE 1: Core Foundation (Essential Infrastructure)
--------------------------------------------------
1. numpy_version - Version information
2. numpy_exceptions - Exception hierarchy
3. numpy_dtypes - Basic data types
4. numpy__typing__scalars - Scalar type definitions
5. numpy__typing__shape - Shape type definitions
6. numpy__typing__dtype_like - DType-like definitions
7. numpy_core__multiarray_umath - Core array and ufunc C interface
8. numpy_core_multiarray - Core multiarray functionality

PHASE 2: Type System and Array Structure
----------------------------------------
1. numpy_core__dtype - Data type system
2. numpy_core_numerictypes - Numeric type definitions
3. numpy__typing__array_like - Array-like type definitions
4. numpy__typing__nested_sequence - Nested sequence types
5. numpy_core__internal - Internal array structure
6. numpy_core_overrides - Array function overrides

PHASE 3: Basic Array Operations
-------------------------------
1. numpy_core_numeric - Numeric operations
2. numpy_core_fromnumeric - Array creation from numeric
3. numpy_core_shape_base - Shape manipulation
4. numpy_core_function_base - Basic array functions
5. numpy_lib__shape_base_impl - Shape base implementation
6. numpy_lib__stride_tricks_impl - Stride tricks

PHASE 4: Mathematical Operations
--------------------------------
1. numpy_core_umath - Universal functions (ufuncs)
2. numpy_core_einsumfunc - Einstein summation
3. numpy_lib__ufunclike_impl - Ufunc-like operations
4. numpy_lib__function_base_impl - Function base implementation

PHASE 5: Advanced Array Features
--------------------------------
1. numpy_lib__arraysetops_impl - Set operations on arrays
2. numpy_lib__arraypad_impl - Array padding
3. numpy_lib__index_tricks_impl - Advanced indexing
4. numpy_core_records - Structured arrays
5. numpy_ma_core - Masked arrays core

PHASE 6: Domain-Specific Modules
--------------------------------
1. numpy_linalg - Linear algebra
2. numpy_fft - Fast Fourier Transform
3. numpy_random - Random number generation
4. numpy_polynomial - Polynomial operations

PHASE 7: I/O and Utilities
--------------------------
1. numpy_lib__npyio_impl - NumPy I/O operations
2. numpy_lib__format_impl - Array format handling
3. numpy_lib__utils_impl - Utility functions
4. numpy_ctypeslib - C-types library interface

PHASE 8: Testing Infrastructure
-------------------------------
1. numpy_testing - Testing utilities
2. numpy_testing__private_utils - Private testing utilities
3. Test modules for each implemented component

Key Implementation Notes:
------------------------
- Start with modules that have 0 dependencies
- Implement type definitions before operations
- Core array structure is critical for everything else
- Many modules can be implemented in parallel within each phase
- Testing infrastructure should be built alongside main modules
- F2py modules can be deferred as they're for Fortran integration
""")
    
    # Show critical path
    print("\n" + "="*80)
    print("CRITICAL PATH TO NUMPY CORE")
    print("="*80)
    
    # Find dependencies of numpy module itself
    numpy_deps = set()
    to_process = ['numpy']
    processed = set()
    
    while to_process:
        current = to_process.pop(0)
        if current in processed:
            continue
        processed.add(current)
        
        for dep in dependencies.get(current, []):
            numpy_deps.add(dep)
            if dep not in processed:
                to_process.append(dep)
    
    print(f"\nDirect and indirect dependencies of 'numpy' module ({len(numpy_deps)}):")
    # Group by category
    numpy_deps_by_cat = defaultdict(list)
    for dep in numpy_deps:
        for cat, modules in categories.items():
            if dep in modules:
                numpy_deps_by_cat[cat].append(dep)
                break
    
    for cat in priority_categories:
        if cat in numpy_deps_by_cat:
            print(f"\n{cat.upper()}:")
            for dep in sorted(numpy_deps_by_cat[cat])[:10]:
                print(f"  - {dep}")
            if len(numpy_deps_by_cat[cat]) > 10:
                print(f"  ... and {len(numpy_deps_by_cat[cat]) - 10} more")

if __name__ == '__main__':
    main()