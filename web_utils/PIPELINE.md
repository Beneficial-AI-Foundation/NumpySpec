# Pipeline for Generating NumPy Operations JSON Files

This document outlines the step-by-step process for generating comprehensive NumPy operations documentation in JSON format.

## Overview

The goal is to create structured JSON files containing NumPy function documentation, including names, descriptions, URLs, full documentation, and code references.

## Step-by-Step Pipeline

### 1. Categorize the Entire NumPy Repository

**Prompt:**
```
Use web search or browsermcp to explore the entire NumPy repository structure and documentation. Research how NumPy officially organizes its functions across all modules. Look for:
- Main module categories (e.g., numpy.linalg, numpy.random, numpy.fft, numpy.polynomial, etc.)
- Function groupings within the official documentation
- API reference structure

Create a comprehensive categorization scheme covering ALL NumPy functions. Store this in web_utils/numpy_full_categories.json with structure:
{
  "categories": {
    "module_or_category_name": {
      "description": "Clear definition of this module/category",
      "subcategories": {
        "subcategory_name": {
          "description": "What functions belong here",
          "search_strategy": "How to find these functions (e.g., module path, documentation section)"
        }
      },
      "fetch_strategy": "How to systematically extract all functions from this category"
    }
  }
}

Then create multiple sub-agents for each major category. Each sub-agent should:
1. Be given a clear scope (e.g., "all numpy.linalg functions", "all numpy.random functions")
2. Instructions to identify ALL functions in their category
3. Directive to follow specific pipeline steps for documentation extraction
4. Output to category-specific files

Example sub-agent creation:
```
claude -q --project-doc CLAUDE.md -a full-auto "Extract ALL NumPy linear algebra functions from numpy.linalg module. Use browsermcp to systematically go through the numpy.linalg documentation and identify every available function. Create a comprehensive list and then follow these specific steps from web_utils/PIPELINE.md:
- Step 2: Initial Request - Create a list of all numpy.linalg functions with names and URLs
- Step 4: Create Initial JSON Structure & Fetch Documentations - Extract full documentation and source code
- Step 6: Fixing Potential Issues - Ensure all source code is properly fetched
Store results in web_utils/output/linalg_all_operations.json"
```
```

### 2. Initial Request - Identify Target Functions and Gather Function Lists

**Prompt:**
```
Use the browsermcp tool to search for all numpy dense matrix linalg operations such as diagonal, transpose and etc. available. Make a list of them in web_utils/linalg_ops.json, just the names and urls to the exisiting documentation, leave the in-depth investigation later.
```

### 3. Categorize Specific Function Groups

**Prompt:**
```
Use web search or browsermcp to research how NumPy officially categorizes its functions in the documentation. Look for the main categories used in the NumPy documentation structure (e.g., Linear algebra, Array manipulation, Mathematical functions, etc.). 

Create a categorization scheme for the functions found in step 1. You may use:
- Official NumPy documentation categories as reference
- Your own logical grouping based on functionality

Store the categorization in web_utils/numpy_categories.json with this structure:
{
  "categories": {
    "category_name": {
      "description": "Clear definition of what functions belong in this category",
      "functions": ["list", "of", "function", "names"],
      "fetch_strategy": "How to identify/search for functions in this category"
    }
  }
}

Then create multiple sub-agents, one for each category. For each sub-agent, provide:
1. A clear definition of the category
2. The list of functions to process from that category
3. Instructions to follow specific steps in this pipeline for their assigned functions
4. Output location: web_utils/output/{category_name}_operations.json

Example sub-agent creation:
```
claude -q --project-doc CLAUDE.md -a full-auto "You are tasked with processing NumPy linear algebra decomposition functions. These are functions that decompose matrices into factors (like SVD, QR, LU decomposition). Process the following functions: [numpy.linalg.svd, numpy.linalg.qr, ...]. Follow these specific steps from web_utils/PIPELINE.md:
- Step 4: Create Initial JSON Structure & Fetch Documentations - Extract documentation and source code for each function
- Step 6: Fixing Potential Issues and Fetching More Source Code - Ensure complete source code retrieval
Store results in web_utils/output/decompositions_operations.json"
```
```

### 4. Create Initial JSON Structure & Fetch Documentations

**Prompt:**
```
"Use browsermcp and other tools to search for the docstring and source code, store them in web_utils/output/linalg_operation.json. For each function, create a JSON entry with these fields:
{
  "name": "numpy.linalg.function_name",
  "description": "Brief one-line description",
  "url": "Official NumPy documentation URL",
  "doc": "Full documentation string with parameters, returns, examples",
  "code": "Implementation or reference to source"
}
Remember, grab all the functions in the list in web_utils/linalg_ops.json, and store them in web_utils/output/linalg_operation.json. If you are not able to conduct that much work in a sequence, you may try to create sub-tasks or sub-agents to do the work: Decompose the linalg operations into smaller sub-tasks, such as matrix_vector_products, decompositions, eigenvalues, norms, solving_equations, other_ops, and handle them using sub-agents, which store the results separately in web_utils/. If you are doing so, output the draft file list for reference.
```

### 5. (Possible Follow-up) Merge and Unify Format

**Prompt:**
```
"Merge all individual JSON files in the list in web_utils/ into a single comprehensive file with this structure:
{
  "numpy_linalg_operations": {
    "category_name": [array of functions],
    ...
  },
  "metadata": {
    "total_functions": N,
    "categories": M,
    "generated_date": "YYYY-MM-DD",
    "source": "NumPy v2.3 documentation and GitHub repository"
  }
}"
```

### 6. Fixing Potential Issues and Fetching More Source Code

**Prompt:**
```
Currently, in web_utils/output/linalg_operations.json, there are some values which is not detailed docstring and source code, but rather a link to specific lines instead of a complete code which could be found on Github, fix them by using your mcp tool to fetch the doc and code from url given. For C-implemented functions, note that they are 'C implementation' with a reference.
```

### 7. Clean up and Finalize

**Prompt:**
```
Now check the format of the final JSON file in web_utils/output/linalg_operations.json, and make sure the format is correct. After that, delete all the draft files you produced in the previous steps, including sub-agent outputs, the python or lean script you used to generate the final file, .history files, and the intermediate files you used to generate the final file. Finally, make a new commit with the message "Update linalg_operations.json".
```

## Final Prompt (What is actually input to the Claude code agent)

Perform the pipeline demonstrated in web_utils/PIPELINE.md, and store the output in dir (or sub-dirs) within web_utils/full_numpy. Some of your jobs are already completed, and you can skip them. You can create task (or subagent) to decompose & accomplish complicated tasks. Note that you should provide detailed code for the "code" key when and if the source code could be found. Something like "code in xxx.py" is not welcomed if the code could be found in detail (there are exceptions, which is the source code lies in C file, and you could just indicate that code implemented in C). If you are unsure about what to do, see the alrady completed json for example (e.g. web_utils/full_numpy/linear_algebra/linalg_operations.json). Remember and check it every time you want to mark something as completed and move on: you should provide detailed code for the "code" key when and if the source code could be found. Something like "code in xxx.py" is not welcomed if the code could be found in detail (there are exceptions, which is the source code lies in C file, and you could just indicate that code implemented in C).