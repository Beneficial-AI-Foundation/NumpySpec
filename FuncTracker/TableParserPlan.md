# Plan: Compositional 2D Table Parser for FuncTracker

After studying Lean 4's parser infrastructure and metaprogramming capabilities, here's a comprehensive plan for building a robust 2D table parser.

## Core Insights

1. **Two-Phase Approach**: Separate syntax recognition from semantic interpretation
2. **Grid-First Parsing**: Parse the 2D structure into a grid before interpreting cells
3. **Custom Elaborator**: Use term elaboration for better control over the parsing process
4. **Parsec for Structure**: Use Lean's Parsec library for character-level grid parsing

## Architecture Overview

```
┌─────────────────┐
│ Syntax Layer    │  funcTable! ╔═══╗...╚═══╝
└────────┬────────┘
         │ extract raw string
┌────────▼────────┐
│ Grid Parser     │  Parsec-based 2D grid parser
└────────┬────────┘
         │ Grid[row][col]
┌────────▼────────┐
│ Cell Parser     │  Parse individual cells
└────────┬────────┘
         │ TableData
┌────────▼────────┐
│ Elaborator      │  Convert to FunctionTable
└────────┬────────┘
         │
    FunctionTable
```

## Detailed Design

### 1. Syntax Definition (Keep Simple)

```lean
-- Keep the syntax minimal - just capture the whole table
syntax "funcTable!" strLit : term

-- Alternative: capture as raw tokens
syntax "funcTable!" rawStx : term
```

### 2. Grid Parser (Parsec-Based)

```lean
import Std.Internal.Parsec
open Std.Internal.Parsec String

-- Grid cell content
inductive Cell where
  | content : String → Cell
  | border : Char → Cell
  | empty : Cell

-- Parse a 2D grid structure
structure Grid where
  cells : Array (Array Cell)
  rows : Nat
  cols : Nat

namespace GridParser

-- Parse horizontal border: ═══
def hBorder : Parser Unit := do
  let _ ← many1 (char '═')
  pure ()

-- Parse vertical border: │
def vBorder : Parser Unit := char '│' *> pure ()

-- Parse cell content between borders
def cellContent : Parser String := do
  let chars ← many (satisfy (· ≠ '│'))
  pure (String.mk chars.toList |>.trim)

-- Parse a complete row: │ cell │ cell │ ... │
def tableRow : Parser (Array String) := do
  let _ ← vBorder
  let cells ← sepBy vBorder cellContent
  return cells.toArray

-- Parse table structure
def parseTable : Parser Grid := do
  -- Top border: ╔═══╗
  let _ ← char '╔' *> hBorder *> char '╗' *> newline
  
  -- Parse rows
  let rows ← many1 (tableRow <* newline)
  
  -- Bottom border: ╚═══╝
  let _ ← char '╚' *> hBorder *> char '╝'
  
  -- Validate all rows have same width
  let cols := rows[0]!.size
  if rows.any (·.size ≠ cols) then
    fail "inconsistent row widths"
  
  return ⟨rows.toArray, rows.size, cols⟩

end GridParser
```

### 3. Cell Interpreter

```lean
-- Interpret cell contents based on position and content
def interpretCell (content : String) (col : Nat) : MacroM CellValue := do
  match col with
  | 0 => pure (CellValue.name content)  -- First column is function name
  | 1 => -- Second column is status
    match content with
    | "✗" => pure (CellValue.status .notStarted)
    | "⋯" => pure (CellValue.status .inProgress)
    | "✓" => pure (CellValue.status .implemented)
    | "✓✓" => pure (CellValue.status .tested)
    | "✓✓✓" => pure (CellValue.status .documented)
    | _ => throwError s!"invalid status symbol: {content}"
  | 2 => pure (CellValue.file content)
  | 3 => parseLineRange content  -- Parse "10-20" format
  | 4 => pure (CellValue.complexity content)
  | _ => throwError "too many columns"

-- Detect header rows
def isHeaderRow (row : Array String) : Bool :=
  row.any (·.toLower ∈ ["function", "status", "file", "lines", "complexity"])
```

### 4. Custom Term Elaborator

```lean
-- Main elaborator that ties everything together
@[term_elab funcTable!]
def elabFuncTable : TermElab := fun stx expectedType? => do
  match stx with
  | `(funcTable! $table:strLit) => do
    -- Extract the string content
    let tableStr := table.getString
    
    -- Parse into grid using Parsec
    let grid ← match GridParser.parseTable.run tableStr with
      | .ok _ grid => pure grid
      | .error pos msg => throwError s!"parse error at {pos}: {msg}"
    
    -- Skip header row if present
    let dataRows := if grid.rows > 0 && isHeaderRow grid.cells[0]! then
      grid.cells[1:]
    else
      grid.cells
    
    -- Convert grid to FunctionTable
    let functions ← dataRows.mapM (interpretRow ·)
    
    -- Build the expression
    let funcsExpr ← functions.mapM functionToExpr
    mkAppM ``FunctionTable.mk #[mkArrayLit ``TrackedFunction funcsExpr]
    
  | _ => throwUnsupportedSyntax
```

### 5. Alternative: Raw Token Approach

Instead of using string literals, we could capture raw tokens:

```lean
-- Capture everything between funcTable! and the end
syntax "funcTable!" rawTableContent : term

-- In the elaborator, reconstruct the string from raw tokens
def extractTableString (stx : Syntax) : String := do
  -- Walk the syntax tree collecting tokens
  let tokens := stx.getArgs.map (·.getAtomVal)
  String.join tokens.toList
```

## Implementation Strategy

### Phase 1: Basic Grid Parser
1. Implement Parsec-based grid parser
2. Test with simple tables
3. Handle border variations

### Phase 2: Cell Interpretation
1. Parse different cell types
2. Handle escape sequences
3. Validate cell contents

### Phase 3: Elaborator Integration
1. Create term elaborator
2. Connect to parser
3. Generate proper expressions

### Phase 4: Enhanced Features
1. Column alignment detection
2. Separator row support (╠═══╣)
3. Better error messages with positions

## Key Advantages

1. **Separation of Concerns**: Grid parsing is separate from interpretation
2. **Compositional**: Each phase can be tested independently
3. **Error Recovery**: Better error messages with position information
4. **Extensible**: Easy to add new cell types or table formats
5. **Performance**: Parsec is efficient for character-level parsing

## Testing Strategy

```lean
-- Test grid parser
#eval GridParser.parseTable.run "╔═══╗\n│ a │\n╚═══╝"

-- Test cell interpreter
#eval interpretCell "✓✓" 1  -- Should return Status.tested

-- Test full pipeline
def testTable := funcTable! "╔═════════════╗
│ foo │ ✓     │
│ bar │ ⋯     │
╚═════════════╝"

#check testTable : FunctionTable
```

## Comparison to Current Approach

Current approach issues:
- Trying to parse syntax trees directly
- Mixing syntax recognition with interpretation
- Complex pattern matching on syntax nodes

New approach benefits:
- Clean separation of parsing phases
- Standard parsing techniques (Parsec)
- Better error messages
- More maintainable

## Next Steps

1. Prototype the Parsec grid parser
2. Test with various table formats
3. Implement the elaborator
4. Integrate with existing FuncTracker types
5. Add comprehensive tests