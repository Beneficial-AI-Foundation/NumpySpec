import FuncTracker.TableParser.Basic

/--example 1-/
def gridExample : String:= "
  ╔══════════════════╦════════╦═════════╗
  ║ Function         ║ Status ║ Depends ║
  ╠══════════════════╬════════╬═════════╣
  ║ parseInput       ║   ✓    ║         ║
  ║ validateInput    ║   ✓✓   ║    ←    ║
  ║ processData      ║   ⋯    ║    ←    ║
  ║ generateOutput   ║   ✗    ║    ←    ║
  ╚══════════════════╩════════╩═════════╝
  "
/-- example 2-/

def gridTableStr : String :=
  "╔═══════════════╦═══════════════╦═══════════════╗\n" ++
  "║ Function      ║ Status        ║ DependsOn     ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func1         ║ ✓             ║      .        ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func2         ║ ⋯             ║ ←             ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func3         ║ ✓✓            ║        .      ║\n" ++
  "╠═══════════════╬═══════════════╬═══════════════╣\n" ++
  "║ func4         ║ ✗             ║   ←           ║\n" ++
  "╚═══════════════╩═══════════════╩═══════════════╝"

-- /-- Parse at least one non-empty cell content -/
-- def cellContentNonEmpty : Parser String := do
--   let content ← cell
--   if content.isEmpty then
--     fail s!"empty cell"
--   else
--     pure content
