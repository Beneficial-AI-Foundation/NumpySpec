import FuncTracker.Basic

namespace FuncTracker

/-- Pretty print a progress report -/
def Progress.pretty (p : Progress) : String :=
  let pct := p.percentComplete
  let bar := String.mk <| List.replicate (pct.toUInt32.toNat / 5) '█' ++
             List.replicate (20 - pct.toUInt32.toNat / 5) '░'
  s!"Progress: [{bar}] {pct.toUInt32}%\n" ++
  s!"  Total: {p.total}\n" ++
  s!"  Not Started: {p.notStarted}\n" ++
  s!"  In Progress: {p.inProgress}\n" ++
  s!"  Implemented: {p.implemented}\n" ++
  s!"  Tested: {p.tested}\n" ++
  s!"  Documented: {p.documented}"

/-- Generate a markdown report -/
def FunctionTable.toMarkdown (table : FunctionTable) : String :=
  let header := "| Function | Status | File | Lines | Complexity |\n|----------|--------|------|-------|------------|\n"
  let rows := table.functions.map fun f =>
    let file := f.file.getD "-"
    let lines := match f.lines with
      | some (s, e) => s!"{s}-{e}"
      | none => "-"
    let complexity := f.complexity.getD "-"
    s!"| {f.name} | {f.status.toSymbol} | {file} | {lines} | {complexity} |"
  
  header ++ String.intercalate "\n" rows.toList ++ "\n\n" ++ table.computeProgress.pretty

/-- Generate an HTML report -/
def FunctionTable.toHTML (table : FunctionTable) : String :=
  let rows := table.functions.map fun f =>
    let statusClass := match f.status with
      | .notStarted => "not-started"
      | .inProgress => "in-progress"
      | .implemented => "implemented"
      | .tested => "tested"
      | .documented => "documented"
    
    let file := f.file.getD "-"
    let lines := match f.lines with
      | some (s, e) => s!"{s}-{e}"
      | none => "-"
    let complexity := f.complexity.getD "-"
    
    s!"<tr>
        <td>{f.name}</td>
        <td class=\"{statusClass}\">{f.status.toSymbol}</td>
        <td>{file}</td>
        <td>{lines}</td>
        <td>{complexity}</td>
      </tr>"
  
  let progress := table.computeProgress
  let pct := progress.percentComplete.toUInt32
  
  let style := "table { border-collapse: collapse; width: 100%; } " ++
               "th, td { border: 1px solid #ddd; padding: 8px; text-align: left; } " ++
               "th { background-color: #f2f2f2; } " ++
               ".not-started { color: red; } " ++
               ".in-progress { color: orange; } " ++
               ".implemented { color: green; } " ++
               ".tested { color: darkgreen; } " ++
               ".documented { color: darkgreen; font-weight: bold; } " ++
               ".progress-bar { background-color: #f0f0f0; border-radius: 10px; padding: 3px; } " ++
               ".progress-fill { background-color: #4CAF50; height: 20px; border-radius: 10px; }"
  
  s!"<html>
<head>
  <style>{style}</style>
</head>
<body>
  <h1>Function Implementation Tracker</h1>
  
  <div class=\"progress-bar\">
    <div class=\"progress-fill\" style=\"width: {pct}%\"></div>
  </div>
  <p>{pct}% Complete ({progress.implemented + progress.tested + progress.documented}/{progress.total} functions)</p>
  
  <table>
    <thead>
      <tr>
        <th>Function</th>
        <th>Status</th>
        <th>File</th>
        <th>Lines</th>
        <th>Complexity</th>
      </tr>
    </thead>
    <tbody>
      {String.intercalate "\n      " rows.toList}
    </tbody>
  </table>
  
  <h2>Summary</h2>
  <ul>
    <li>Not Started: {progress.notStarted}</li>
    <li>In Progress: {progress.inProgress}</li>
    <li>Implemented: {progress.implemented}</li>
    <li>Tested: {progress.tested}</li>
    <li>Documented: {progress.documented}</li>
  </ul>
</body>
</html>"

end FuncTracker