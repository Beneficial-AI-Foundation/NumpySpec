import VersoManual
import GaussianSpec.Manual

open Verso.Genre Manual

/-- Configuration for the generated manual.
At this stage we only emit multi-page HTML; other formats can be added later. -/
private def cfg : Config := {
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 2
}

/-- Entry-point for `lake exe gaussianspecmanual`. Builds the HTML artefacts in `_out/`.
Use e.g.

```
lake build
lake exe gaussianspecmanual
python3 -m http.server 8000 --directory _out/html-multi &
```

and open <http://localhost:8000> in a browser.
-/
def main := manualMain (%doc GaussianSpec.Manual) (config := cfg)
