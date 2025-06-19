import Lake
open Lake DSL

/-- Main GaussianSpec package -/
package GaussianSpec where
  -- Lean options (typechecked!)
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

/-! Dependencies (order matters for compilation) -/

/-- Used for documentation generation -/
require verso from git "https://github.com/leanprover/verso" @ "main"

/-- Used for theorem proving. *Must* come before `mathlib` to avoid recompiling `mathlib`. --/
require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "temp-v4.21.0-rc3"

/--Used for math library--/
require mathlib from git "https://github.com/leanprover-community/mathlib4"

-- Main library
lean_lib GaussianSpec where
  -- Include the root module and all submodules
  globs := #[.andSubmodules `GaussianSpec]

-- FuncTracker sublibrary for 2D function tracking tables
lean_lib FuncTracker where
  -- Include all FuncTracker modules
  globs := #[.andSubmodules `FuncTracker]

-- Generated code library
lean_lib Generated where
  srcDir := "."
  -- Include all Spec modules from generated/Spec directory
  globs := #[.andSubmodules `generated]

-- Executables
@[default_target]
lean_exe gaussianspec where
  root := `Main

lean_exe gaussianspecmanual where
  root := `GaussianSpec.ManualMain
