import Lake
open Lake DSL

-- Main GaussianSpec package
package «GaussianSpec» where
  version := "0.1.0"
  -- Lean options (typechecked!)
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

-- Dependencies (order matters for compilation)
require verso from git "https://github.com/leanprover/verso" @ "main"
require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "temp-v4.21.0-rc3"
require mathlib from git "https://github.com/leanprover-community/mathlib4"

-- Main library
lean_lib «GaussianSpec» where
  -- Include the root module and all submodules
  globs := #[.andSubmodules `GaussianSpec]

-- Generated code library
lean_lib «Generated» where
  srcDir := "generated"
  -- Include all Spec modules
  globs := #[.andSubmodules `Spec]

-- Executables
@[default_target]
lean_exe «gaussianspec» where
  root := `Main

lean_exe «gaussianspecmanual» where
  root := `GaussianSpec.ManualMain

-- Targets for building specific components
target allLibs : Unit := do
  let libs ← [
    findLeanLib? `GaussianSpec,
    findLeanLib? `Generated
  ].filterMapM id
  libs.forM fun lib => fetch <| lib.target
  return .nil

-- Convenience target for building just generated code
target generated : Unit := do
  if let some lib ← findLeanLib? `Generated then
    fetch lib.target
  return .nil