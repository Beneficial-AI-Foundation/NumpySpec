import Lake
open Lake DSL

package GaussianSpec where
  version := "0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

require verso from git "https://github.com/leanprover/verso" @ "main"
require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib GaussianSpec

lean_lib generated where
  srcDir := "."

lean_exe gaussianspec where
  root := `Main