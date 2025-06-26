import Lake
open Lake DSL

package leanArrayLib where
  leanOptions := #[
    ⟨`linter.missingDocs, true⟩
  ]

lean_lib LeanArrayLib
lean_lib NDArray

@[default_target]
lean_exe leanarraylib where
  root := `Main

lean_exe testexe where
  root := `Test

lean_exe ndtest where
  root := `NDArrayTest

-- Test scripts
script test do
  -- First ensure everything is built
  IO.println "Building test executables..."
  let buildResult ← IO.Process.output {
    cmd := "lake"
    args := #["build", "testexe", "ndtest"]
  }
  if buildResult.exitCode ≠ 0 then
    IO.eprintln s!"Build failed:\n{buildResult.stderr}"
    return buildResult.exitCode
  
  IO.println "Running all tests..."
  
  -- Run LeanArrayLib tests
  IO.println "\n=== LeanArrayLib Tests ==="
  let testResult ← IO.Process.output {
    cmd := "./.lake/build/bin/testexe"
  }
  IO.print testResult.stdout
  if testResult.exitCode ≠ 0 then
    IO.eprintln testResult.stderr
  
  -- Run NDArray tests
  IO.println "\n=== NDArray Tests ==="
  let ndtestResult ← IO.Process.output {
    cmd := "./.lake/build/bin/ndtest"
  }
  IO.print ndtestResult.stdout
  if ndtestResult.exitCode ≠ 0 then
    IO.eprintln ndtestResult.stderr
  
  return 0

script test_lean do
  IO.println "Building and running LeanArrayLib tests..."
  let buildResult ← IO.Process.output {
    cmd := "lake"
    args := #["build", "testexe"]
  }
  if buildResult.exitCode ≠ 0 then
    IO.eprintln s!"Build failed:\n{buildResult.stderr}"
    return buildResult.exitCode
    
  let result ← IO.Process.output {
    cmd := "./.lake/build/bin/testexe"
  }
  IO.print result.stdout
  if result.exitCode ≠ 0 then
    IO.eprintln result.stderr
  return result.exitCode

script test_nd do
  IO.println "Building and running NDArray tests..."
  let buildResult ← IO.Process.output {
    cmd := "lake"
    args := #["build", "ndtest"]
  }
  if buildResult.exitCode ≠ 0 then
    IO.eprintln s!"Build failed:\n{buildResult.stderr}"
    return buildResult.exitCode
    
  let result ← IO.Process.output {
    cmd := "./.lake/build/bin/ndtest"
  }
  IO.print result.stdout
  if result.exitCode ≠ 0 then
    IO.eprintln result.stderr
  return result.exitCode