import Lake

open Lake DSL

require hazel from git "https://github.com/szch79/hazel.git" @ "v4.35.0-rc2"

abbrev linters : Array LeanOption := #[
  ⟨`linter.hazel, true⟩,
  ⟨`linter.hazel.docstring.missingDocstring, false⟩,
  ⟨`linter.hazel.style.redundantImplicitLevel, .ofNat 2⟩
]

package ab where
  version := v!"0.1.0"
  leanOptions := linters.map fun s => { s with name := `weak ++ s.name }

@[default_target]
lean_lib Ab

lean_lib AbTest where
  globs := #[.submodules `AbTest]

@[lint_driver]
script lint args do
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "Ab"] ++ args.toArray
  }
  return ← child.wait

@[test_driver]
script test _args do
  let child ← IO.Process.spawn { cmd := "lake", args := #["build", "Ab", "AbTest", "--wfail"] }
  return ← child.wait
