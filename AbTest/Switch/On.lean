/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

meta import Ab.Syntax
meta import Ab.Print
meta import AbTest.Switch.Def
meta import Lean.Compiler.ImplementedByAttr

/-!
# The test switches in variants that the options set

`flag` is `true` and `impl` is `fastest`, for the whole module, as the `leanOptions` of a package
set them for every module of a library, and the sites follow them.
-/

-- Tests deliberately use concrete examples.
set_option linter.hazel false

set_option ab.flag true
set_option ab.impl "fastest"

open Lean

namespace AbTest.Switch.On

/-- The twin of `double`. -/
unsafe def doubleUnsafe (n : Nat) : Nat := n + n

/-- A definition with a twin in the `fast` variant only. -/
@[impl (variants := fast) implemented_by doubleUnsafe]
def double (n : Nat) : Nat := 2 * n

/-- A definition with a twin when `flag` is `true`. -/
@[flag implemented_by doubleUnsafe]
def double' (n : Nat) : Nat := 2 * n

run_cmd Elab.Command.liftCoreM do
  let ran ← IO.mkRef false
  ab%[AbTest.Switch.flag| true] ``double "test_registry" do ran.set true
  unless ← ran.get do throwError "not run with `flag` `true`"
  ab%[AbTest.Switch.impl] ``double' "test_match"
    | .fastest => pure ()
    | _ => throwError "`ab%[...]` does not run the branch of `fastest`"

run_meta do
  let env ← getEnv
  unless (Compiler.getImplementedBy? env ``double).isNone do
    throwError "the twin of `double` is attached"
  unless Compiler.getImplementedBy? env ``double' == some ``doubleUnsafe do
    throwError "the twin of `double'` is not attached"
  unless (AbTest.Switch.flag.sitesOf env ``double').all (·.activeIn true) do
    throwError "the site of `double'` is not active"

/--
info: [flag] Whether to use the fast paths of the tests.
  [variants] false (default), true (this build)
  [sites] 2/2 active
    [module] AbTest.Switch.On
      [test_registry] double
        [branch] ● #[true]
        [skip] ○ #[false]
        [payload]  (x1)
      [implemented_by] double'
        [branch] ● #[true]
        [skip] ○ #[false]
        [payload]  (x1)
[impl] Which implementation the tests run.
  [variants] reference, fast (default), fastest (this build)
  [sites] 1/2 active
    [module] AbTest.Switch.On
      [implemented_by] double
        [branch] ○ #[fast]
        [skip] ● #[reference, fastest]
      [test_match] double'
        [branch] ● #[fastest]
        [branch] ○ #[reference, fast]
-/
#guard_msgs in
#print ab

end AbTest.Switch.On
