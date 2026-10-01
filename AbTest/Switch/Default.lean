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
# The test switches in their default variants

`flag` is `false` and `impl` is `fast`.  The forms of a site are recorded with their payloads, the
attribute is applied and the continuations run in the variants of their sites only, the branch of
the variant runs, and the misuses of the attribute are errors.  The report shows every shape of a
site: one branch and a skip, one branch for every variant, a branch for each variant, branches of
a `Bool` switch, and several branches and a skip.
-/

-- Tests deliberately use concrete examples.
set_option linter.hazel false

open Lean

namespace AbTest.Switch.Default

/-- The twin of `double`. -/
unsafe def doubleUnsafe (n : Nat) : Nat := n + n

/-- A definition with a twin in the `fast` and `fastest` variants. -/
@[impl (variants := fast, fastest) implemented_by doubleUnsafe]
def double (n : Nat) : Nat := 2 * n

/-- A definition with a twin when `flag` is `true`, which it is not. -/
@[flag (payload := { text := "shift", speedup := 2 }) implemented_by doubleUnsafe]
def double' (n : Nat) : Nat := 2 * n

run_cmd Elab.Command.liftCoreM do
  AbTest.Switch.flag.whenIn ``double "test_registry" #[true] (payload := { text := "registry" })
    (throwError "run with `flag` `false`")
  AbTest.Switch.impl.whenIn ``double "test_registry" #[.fastest] (throwError "run in `fast`")
  let variant ←
    AbTest.Switch.impl.register ``double' (.cont "test_register" #[#[.fast, .fastest]]) ()
  unless variant == .fast do throwError "`register` does not return `fast`"

-- The syntax records the same sites as the functions.
run_cmd Elab.Command.liftCoreM do
  ab%[AbTest.Switch.flag| true] ``double "test_syntax" (payload := { text := "syntax" }) do
    throwError "run with `flag` `false`"
  ab%[AbTest.Switch.impl| .fast, .fastest] ``double' "test_syntax" do pure ()
  let ran ← ab%[AbTest.Switch.impl] ``double' "test_match"
    | .fast =>
      let result := true
      pure result
    | _ => throwError "`ab%[...]` does not run the branch of `fast`"
  unless ran do throwError "`ab%[...]` does not return the result of its branch"

/-- A definition with a twin in every variant of `impl`, so that its site skips none. -/
@[impl (variants := reference, fast, fastest) implemented_by doubleUnsafe]
def doubleEverywhere (n : Nat) : Nat := 2 * n

-- Sites that skip no variant, a branch for each variant, branches of a `Bool` switch with a
-- payload, and several branches that leave a variant to skip.
run_cmd Elab.Command.liftCoreM do
  let ran ← IO.mkRef false
  ab%[AbTest.Switch.impl| .reference, .fast, .fastest] ``doubleEverywhere "test_every" do
    ran.set true
  unless ← ran.get do throwError "not run in every variant"
  ab%[AbTest.Switch.impl] ``doubleEverywhere "test_each"
    | .reference => throwError "run in `reference`"
    | .fast => pure ()
    | .fastest => throwError "run in `fastest`"
  ab%[AbTest.Switch.flag] ``doubleEverywhere "test_bool" (payload := { text := "bool" })
    | true => throwError "run with `flag` `true`"
    | false => pure ()
  discard <| AbTest.Switch.impl.register ``doubleEverywhere
    (.cont "test_partial" #[#[.reference], #[.fastest]]) ()

/--
info: [flag] Whether to use the fast paths of the tests.
  [variants] false (default, this build), true
  [sites] 1/4 active
    [module] AbTest.Switch.Default
      [test_registry] double
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] registry (x1)
      [test_syntax] double
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] syntax (x1)
      [implemented_by] double'
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] shift (x2)
      [test_bool] doubleEverywhere
        [branch] ○ #[true]
        [branch] ● #[false]
        [payload] bool (x1)
[impl] Which implementation the tests run.
  [variants] reference, fast (default, this build), fastest
  [sites] 7/9 active
    [module] AbTest.Switch.Default
      [implemented_by] double
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_registry] double
        [branch] ○ #[fastest]
        [skip] ● #[reference, fast]
      [test_register] double'
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_syntax] double'
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_match] double'
        [branch] ● #[fast]
        [branch] ○ #[reference, fastest]
      [implemented_by] doubleEverywhere
        [branch] ● #[reference, fast, fastest]
      [test_every] doubleEverywhere
        [branch] ● #[reference, fast, fastest]
      [test_each] doubleEverywhere
        [branch] ○ #[reference]
        [branch] ● #[fast]
        [branch] ○ #[fastest]
      [test_partial] doubleEverywhere
        [branch] ○ #[reference]
        [branch] ○ #[fastest]
        [skip] ● #[fast]
-/
#guard_msgs in
#print ab

/--
info: [flag] Whether to use the fast paths of the tests.
  [variants] false (default, this build), true
  [sites] 1/4 active
    [module] AbTest.Switch.Default
      [test_registry] double
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] registry (x1)
      [test_syntax] double
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] syntax (x1)
      [implemented_by] double'
        [branch] ○ #[true]
        [skip] ● #[false]
        [payload] shift (x2)
      [test_bool] doubleEverywhere
        [branch] ○ #[true]
        [branch] ● #[false]
        [payload] bool (x1)
-/
#guard_msgs in
#print ab flag

/--
info: [impl] Which implementation the tests run.
  [variants] reference, fast (default, this build), fastest
  [sites] 7/9 active
    [module] AbTest.Switch.Default
      [implemented_by] double
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_registry] double
        [branch] ○ #[fastest]
        [skip] ● #[reference, fast]
      [test_register] double'
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_syntax] double'
        [branch] ● #[fast, fastest]
        [skip] ○ #[reference]
      [test_match] double'
        [branch] ● #[fast]
        [branch] ○ #[reference, fastest]
      [implemented_by] doubleEverywhere
        [branch] ● #[reference, fast, fastest]
      [test_every] doubleEverywhere
        [branch] ● #[reference, fast, fastest]
      [test_each] doubleEverywhere
        [branch] ○ #[reference]
        [branch] ● #[fast]
        [branch] ○ #[fastest]
      [test_partial] doubleEverywhere
        [branch] ○ #[reference]
        [branch] ○ #[fastest]
        [skip] ● #[fast]
-/
#guard_msgs in
#print ab impl

/--
error: `impl` is not over `Bool`, so name the variants in which it applies the attribute, as in `@[impl (variants := reference) attr]`
-/
#guard_msgs in
@[impl implemented_by doubleUnsafe]
def noVariants (n : Nat) : Nat := n

/-- error: `slow` is not a variant of `impl` -/
#guard_msgs in
@[impl (variants := slow) implemented_by doubleUnsafe]
def unknownVariant (n : Nat) : Nat := n

/-- error: `impl` takes no payload -/
#guard_msgs in
@[impl (variants := fast) (payload := 1) implemented_by doubleUnsafe]
def noPayload (n : Nat) : Nat := n

/--
error: `ab.impl` is set to `slow`, which is not a variant of `impl`; its variants are `reference`, `fast`, `fastest`
-/
#guard_msgs in
set_option ab.impl "slow" in
run_meta discard AbTest.Switch.impl.variant

/--
error: `nothing` is not a switch of the imported modules; the switches are `flag`, `impl`
-/
#guard_msgs in
#print ab nothing

end AbTest.Switch.Default
