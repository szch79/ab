/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

meta import Ab.Syntax
meta import Ab.Print
meta import AbTest.Switch.Def
meta import AbTest.Switch.OrderedDef
meta import Lean.Compiler.ImplementedByAttr

/-!
# Ordered switches

`tier` is `fast` and `shape` is `left`.  The sites name the variants above some by `upset` and those
below some by `downset`, in the attribute and in `ab%`, and the report names them back the same way.
A site whose variants are neither an up-set nor a down-set is an error, whatever form names them,
and so are `upset` and `downset` on a switch that is not ordered.
-/

-- Tests deliberately use concrete examples.
set_option linter.hazel false

open Lean

namespace AbTest.Switch.Ordered

/-- The twin of `double`. -/
unsafe def doubleUnsafe (n : Nat) : Nat := n + n

/-- A definition with a twin from `fast` up. -/
@[tier (upset := fast) implemented_by doubleUnsafe]
def double (n : Nat) : Nat := 2 * n

/-- A definition with a twin up to `reference`. -/
@[tier (downset := reference) implemented_by doubleUnsafe]
def double' (n : Nat) : Nat := 2 * n

/-- A definition with a twin in variants that are listed, and are an up-set. -/
@[tier (variants := fast, fastest) implemented_by doubleUnsafe]
def doubleListed (n : Nat) : Nat := 2 * n

/-- A definition with a twin from `left` or `right` up. -/
@[shape (upset := left, right) implemented_by doubleUnsafe]
def doubleCorners (n : Nat) : Nat := 2 * n

/-- A definition with a twin up to `right`. -/
@[shape (downset := right) implemented_by doubleUnsafe]
def doubleRight (n : Nat) : Nat := 2 * n

run_meta do
  let env ← getEnv
  for decl in [``double, ``doubleListed, ``doubleCorners] do
    unless Compiler.getImplementedBy? env decl == some ``doubleUnsafe do
      throwError "the twin of `{decl}` is not attached"
  for decl in [``double', ``doubleRight] do
    unless (Compiler.getImplementedBy? env decl).isNone do
      throwError "the twin of `{decl}` is attached"

run_cmd Elab.Command.liftCoreM do
  let ran ← IO.mkRef false
  ab%[AbTest.Switch.tier| upset .fast] ``double "test_upset" do ran.set true
  unless ← ran.get do throwError "not run from `fast` up"
  ab%[AbTest.Switch.tier| downset .reference] ``double "test_downset" do throwError "run in `fast`"
  ab%[AbTest.Switch.shape| downset .left, .right] ``double "test_downset" do pure ()
  -- A `match` site is not checked, since its branches cover every variant.
  ab%[AbTest.Switch.tier] ``double "test_match"
    | .fast => pure ()
    | _ => throwError "`ab%[...]` does not run the branch of `fast`"

/--
error: the site `@[implemented_by]` on `AbTest.Switch.Ordered.doubleGap` takes effect in `reference` but not in `fast` above it, and in `fastest` but not in `fast` below it; a site of the ordered switch `tier` takes effect in an `upset` or a `downset` of its variants
-/
#guard_msgs in
@[tier (variants := reference, fastest) implemented_by doubleUnsafe]
def doubleGap (n : Nat) : Nat := 2 * n

/--
error: the site `@[implemented_by]` on `AbTest.Switch.Ordered.doubleLeft` takes effect in `left` but not in `top` above it, and in `left` but not in `bottom` below it; a site of the ordered switch `shape` takes effect in an `upset` or a `downset` of its variants
-/
#guard_msgs in
@[shape (variants := left) implemented_by doubleUnsafe]
def doubleLeft (n : Nat) : Nat := 2 * n

/--
error: `impl` is not ordered, so `upset` cannot name its variants; declare it with `(ordered := true)`
-/
#guard_msgs in
@[impl (upset := fast) implemented_by doubleUnsafe]
def doubleUnordered (n : Nat) : Nat := 2 * n

/--
error: the site `test_gap` on `AbTest.Switch.Ordered.double` takes effect in `reference` but not in `fast` above it, and in `fastest` but not in `fast` below it; a site of the ordered switch `tier` takes effect in an `upset` or a `downset` of its variants
-/
#guard_msgs in
run_cmd Elab.Command.liftCoreM do
  ab%[AbTest.Switch.tier| .reference, .fastest] ``double "test_gap" do pure ()

/--
error: `flag` is not ordered, so `downset` cannot name its variants; declare it with `(ordered := true)`
-/
#guard_msgs in
run_cmd Elab.Command.liftCoreM do
  ab%[AbTest.Switch.flag| downset true] ``double "test_unordered" do pure ()

/--
info: [tier] How fast an implementation the tests may run.
  [variants] reference, fast (default, this build), fastest
  [sites] 4/6 active
    [module] AbTest.Switch.Ordered
      [implemented_by] double
        [branch] ● upset #[fast]
        [skip] ○ downset #[reference]
      [test_upset] double
        [branch] ● upset #[fast]
        [skip] ○ downset #[reference]
      [test_downset] double
        [branch] ○ downset #[reference]
        [skip] ● upset #[fast]
      [test_match] double
        [branch] ● #[fast]
        [branch] ○ #[reference, fastest]
      [implemented_by] double'
        [branch] ○ downset #[reference]
        [skip] ● upset #[fast]
      [implemented_by] doubleListed
        [branch] ● upset #[fast]
        [skip] ○ downset #[reference]
-/
#guard_msgs in
#print ab tier

/--
info: [shape] Which corner of a diamond the tests run.
  [variants] bottom, left (default, this build), right, top
  [sites] 2/3 active
    [module] AbTest.Switch.Ordered
      [test_downset] double
        [branch] ● downset #[left, right]
        [skip] ○ upset #[top]
      [implemented_by] doubleCorners
        [branch] ● upset #[left, right]
        [skip] ○ downset #[bottom]
      [implemented_by] doubleRight
        [branch] ○ downset #[right]
        [skip] ● upset #[left]
-/
#guard_msgs in
#print ab shape

end AbTest.Switch.Ordered
