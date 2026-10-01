/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

meta import Ab.Print
meta import AbTest.Switch.Def
import AbTest.Switch.Default
import AbTest.Switch.Reference

/-!
# Imports compiled in different variants of a switch

`AbTest.Switch.Default` and `AbTest.Switch.Reference` were compiled in different variants of `impl`,
so asking for its variant is an error, and the report of its sites, by module, marks no branch,
while `flag`, which only the first of them recorded, is independent of it.
-/

-- Tests deliberately use concrete examples.
set_option linter.hazel false

/--
error: `AbTest.Switch.Default` was compiled with `ab.impl=fast` and `AbTest.Switch.Reference` with `ab.impl=reference`, so their code cannot be combined; build every library with the same value of `ab.impl`
-/
#guard_msgs in
run_meta discard AbTest.Switch.impl.variant

run_meta do
  if ← AbTest.Switch.flag.variant then throwError "`flag` is `true`"

/--
info: [impl] Which implementation the tests run.
  [variants] reference, fast (default), fastest
  [build] `AbTest.Switch.Default` was compiled with `ab.impl=fast` and `AbTest.Switch.Reference` with `ab.impl=reference`, so their code cannot be combined; build every library with the same value of `ab.impl`
  [sites] 10
    [module] AbTest.Switch.Default
      [implemented_by] AbTest.Switch.Default.double
        [branch] #[fast, fastest]
        [skip] #[reference]
      [test_registry] AbTest.Switch.Default.double
        [branch] #[fastest]
        [skip] #[reference, fast]
      [test_register] AbTest.Switch.Default.double'
        [branch] #[fast, fastest]
        [skip] #[reference]
      [test_syntax] AbTest.Switch.Default.double'
        [branch] #[fast, fastest]
        [skip] #[reference]
      [test_match] AbTest.Switch.Default.double'
        [branch] #[fast]
        [branch] #[reference, fastest]
      [implemented_by] AbTest.Switch.Default.doubleEverywhere
        [branch] #[reference, fast, fastest]
      [test_every] AbTest.Switch.Default.doubleEverywhere
        [branch] #[reference, fast, fastest]
      [test_each] AbTest.Switch.Default.doubleEverywhere
        [branch] #[reference]
        [branch] #[fast]
        [branch] #[fastest]
      [test_partial] AbTest.Switch.Default.doubleEverywhere
        [branch] #[reference]
        [branch] #[fastest]
        [skip] #[fast]
    [module] AbTest.Switch.Reference
      [test_register] AbTest.Switch.Reference.double
        [branch] #[fast, fastest]
        [skip] #[reference]
-/
#guard_msgs in
#print ab impl
