/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

meta import AbTest.Switch.Def

/-!
# A variant in which a site takes no effect

`impl` is `reference`, in which a site registered for the other variants takes no effect, while
`register` still returns `reference`.
-/

-- Tests deliberately use concrete examples.
set_option linter.hazel false

set_option ab.impl "reference"

open Lean

namespace AbTest.Switch.Reference

/-- A definition whose code a site chooses. -/
def double (n : Nat) : Nat := 2 * n

run_cmd Elab.Command.liftCoreM do
  let variant ←
    AbTest.Switch.impl.register ``double (.cont "test_register" #[#[.fast, .fastest]]) ()
  unless variant == .reference do throwError "`register` does not return `reference`"
  unless (AbTest.Switch.impl.sitesOf (← getEnv) ``double).all (!·.activeIn .reference) do
    throwError "the site takes effect in `reference`"

end AbTest.Switch.Reference
