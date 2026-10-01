/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Declare
public meta import AbTest.Switch.Types
public import AbTest.Switch.Types

/-!
# The ordered test switches

A switch among the three variants of `Impl`, ordered from `reference` to `fastest`, and a switch
among those of `Diamond`, whose order is partial.  They exist in the modules that import this one.
An ordered switch over a type without a decidable `≤`, or whose `≤` is not a partial order, is an
error.
-/

namespace AbTest.Switch

/-- How fast an implementation the tests may run. -/
declare_ab_switch tier (variants := Impl) (default := fast) (ordered := true)

/-- Which corner of a diamond the tests run. -/
declare_ab_switch shape (variants := Diamond) (default := left) (ordered := true)

/-- A switch over `Tied` that is not ordered, so that its `≤` is not checked. -/
declare_ab_switch unordered (variants := Tied) (ordered := false)

/--
error: `(ordered := true)` orders the variants by an instance of `LE Ordering` whose `≤` is decidable, such as `leOfOrd` with `deriving Ord`:
  failed to synthesize instance of type class
    LE Ordering
  ⏎
  Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
declare_ab_switch ordering (variants := Ordering) (ordered := true)

/--
error: `≤` on `AbTest.Switch.Tied` is not a partial order: `left ≤ right` and `right ≤ left` hold for distinct variants
-/
#guard_msgs in
declare_ab_switch tied (variants := Tied) (ordered := true)

/-- error: `ordered` is `true` or `false` -/
#guard_msgs in
declare_ab_switch maybe (variants := Impl) (ordered := maybe)

end AbTest.Switch
