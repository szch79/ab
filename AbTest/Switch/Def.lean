/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Declare
public meta import AbTest.Switch.Types
public import AbTest.Switch.Types

/-!
# The test switches

A switch over `Bool` whose sites carry a `Note`, and a switch among the three variants of `Impl`.
They exist in the modules that import this one.  Misdeclared switches are errors.
-/

namespace AbTest.Switch

/-- Whether to use the fast paths of the tests. -/
declare_ab_switch flag (payload := Note)

/-- Which implementation the tests run. -/
declare_ab_switch impl (variants := Impl) (default := fast)

/-- error: the name of a switch is atomic, since it is also the name of its attribute -/
#guard_msgs in
declare_ab_switch nested.flag

/-- error: `Note` is not an enumeration, since `Note.mk` has arguments -/
#guard_msgs in
declare_ab_switch notes (variants := Note)

/-- error: `slow` is not a variant of `slowImpl`; its variants are `reference`, `fast`, `fastest` -/
#guard_msgs in
declare_ab_switch slowImpl (variants := Impl) (default := slow)

end AbTest.Switch
