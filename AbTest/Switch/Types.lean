/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public import Lean.Message

/-!
# The types of the test switches

The variant type and the payload type of the switches of `AbTest.Switch.Def`, which that module
imports at both phases, since a switch uses them at the meta phase and the code that it chooses
between at run time.
-/

namespace AbTest.Switch

/-- The variants of a switch among three implementations. -/
public inductive Impl where
  /-- The reference implementation. -/
  | reference
  /-- A faster one. -/
  | fast
  /-- The fastest one. -/
  | fastest
deriving BEq, Inhabited, Ord

/-- The implementations from the reference one to the fastest one, for an ordered switch. -/
public instance : LE Impl := leOfOrd

/--
The variants of a switch ordered as a diamond: `bottom` is below `left` and `right`, which are
below `top` and not comparable.
-/
public inductive Diamond where
  /-- The least variant. -/
  | bottom
  /-- A variant that `right` is not comparable with. -/
  | left
  /-- A variant that `left` is not comparable with. -/
  | right
  /-- The greatest variant. -/
  | top
deriving BEq, Inhabited

/-- The order of `Diamond`. -/
public def Diamond.le : Diamond → Diamond → Bool
  | .bottom, _ | _, .top | .left, .left | .right, .right => true
  | _, _ => false

public instance : LE Diamond := ⟨fun a b => a.le b⟩

public instance : DecidableRel (α := Diamond) (· ≤ ·) := fun a b =>
  inferInstanceAs (Decidable (a.le b))

/-- The variants of a switch whose `≤` holds everywhere, which is not a partial order. -/
public inductive Tied where
  /-- One variant. -/
  | left
  /-- The other variant. -/
  | right
deriving BEq, Inhabited

public instance : LE Tied := ⟨fun _ _ => True⟩

public instance : DecidableRel (α := Tied) (· ≤ ·) := fun _ _ => instDecidableTrue

/-- The payload of a test switch. -/
public structure Note where
  /-- The text of the note. -/
  text : String
  /-- How much faster the site is expected to be. -/
  speedup : Nat := 1
deriving Inhabited

public instance : ToString Note where
  toString note := s!"{note.text} (x{note.speedup})"

end AbTest.Switch
