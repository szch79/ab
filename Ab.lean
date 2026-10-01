/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Declare
public meta import Ab.Print
public meta import Ab.Syntax

/-!
# Ab

Ab marks the places in Lean code whose compiled code a build can choose between, records every
such place, and reports them.

A switch is a choice that the build of a library makes among the variants of the switch, the
constructors of `Bool` or of another enumeration, set by the option `ab.<name>`.  A site is a place
where the variants differ, with a payload of the user's type:

* `Ab.Switch` holds the switches and their sites, and the variant of the build, a setting of the
  build of every library that the modules importing a library follow, with the functions that
  record a site, `Ab.Switch.register` and `Ab.Switch.whenIn`.
* `Ab.Syntax` holds the `ab%` syntax for meta code.  `ab%[sw| a, b] target "label" do k` runs `k`
  in the variants `a` and `b` only, and `ab%[sw] target "label"` followed by branches, as of a
  `match`, runs the branch of the variant of the build.
* `declare_ab_switch name` declares a switch, its option and its attribute, in `Ab.Declare`, and
  `@[name attr]` applies the attribute `attr` in some variants only.
* An ordered switch, declared with `(ordered := true)`, orders its variants by `≤`, and each of
  its sites takes effect in the variants above some, which `upset` names, or in those below some,
  which `downset` names.
* Every form records the site in every variant, with the variants of each of its branches and
  where it is written.
* `#print ab` lists the switches with their sites, and `#print ab name` one switch, in `Ab.Print`.
-/
