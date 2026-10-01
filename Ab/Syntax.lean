/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Switch
public meta import Lean.Parser.Do
meta import Ab.Init

/-!
# The `ab%` syntax

The sites of a switch `sw` in meta code, on a constant `target` under a label:

* `ab%[sw| a, b] target "label" do k` records a site on `target` and runs `k` in the variants `a`
  and `b` only.  It expands to `Ab.Switch.whenIn`.  On an ordered switch, `ab%[sw| upset a, b]`
  names the variants above `a` or `b`, and `ab%[sw| downset a, b]` those below `a` or `b`.
* `ab%[sw] target "label"` followed by branches records a site on `target` and runs the branch of
  the variant of the build.  It expands to a `match` on the variant that `Ab.Switch.register`
  returns, and its right-hand sides are `do` sequences, so that a nested action runs in its own
  branch.
-/

public meta section

namespace Ab

open Lean

/--
How a site of an ordered switch names its variants: `upset` names those above some variants, and
`downset` those below some, both inclusive.
-/
syntax abBound := &"upset " <|> &"downset "

/--
`ab%[sw| a, b] target "label" do k` records a site of the switch `sw` on `target` under the label
`label`, which takes effect in the variants `a` and `b`, and runs `k` in those variants only.
On an ordered switch, `ab%[sw| upset a, b]` takes effect in the variants above `a` or `b`, and
`ab%[sw| downset a, b]` in those below `a` or `b`, both inclusive.  `(payload := p)` after the label
gives the payload of the site, which is `default` otherwise.
-/
syntax (name := abSite) "ab%[" ident "| " (abBound)? term,+ "]" ppSpace term:max ppSpace str
  (" (" &"payload" " := " term ")")? ppSpace "do" doSeq : term

/--
`ab%[sw] target "label"` followed by branches, as of a `match` on the variant of the build, records
a site of the switch `sw` on `target` under the label `label`, and runs the branch of that variant:

```
ab%[sw] target "label"
| .a | .b => ...
| _ => ...
```

The right-hand sides are `do` sequences, and the result is that of the branch that runs.  The site
records the variants in which each branch runs, `_` standing for those that the earlier patterns do
not match.  `(payload := p)` after the label gives the payload of the site, which is `default`
otherwise.
-/
syntax (name := abMatch) "ab%[" ident "]" ppSpace term:max ppSpace str
  (" (" &"payload" " := " term ")")? Parser.Term.doMatchAlts : term

macro_rules
  | `(ab%[$sw| $[$bound?:abBound]? $variants,*] $target $label
      $[(payload := $payload?)]? do $k) => do
    let payload ← payload?.getDM `(default)
    let some bound := bound? |
      `(Ab.Switch.whenIn $sw $target $label #[$variants,*] (do $k) $payload)
    -- Each alternative of `abBound` is a node around its atom.
    let set ← if bound.raw[0][0].getAtomVal == "upset" then
        `(Ab.Switch.upSet $sw #[$variants,*])
      else `(Ab.Switch.downSet $sw #[$variants,*])
    `((do Ab.Switch.whenIn $sw $target $label (← $set:term) (do $k) $payload))

macro_rules
  | `(ab%[$sw] $target $label $[(payload := $payload?)]? $alts:matchAlts) => do
    let payload ← payload?.getDM `(default)
    -- The variants that each alternative names, and whether it has `_`.
    let alts' ← alts.raw[0].getArgs.mapM fun alt => do
      let patterns := alt[1].getSepArgs.flatMap (·.getSepArgs)
      let variants : Array Term :=
        patterns.filter (!·.isOfKind ``Parser.Term.hole) |>.map (⟨·⟩)
      `((#[$variants,*], $(quote (decide (variants.size < patterns.size)))))
    `(do
      match ← Ab.Switch.register $sw $target
          (.cont $label (Ab.Switch.branchesOf $sw #[$alts',*])) $payload with
        $alts:matchAlts)

end Ab

end -- public meta section
