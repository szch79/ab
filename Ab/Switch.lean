/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Lean.CoreM
public meta import Lean.Elab.DeclarationRange
public meta import Lean.EnvExtension
public meta import Lean.Message
meta import Ab.Init

/-!
# Switches

A switch is a choice that the build of a library makes among the variants of the switch, the values
of its variant type, such as whether to attach the code that the kernel does not check, or which of
several implementations a program runs.  A site is a place where the variants differ: an attribute
that Ab applies in some variants only, or a continuation of the caller with a branch for some
variants.  Every build records every site, with the variants of each of its branches, where it is
written and a payload of the user, so that a report in any variant shows what the other variants
change.

The variants of an ordered switch carry an order, and each of its sites takes effect in an up-set
or a down-set of it, which `upset` and `downset` name by their bounds.

This module holds the types and the registry of the switches that the loaded modules declare, the
order of an ordered switch, the variant of the build, and the functions that register a site.
-/

public meta section

namespace Ab

open Lean

/-- The names `names`, in code. -/
def codeList (names : Array String) : MessageData :=
  .joinSep (names.toList.map fun name => m!"`{name}`") ", "

/-- What a site of a switch is, with the variants of type `ρ` in which each branch of it runs. -/
inductive SiteKind (ρ : Type) where
  /-- The attribute `name`, which Ab applies in the variants `variants` only. -/
  | attr (name : Name) (variants : Array ρ)
  /--
  A continuation of the caller under the label `label`, whose branches run in the variants
  `branches` only, while nothing runs in the others.
  -/
  | cont (label : String) (branches : Array (Array ρ))
deriving BEq, Inhabited

namespace SiteKind

/-- The variants in which each branch of the site runs, a single one for an attribute. -/
def branches : SiteKind ρ → Array (Array ρ)
  | .attr _ variants => #[variants]
  | .cont _ branches => branches

/-- The kind with each of its variants mapped by `f`. -/
def map (f : ρ → σ) : SiteKind ρ → SiteKind σ
  | .attr name variants => .attr name (variants.map f)
  | .cont label branches => .cont label (branches.map (·.map f))

/-- The kind, as the reports name it, without its variants. -/
def toMessageData : SiteKind ρ → MessageData
  | .attr name _ => m!"`@[{name}]`"
  | .cont label _ => m!"`{label}`"

instance : ToMessageData (SiteKind ρ) := ⟨toMessageData⟩

end SiteKind

/-- A site of a switch with the variant type `ρ` and the payload type `α`. -/
structure SwitchSite (ρ α : Type) where
  /-- The constant that the site is attached to, under which a walk of the code finds it. -/
  target : Name
  /-- What the site is, with the variants in which it takes effect. -/
  kind : SiteKind ρ
  /-- The module where the site is written, not necessarily the one that declares `target`. -/
  module : Name
  /-- Where the site is written in `module`, when its syntax has a position. -/
  range? : Option DeclarationRange
  /-- The data that the user gives with the site. -/
  payload : α
deriving Inhabited

/-- Whether a branch of the site runs in the variant `variant`. -/
def SwitchSite.activeIn [BEq ρ] (site : SwitchSite ρ α) (variant : ρ) : Bool :=
  site.kind.branches.any (·.contains variant)

/-- Adds the site `site` to the sites `m`, under its target. -/
def insertSite (m : NameMap (Array (SwitchSite ρ α))) (site : SwitchSite ρ α) :
    NameMap (Array (SwitchSite ρ α)) :=
  m.alter site.target fun sites? => (sites?.getD #[]).push site

/--
The constant `target` of a site written in `module` at `range?`.  Go to Definition on it opens the
site, when its range is known, rather than the declaration of `target`.  It hovers as `target` when
the environment of the message has it, and as its name otherwise.
-/
def ofSiteTarget (target module : Name) (range? : Option DeclarationRange) : MessageData :=
  -- The importers of a module do not have its private constants, whose sites they still report,
  -- since they run their compiled code.  So the name, the location and the docstring come from the
  -- site, and only the type in the hover from the environment.
  let name := (privateToUserName? target).getD target
  .ofLazy (fun ctx? => Dynamic.mk <$> do
      let some ctx := ctx? | return MessageData.ofName name
      let info? := ctx.env.find? target
      let some range := range? |
        return if info?.isSome then MessageData.ofConstName target else .ofName name
      let location : Option DeclarationLocation := some { module, range }
      let site := s!"A site at line {range.pos.line} of `{module}`"
      match info? with
      | some info =>
        -- The infos of the name are dropped, so that the hover with the location covers all of it.
        let fmt := (← ppConstNameWithInfos ctx target).fmt
        return .withExprHover fmt (.const target (info.levelParams.map mkLevelParam)) ctx.lctx
          (location? := location) (docString? := s!"{site}.")
      | none =>
        return .withExprHover (format name) (toExpr name) ctx.lctx (location? := location)
          (docString? := s!"{site}, on a constant that is not visible here, such as a private one \
            of another module, so only its name is known."))
    (fun _ => false)

/-- The target of the site, which Go to Definition on it opens when its range is known. -/
def SwitchSite.targetMessage (site : SwitchSite ρ α) : MessageData :=
  ofSiteTarget site.target site.module site.range?

/-- What every switch has, whatever its types. -/
structure SwitchInfo where
  /-- The name of the switch, which is also the name of its attribute. -/
  name : Name
  /-- What the switch chooses. -/
  descr : String
  /-- The option that sets the variant, `ab.<name>`. -/
  optionName : Name
  /-- The variant type, whose constructors are the variants. -/
  variantType : Name
  /-- The names of the variants, in the order of the variant type. -/
  variantNames : Array String
  /-- The variant of a build that does not set the option. -/
  default : String
  /-- Whether the variant type is `Bool`, whose option is a `Bool` rather than a string. -/
  isBool : Bool
  /-- The order of the variants, on their names, when the switch is ordered. -/
  le? : Option (String → String → Bool) := none
  /-- The declaration of the switch. -/
  ref : Name
deriving Inhabited

/--
The variants of each branch of a `match` on the variant whose alternatives match the variants
`alts`, every variant for the alternative `_`: a variant goes to the first branch that matches it.
-/
def SwitchInfo.branchesOf (info : SwitchInfo) (alts : Array (Array String × Bool)) :
    Array (Array String) :=
  (alts.foldl (init := (#[], #[])) fun (branches, matched) (variants, rest) =>
    let branch := (if rest then info.variantNames else variants).filter (!matched.contains ·)
    (branches.push branch, matched ++ branch)).1

/-- The setting of the option that selects the variant `variant`, as `-D` takes it. -/
def SwitchInfo.setting (info : SwitchInfo) (variant : String) : String :=
  s!"{info.optionName}={variant}"

/-!
### Ordered switches

The variants of an ordered switch carry an order, such as how much a build trusts, and a site
takes effect in every variant above one where it does, or in every variant below one.  So the
variants of a site are an up-set of the order, which `upset a, b` names by its minimal elements, or
a down-set, which `downset a, b` names by its maximal elements.
-/

/-- The elements of `all` that are above one of `gens` in the order `le`, in the order of `all`. -/
def upSetOf (le : σ → σ → Bool) (all gens : Array σ) : Array σ :=
  all.filter fun b => gens.any (le · b)

/-- The elements of `all` that are below one of `gens` in the order `le`, in the order of `all`. -/
def downSetOf (le : σ → σ → Bool) (all gens : Array σ) : Array σ :=
  all.filter fun b => gens.any (le b ·)

/--
An element of `set` and one of `all` above it in the order `le` that is not in `set`, the first
such pair, and none when `set` is an up-set of `all`.
-/
def upGap? [BEq σ] (le : σ → σ → Bool) (all set : Array σ) : Option (σ × σ) :=
  set.findSome? fun a => (all.find? fun b => le a b && !set.contains b).map (a, ·)

/--
An element of `set` and one of `all` below it in the order `le` that is not in `set`, the first
such pair, and none when `set` is a down-set of `all`.
-/
def downGap? [BEq σ] (le : σ → σ → Bool) (all set : Array σ) : Option (σ × σ) :=
  upGap? (fun a b => le b a) all set

/-- The minimal elements of `set` in the order `le`, which generate it when it is an up-set. -/
def minimalOf [BEq σ] (le : σ → σ → Bool) (set : Array σ) : Array σ :=
  set.filter fun a => !set.any fun b => b != a && le b a

/-- The maximal elements of `set` in the order `le`, which generate it when it is a down-set. -/
def maximalOf [BEq σ] (le : σ → σ → Bool) (set : Array σ) : Array σ :=
  minimalOf (fun a b => le b a) set

/-- The order of the switch, and an error naming the gadget `gadget` when it is not ordered. -/
def SwitchInfo.order [Monad m] [MonadError m] (info : SwitchInfo) (gadget : String) :
    m (String → String → Bool) := do
  let some le := info.le? |
    throwError m!"`{info.name}` is not ordered, so `{gadget}` cannot name its variants; declare it \
      with `(ordered := true)`"
  return le

/-- The variants above one of `gens`, which `upset` names, and an error when it is not ordered. -/
def SwitchInfo.upSet [Monad m] [MonadError m] (info : SwitchInfo) (gens : Array String) :
    m (Array String) :=
  return upSetOf (← info.order "upset") info.variantNames gens

/-- The variants below one of `gens`, which `downset` names, and an error when it is not ordered. -/
def SwitchInfo.downSet [Monad m] [MonadError m] (info : SwitchInfo) (gens : Array String) :
    m (Array String) :=
  return downSetOf (← info.order "downset") info.variantNames gens

/--
Checks that the site `kind` on `target` of an ordered switch takes effect in an up-set or a
down-set of the order.  Every site of a switch that is not ordered passes.
-/
def SwitchInfo.checkSite [Monad m] [MonadError m] (info : SwitchInfo) (target : Name)
    (kind : SiteKind String) : m Unit := do
  let some le := info.le? | return
  let set := info.variantNames.filter fun variant => kind.branches.any (·.contains variant)
  let some (a, b) := upGap? le info.variantNames set | return
  let some (c, d) := downGap? le info.variantNames set | return
  let target := (privateToUserName? target).getD target
  throwError m!"the site {kind} on `{target}` takes effect in `{a}` but not in `{b}` above it, and \
    in `{c}` but not in `{d}` below it; a site of the ordered switch `{info.name}` takes effect in \
    an `upset` or a `downset` of its variants"

/-- A switch with the variant type `ρ` and the payload type `α`. -/
structure Switch (ρ α : Type) extends SwitchInfo where
  /-- The name of a variant. -/
  nameOf : ρ → String
  /-- The variant of a name. -/
  ofName? : String → Option ρ
  /-- The sites recorded by the imported modules and by the current one, by target. -/
  ext : SimplePersistentEnvExtension (SwitchSite ρ α) (NameMap (Array (SwitchSite ρ α)))

instance : Inhabited (Switch ρ α) :=
  ⟨{ toSwitchInfo := default, nameOf := fun _ => "", ofName? := fun _ => none, ext := default }⟩

/-- The variants of each branch of a `match` on the variant, as `SwitchInfo.branchesOf`. -/
def Switch.branchesOf (sw : Switch ρ α) (alts : Array (Array ρ × Bool)) : Array (Array ρ) :=
  (sw.toSwitchInfo.branchesOf (alts.map fun (variants, rest) => (variants.map sw.nameOf, rest))).map
    (·.filterMap sw.ofName?)

/-- Whether the variant `variant` is one of `variants`. -/
def Switch.isIn (sw : Switch ρ α) (variants : Array ρ) (variant : ρ) : Bool :=
  variants.any (sw.nameOf · == sw.nameOf variant)

/-- The variants of the switch, in the order of the variant type. -/
def Switch.variants (sw : Switch ρ α) : Array ρ :=
  sw.variantNames.filterMap sw.ofName?

/-- The variants above one of `gens`, which `upset` names, and an error when it is not ordered. -/
def Switch.upSet [Monad m] [MonadError m] (sw : Switch ρ α) (gens : Array ρ) : m (Array ρ) :=
  return (← sw.toSwitchInfo.upSet (gens.map sw.nameOf)).filterMap sw.ofName?

/-- The variants below one of `gens`, which `downset` names, and an error when it is not ordered. -/
def Switch.downSet [Monad m] [MonadError m] (sw : Switch ρ α) (gens : Array ρ) : m (Array ρ) :=
  return (← sw.toSwitchInfo.downSet (gens.map sw.nameOf)).filterMap sw.ofName?

/-- The sites of the switch attached to `target`. -/
def Switch.sitesOf (sw : Switch ρ α) (env : Environment) (target : Name) :
    Array (SwitchSite ρ α) :=
  (sw.ext.getState env).getD target #[]

/-- The sites of the switch. -/
def Switch.sites (sw : Switch ρ α) (env : Environment) : Array (SwitchSite ρ α) :=
  (sw.ext.getState env).foldl (init := #[]) fun acc _ sites => acc ++ sites

/-- A switch as the generic reports read it, with its variants named and its payloads rendered. -/
structure SwitchEntry extends SwitchInfo where
  /-- The sites of the switch. -/
  sites : Environment → Array (SwitchSite String (Option MessageData))

/-- The switches that the loaded modules declare, in the order they were registered. -/
initialize switchesRef : IO.Ref (Array SwitchEntry) ← IO.mkRef #[]

/-- The switches that the loaded modules declare. -/
def switches : IO (Array SwitchEntry) :=
  switchesRef.get

end Ab

end -- public meta section

/-!
## The variant of a build

A site takes effect, or not, when its module is compiled, so the variant of a switch is a setting of
the build of every library rather than of a single file.  Each module whose code depends on the
variant of a switch records the variant it was compiled in, the first time it asks for it, and the
modules that import it follow the recorded variant.  Modules compiled in different variants of a
switch cannot be combined, and setting the option against the recorded variant is an error.
Different switches are independent.
-/

meta section

namespace Ab

open Lean

/-- The variant of a switch that a module was compiled in. -/
structure VariantRecord where
  /-- The switch. -/
  switch : Name
  /-- The module. -/
  module : Name
  /-- The name of the variant. -/
  variant : String
deriving Inhabited

/--
The variants of a switch recorded by the imported modules and by the current one.  It keeps a module
of each variant rather than the variant alone, since imports compiled in different variants are only
reported when the variant is asked for, and the report names a module of each.
-/
structure VariantState where
  /-- Each recorded variant, with the first module recorded in it. -/
  built : Array (String × Name) := #[]
  /-- Whether the current module has recorded its variant. -/
  recorded : Bool := false
deriving Inhabited

/-- Adds the record `r` to the state `s`. -/
def VariantState.add (s : VariantState) (r : VariantRecord) : VariantState :=
  if s.built.any (·.1 == r.variant) then s
  else { s with built := s.built.push (r.variant, r.module) }

/-- Adds the record `r` to the states `m`, under its switch. -/
def addVariantRecord (m : NameMap VariantState) (r : VariantRecord) : NameMap VariantState :=
  m.insert r.switch ((m.getD r.switch {}).add r)

/-- The variants that the modules were compiled in, by switch. -/
initialize variantExt : SimplePersistentEnvExtension VariantRecord (NameMap VariantState) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m r => (addVariantRecord m r).modify r.switch ({ · with recorded := true })
    addImportedFn := fun ess => ess.foldl (init := {}) fun m es => es.foldl addVariantRecord m
    asyncMode := .sync
  }

/-- The variant that the option of the switch sets, if it is set, and an error if it names none. -/
def SwitchInfo.optionVariant? [Monad m] [MonadOptions m] [MonadError m] (info : SwitchInfo) :
    m (Option String) := do
  let some value := (← getOptions).find? info.optionName | return none
  let variant := match value with
    | .ofBool b => toString b
    | .ofString s => s
    | v => toString v
  unless info.variantNames.contains variant do
    throwError m!"`{info.optionName}` is set to `{variant}`, which is not a variant of \
      `{info.name}`; its variants are \
      {codeList info.variantNames}"
  return some variant

/--
The variant of the switch in this build, which the current module records when `record` holds.  It
is the variant that the imported modules were compiled in, or, when none of them recorded one, the
variant that the option sets, or the default.  Imports compiled in different variants, and the
option set against the recorded variant, are errors, since the compiled code of those modules cannot
follow.
-/
public def SwitchInfo.currentVariant [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (info : SwitchInfo) (record := true) : m String := do
  let s := (variantExt.getState (← getEnv)).getD info.name {}
  let built? ← match s.built.toList with
    | [] => pure none
    | [b] => pure (some b)
    | (variant₁, module₁) :: (variant₂, module₂) :: _ =>
      throwError m!"`{module₁}` was compiled with `{info.setting variant₁}` and `{module₂}` \
        with `{info.setting variant₂}`, so their code cannot be combined; build every library \
        with the same value of `{info.optionName}`"
  let set? ← info.optionVariant?
  if let (some (variant, module), some set) := (built?, set?) then
    if set != variant then
      throwError m!"`{info.setting set}` is set, but `{module}` was compiled with \
        `{info.setting variant}`; set `{info.optionName}` for the build of every library instead, \
        in the `leanOptions` of its package"
  let variant := built?.map (·.1) |>.getD (set?.getD info.default)
  if record && !s.recorded then
    let module := (← getEnv).mainModule
    modifyEnv (variantExt.addEntry · { switch := info.name, module, variant })
  return variant

/-- The variant of the switch in this build, which the current module records if `record` holds. -/
public def Switch.variant [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m]
    (sw : Switch ρ α) (record := true) : m ρ := do
  let name ← sw.currentVariant record
  let some variant := sw.ofName? name | throwError "`{name}` is not a variant of `{sw.name}`"
  return variant

end Ab

end -- meta section

/-!
## Registering the sites of a switch

`Ab.Switch.register` records a site in every build, with the variants in which each of its branches
runs and where it is written, and returns the variant of the build, for a caller that chooses what
to do in each variant itself.  `Ab.Switch.whenIn` is built on it, and runs a continuation of the
caller in some variants only, as when a library adds to a registry of its own, and so is the
attribute form, `@[sw attr]`, in `Ab.Declare`.  The `ab%` syntax, in `Ab.Syntax`, expands to
them.
-/

public meta section

namespace Ab.Switch

open Lean

variable {ρ α : Type} {m : Type → Type}
  [Monad m] [MonadEnv m] [MonadOptions m] [MonadError m] [MonadFileMap m]

/--
Records the site `kind` on `target` with the payload `payload`, written at the syntax of the
current reference, which Go to Definition on it in a report opens, and returns the variant of the
build.  On an ordered switch, the variants in which the site takes effect are an up-set or a
down-set of the order.
-/
def register (sw : Switch ρ α) (target : Name) (kind : SiteKind ρ) (payload : α) : m ρ := do
  sw.checkSite target (kind.map sw.nameOf)
  let variant ← sw.variant
  let module := (← getEnv).mainModule
  let range? ← Elab.getDeclarationRange? (← getRef)
  modifyEnv (sw.ext.addEntry · { target, kind, module, range?, payload })
  return variant

/--
Records a site on `target` under the label `label`, which takes effect in the variants `variants`,
and runs the continuation `k` in those variants only.
-/
def whenIn [Inhabited α] (sw : Switch ρ α) (target : Name) (label : String)
    (variants : Array ρ) (k : m Unit) (payload : α := default) : m Unit := do
  if sw.isIn variants (← sw.register target (.cont label #[variants]) payload) then k

end Ab.Switch

end -- public meta section
