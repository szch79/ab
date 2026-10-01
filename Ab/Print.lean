/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Switch
public meta import Lean.Elab.Command
meta import Ab.Init

/-!
# `#print ab`

`#print ab` lists the switches that the imported modules declare, each as a trace node with its
variants, the variant of this build, and its sites by module, each under its attribute or label,
with a node for each of its branches, marked by whether this build takes it, and its payload.  On
an ordered switch, the variants of a branch show as `upset` their minimal elements when they are
an up-set, and as `downset` their maximal elements when they are a down-set.
`#print ab name` lists the switch `name` only, with its node of sites unfolded.  The modules and
the sites under it are folded.
-/

meta section

namespace Ab

open Lean Elab Command

/--
The text `text`, whose hover and Go to Definition are those of the constant `const`, with the
docstring `docString?` in place of its own.
-/
def ofConstText (text : String) (const : Name) (docString? : Option String := none) :
    MessageData :=
  .ofLazy (fun ctx? => do
      let some ctx := ctx? | return Dynamic.mk (MessageData.ofFormat text)
      let some info := ctx.env.find? const | return Dynamic.mk (MessageData.ofFormat text)
      return Dynamic.mk <| MessageData.withExprHover text
        (.const const (info.levelParams.map mkLevelParam)) ctx.lctx (docString? := docString?))
    (fun _ => false)

/-- The variant of the switch in this build, without recording it, or why it has none. -/
def SwitchInfo.buildVariant (sw : SwitchInfo) : CoreM (Except MessageData String) := do
  try
    return .ok (← sw.currentVariant (record := false))
  catch e =>
    return .error e.toMessageData

/-- The variant `variant` of the switch, whose hover is that of its constructor. -/
def SwitchInfo.variantMessage (sw : SwitchInfo) (variant : String) : MessageData :=
  ofConstText variant (sw.variantType.str variant)

/-- The variants of the switch, with the default and the variant `build?` of this build marked. -/
def SwitchEntry.variantsLine (sw : SwitchEntry) (build? : Option String) : MessageData :=
  .joinSep (sw.variantNames.toList.map fun variant =>
    let marks := (if variant == sw.default then #["default"] else #[]) ++
      (if build? == some variant then #["this build"] else #[])
    if marks.isEmpty then sw.variantMessage variant
    else m!"{sw.variantMessage variant} ({", ".intercalate marks.toList})")
    ", "

/--
The variants `variants`, as a list, or, on an ordered switch, by `upset` and their minimal elements
when they are an up-set, and by `downset` and their maximal elements when they are a down-set, other
than every variant.
-/
def SwitchEntry.setMessage (sw : SwitchEntry) (variants : Array String) : MessageData :=
  let names (variants : Array String) : MessageData :=
    .joinSep (variants.toList.map sw.variantMessage) ", "
  let list := m!"#[{names variants}]"
  match sw.le? with
  | none => list
  | some le =>
    let set := sw.variantNames.filter variants.contains
    if set.isEmpty || set.size == sw.variantNames.size then list
    else if (upGap? le sw.variantNames set).isNone then m!"upset #[{names (minimalOf le set)}]"
    else if (downGap? le sw.variantNames set).isNone then m!"downset #[{names (maximalOf le set)}]"
    else list

/-- The mark of a branch that this build takes. -/
def activeMark : String := "●"

/-- The mark of a branch that this build does not take. -/
def inactiveMark : String := "○"

/--
The node of the site `site`, whose class is its attribute or label and whose header is its target,
with a node for each of its branches and a skip node for the variants in which nothing runs, if any,
each marked by whether the variant `build?` of this build takes it, and its payload.
-/
def SwitchEntry.siteNode (sw : SwitchEntry) (build? : Option String)
    (site : SwitchSite String (Option MessageData)) : MessageData :=
  let cls := match site.kind with
    | .attr name _ => name
    | .cont label _ => .mkSimple label
  let branchNode (cls : Name) (variants : Array String) : MessageData :=
    let mark := match build? with
      | some variant => if variants.contains variant then s!"{activeMark} " else s!"{inactiveMark} "
      | none => ""
    .trace { cls } m!"{mark}{sw.setMessage variants}" #[]
  let branches := site.kind.branches
  let rest := sw.variantNames.filter fun variant => !branches.any (·.contains variant)
  let branchNodes := branches.map (branchNode `branch) ++
    if rest.isEmpty then #[] else #[branchNode `skip rest]
  let payload : Array MessageData := match site.payload with
    -- A trace node, since the infoview indents trace nodes only.
    | some payload => #[.trace { cls := `payload } payload #[]]
    | none => #[]
  .trace { cls } site.targetMessage (branchNodes ++ payload)

/--
The sites `sites` of the switch, a trace node for each module with a node for each of its sites, by
target, and in the order they were recorded for each target.
-/
def SwitchEntry.moduleNodes (sw : SwitchEntry) (build? : Option String)
    (sites : Array (SwitchSite String (Option MessageData))) : Array MessageData :=
  let sorted := sites.toList.mergeSort fun a b =>
    a.module.lt b.module || (a.module == b.module && !b.target.lt a.target)
  sorted.splitBy (·.module == ·.module) |>.toArray.map fun group =>
    .trace { cls := `module } m!"{group.head!.module}" (group.toArray.map (sw.siteNode build?))

/--
The trace node of the switch: its variants, with the default and the variant of this build marked,
and its sites, folded when `collapsed`, with the modules and the sites under it folded.  Its
description hovers as the declaration of the switch.
-/
def SwitchEntry.node (sw : SwitchEntry) (collapsed : Bool) : CoreM MessageData := do
  let sites := sw.sites (← getEnv)
  let build ← sw.buildVariant
  let count : MessageData := match build with
    | .ok variant => m!"{(sites.filter (·.activeIn variant)).size}/{sites.size} active"
    | .error _ => m!"{sites.size}"
  let buildNodes : Array MessageData := match build with
    | .ok _ => #[]
    | .error msg => #[.trace { cls := `build } msg #[]]
  let ordered := if sw.le?.isSome then
      "  The variants are ordered, and each site takes effect in every variant above one where it \
        does, or in every variant below one."
    else ""
  let descr := ofConstText sw.descr sw.ref
    (docString? := s!"{sw.descr}\n\nThe option `{sw.optionName}` sets the variant.{ordered}")
  return .trace { cls := sw.name, collapsed := false } descr <|
    #[.trace { cls := `variants } (sw.variantsLine build.toOption) #[]] ++ buildNodes ++
      #[.trace { cls := `sites, collapsed } count (sw.moduleNodes build.toOption sites)]

/--
Logs the report `msg` as information.  A message that is a trace node is classified as a trace,
which `#guard_msgs` and its filters tell apart from information, so `msg` is composed with nothing.
-/
def logReport (msg : MessageData) : CommandElabM Unit :=
  logInfo (.compose .nil msg)

/--
`#print ab` lists the switches that the imported modules declare, each with its variants, the
default and the variant of this build marked, and its sites, folded.  `#print ab name` lists the
switch `name` only, with its node of sites unfolded.  The modules and the sites under it are
folded.  Each site is under its attribute or label, with the variants of each of its branches,
and of a skip where nothing runs, marked by whether this build takes it.  Go to Definition on a
site opens where it is written.
-/
elab (name := printAb) "#print " &"ab" name?:(ppSpace ident)? : command => do
  let all ← switches
  match name? with
  | none =>
    if all.isEmpty then
      logInfo "No switches are declared in the imported modules."
    else
      let nodes ← liftCoreM <| all.mapM (·.node (collapsed := true))
      logReport <| .joinSep nodes.toList "\n"
  | some name =>
    let some sw := all.find? (·.name == name.getId) |
      throwErrorAt name m!"`{name.getId}` is not a switch of the imported modules; the switches \
        are {codeList (all.map (·.name.toString))}"
    logReport (← liftCoreM <| sw.node (collapsed := false))

end Ab

end -- meta section
