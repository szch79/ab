/-
SPDX-FileCopyrightText: 2026 Mingtong Lin
SPDX-License-Identifier: MIT
-/
module

public meta import Ab.Switch
public meta import Lean.Compiler.IR.CompilerM
public meta import Lean.Elab.Command
public meta import Lean.Elab.Eval
public meta import Lean.Linter.UnusedVariables
meta import Ab.Init

/-!
# Declaring a switch

`declare_ab_switch name` declares a switch, its option `ab.<name>` and its attribute `@[name attr]`,
which applies the attribute `attr` in some variants of the switch only and records the site.  The
switch, its option and its attribute exist in the modules that import the declaring one, as for
every registration that Lean runs when a module is imported.  `(ordered := true)` orders the
variants by `≤`, which is checked to be a partial order when the switch is declared.
-/

public meta section

namespace Ab

open Lean Elab Command

/--
How the attribute of a switch names its variants: `variants` lists them, and on an ordered switch
`upset` names those above some variants and `downset` those below some.
-/
syntax switchVariants := &"variants" <|> &"upset" <|> &"downset"

/--
The arguments of the attribute of a switch: the variants in which it applies the attribute, the
payload of the site, and the attribute.
-/
syntax switchAttrArgs :=
  (atomic("(" switchVariants) " := " ident,+ ")")? ("(" &"payload" " := " term ")")? attr

/-- The name of the attribute that the syntax `stx` applies, as `Lean.Elab.elabAttr` finds it. -/
private def attrName? (stx : Syntax) : Option Name :=
  if stx.getKind == ``Parser.Attr.simple then
    some stx[0].getId.eraseMacroScopes
  else match stx.getKind with
    | .str _ s => some (.mkSimple s)
    | _ => none

/-- Elaborates the term `stx` of the type `type` and evaluates it. -/
private unsafe def evalSyntaxUnsafe (α : Type) [Inhabited α] (type : Expr) (stx : Syntax) :
    CoreM α :=
  (Term.evalTerm α type stx).run' |>.run'

@[inherit_doc evalSyntaxUnsafe, implemented_by evalSyntaxUnsafe]
private opaque evalSyntax (α : Type) [Inhabited α] (type : Expr) (stx : Syntax) : CoreM α

/--
The payload that the term `stx?` of the type `payloadType?` evaluates to, or the default without it,
and an error when the switch `sw` takes no payload.
-/
private def Switch.payload [Inhabited α] (sw : Switch ρ α) (payloadType? : Option Expr)
    (stx? : Option Syntax) : CoreM α :=
  match stx?, payloadType? with
  | none, _ => pure default
  | some stx, some type => evalSyntax α type stx
  | some stx, none => throwErrorAt stx m!"`{sw.name}` takes no payload"

/--
Applies the attribute of the switch `sw` written as `stx` to `decl`: records the site, and applies
the inner attribute in the variants of the site.
-/
private def addSwitchAttr [Inhabited α] (sw : Switch ρ α) (payloadType? : Option Expr)
    (decl : Name) (stx : Syntax) (kind : AttributeKind) : AttrM Unit := do
  let args := stx[1]
  let variantIds := args[0][3].getSepArgs
  let variants ← if variantIds.isEmpty then
      if sw.isBool then pure (#["true"].filterMap sw.ofName?) else
      throwErrorAt stx m!"`{sw.name}` is not over `Bool`, so name the variants in which it applies \
        the attribute, as in `@[{sw.name} (variants := {sw.variantNames[0]!}) attr]`"
    else
      let named ← variantIds.mapM fun id => do
        let some variant := sw.ofName? id.getId.toString |
          throwErrorAt id m!"`{id.getId}` is not a variant of `{sw.name}`"
        pure variant
      -- Each alternative of `switchVariants` is a node around its atom.
      withRef args[0][1] do
        match args[0][1][0][0].getAtomVal with
        | "upset" => sw.upSet named
        | "downset" => sw.downSet named
        | _ => pure named
  let payload ← sw.payload payloadType? (if args[1].isNone then none else some args[1][3])
  let inner := args[2]
  let some attr := attrName? inner | throwErrorAt inner "unknown attribute"
  let impl ← ofExcept <| getAttributeImpl (← getEnv) attr
  match impl.applicationTime with
  | .beforeElaboration =>
    throwErrorAt inner m!"`{sw.name}` cannot apply `{attr}`, which applies before elaboration"
  | .afterCompilation =>
    if (IR.findEnvDecl (← getEnv) decl).isNone then
      throwErrorAt inner m!"`{attr}` applies after compilation, so `{sw.name} {attr}` must be \
        attached with the `attribute` command after the declaration"
  | .afterTypeChecking => pure ()
  let variant ← withRef stx <| sw.register decl (.attr attr variants) payload
  if sw.isIn variants variant then impl.add decl inner kind

/--
Registers the switch `name`, with the variants `variants` of the type `variantType`, named and in
order, the payload type `payloadType?` (`none` for `Unit`), the rendering `render` of its payloads
and the order `le?` of its variants, when it is ordered: its option `ab.<name>`, the extension of
its sites, named after `ref`, and its attribute.  The parser of the attribute is declared by
`declare_ab_switch`, which calls this function.
-/
def registerSwitch [BEq ρ] [Inhabited α] (name : Name) (descr : String) (variantType : Name)
    (variants : Array (String × ρ)) (default : String) (isBool : Bool)
    (payloadType? : Option Expr) (render : α → Option MessageData)
    (le? : Option (ρ → ρ → Bool) := none) (ref : Name := by exact decl_name%) :
    IO (Switch ρ α) := do
  let optionName := `ab ++ name
  let ofName? (n : String) := (variants.find? (·.1 == n)).map (·.2)
  let le? := le?.map fun le a b => match ofName? a, ofName? b with
    | some a, some b => le a b
    | _, _ => false
  let info : SwitchInfo :=
    { name, descr, optionName, variantType, variantNames := variants.map (·.1), default, isBool,
      le?, ref }
  registerOption optionName {
    name := optionName
    declName := ref
    defValue := if isBool then .ofBool (default == "true") else .ofString default
    descr := s!"{descr}  The variant of the switch `{name}`, which is a setting of the build of a \
      whole library: set `weak.{optionName}` in the `leanOptions` of its package, and the modules \
      that import the library follow the variant it was built in."
  }
  let ext ← registerSimplePersistentEnvExtension {
    name := ref
    addEntryFn := insertSite
    addImportedFn := fun ess => ess.foldl (init := {}) fun m es => es.foldl insertSite m
    asyncMode := .sync
  }
  let sw : Switch ρ α := {
    info with
    nameOf := fun variant => (variants.find? (·.2 == variant)).map (·.1) |>.getD ""
    ofName?
    ext }
  registerBuiltinAttribute {
    ref, name
    descr := s!"apply an attribute in some variants of the switch `{name}` only"
    add := addSwitchAttr sw payloadType?
  }
  switchesRef.modify (·.push {
    info with
    sites := fun env => (sw.sites env).map fun site =>
      { site with kind := site.kind.map sw.nameOf, payload := render site.payload } })
  return sw

/--
`declare_ab_switch name` declares a switch, a choice that the build of a library makes, with the
option `ab.<name>` that sets its variant and the attribute `@[name attr]`, which applies `attr` in
some variants only.  The switch is the declaration `name` in the current namespace, of type
`Ab.Switch ρ α`, and it, its option and its attribute exist in the modules that import this one.
The name is atomic, since it names the attribute.

* `(variants := T)` makes the variants the constructors of the enumeration `T`, by default `Bool`.
  The option is a `Bool` for `Bool`, and otherwise a string naming a constructor.
* `(default := a)` names the variant of a build that does not set the option, by default the first
  variant.
* `(ordered := true)` orders the variants by the instance of `LE T`, whose `≤` is decidable and a
  partial order, such as `leOfOrd` with `deriving Ord`.  A site of an ordered switch takes effect
  in every variant above one where it does, or in every variant below one.
* `(payload := P)` makes `P` the type of the data that each site carries, which the reports render
  through `ToMessageData`.  Without it the payload is `()` and the reports show none.

The attribute is written `@[name (variants := a, b) (payload := p) attr]`.  It applies `attr` in
the variants `a` and `b` only, and records the site with the payload `p`, a term of type `P`.  On
an ordered switch, `(upset := a, b)` names the variants above `a` or `b`, and
`(downset := a, b)` those below `a` or `b`, both inclusive.  The variants may be left out for a
switch over `Bool`, where they are `true`, and the payload when it is `default`.
-/
syntax (name := declareAbSwitch) (docComment)? "declare_ab_switch " ident
  (atomic(" (" &"variants") " := " ident ")")?
  (atomic(" (" &"default") " := " ident ")")?
  (atomic(" (" &"ordered") " := " ident ")")?
  (" (" &"payload" " := " ident ")")? : command

/-- The constructors of the enumeration `type`, which have no arguments. -/
private def enumCtors (type : Name) : CoreM (Array Name) := do
  let .inductInfo info ← getConstInfo type |
    throwError m!"`{.ofConstName type}` is not an inductive type"
  unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do
    throwError m!"`{.ofConstName type}` is not an enumeration, since it has parameters, indices \
      or universes"
  info.ctors.toArray.mapM fun ctor => do
    let .ctorInfo ctorInfo ← getConstInfo ctor | unreachable!
    unless ctorInfo.numFields == 0 do
      throwError m!"`{.ofConstName type}` is not an enumeration, since `{.ofConstName ctor}` has \
        arguments"
    return ctor

/--
Checks that `≤` on the enumeration `type`, whose constructors are `variants` by name, is decidable
and a partial order, by evaluating it on every pair of constructors.
-/
private def checkPartialOrder (type : Name) (variants : Array (String × Ident)) :
    CommandElabM Unit := do
  -- Elaborated without recovery first, since `Term.evalTerm` logs its errors rather than throwing.
  try
    liftTermElabM <| Term.withoutErrToSorry do
      discard <| Term.elabTermAndSynthesize
        (← `(fun (a b : $(mkIdent type)) => decide (a ≤ b))) none
  catch e =>
    throwError m!"`(ordered := true)` orders the variants by an instance of `LE {type}` whose `≤` \
      is decidable, such as `leOfOrd` with `deriving Ord`:{indentD e.toMessageData}"
  let rows ← variants.mapM fun (_, a) => do
    let cells ← variants.mapM fun (_, b) => `(decide ($a ≤ $b))
    `(#[$cells,*])
  let table ← liftCoreM <| evalSyntax (Array (Array Bool)) (toTypeExpr (Array (Array Bool)))
    (← `(#[$rows,*]))
  let le (i j : Nat) := table[i]![j]!
  let name (i : Nat) := variants[i]!.1
  let notPartial := m!"`≤` on `{type}` is not a partial order"
  let indices := List.range variants.size
  for i in indices do
    unless le i i do
      throwError m!"{notPartial}: `{name i} ≤ {name i}` does not hold"
  for i in indices do
    for j in indices do
      if i < j && le i j && le j i then
        throwError m!"{notPartial}: `{name i} ≤ {name j}` and `{name j} ≤ {name i}` hold for \
          distinct variants"
      for k in indices do
        if le i j && le j k && !le i k then
          throwError m!"{notPartial}: `{name i} ≤ {name j}` and `{name j} ≤ {name k}` hold, but \
            not `{name i} ≤ {name k}`"

@[command_elab declareAbSwitch, inherit_doc declareAbSwitch]
def elabDeclareAbSwitch : CommandElab := fun stx => do
  let `($[$doc?:docComment]? declare_ab_switch $id $[(variants := $type?)]?
      $[(default := $default?)]? $[(ordered := $ordered?)]? $[(payload := $payload?)]?) := stx
    | throwUnsupportedSyntax
  let name := id.getId
  unless name.isAtomic do
    throwErrorAt id "the name of a switch is atomic, since it is also the name of its attribute"
  let type ← match type? with
    | none => pure ``Bool
    | some type => liftCoreM <| realizeGlobalConstNoOverloadWithInfo type
  let variants := (← liftCoreM <| enumCtors type).map fun ctor => (ctor.getString!, mkIdent ctor)
  let variantNames := variants.map (·.1)
  let variantOf (variantId : Ident) : CommandElabM String := do
    let variant := variantId.getId.toString
    unless variantNames.contains variant do
      throwErrorAt variantId m!"`{variant}` is not a variant of `{name}`; its variants are \
        {codeList variantNames}"
    return variant
  let default ← default?.mapM variantOf
  let default := default.getD variantNames[0]!
  let le ← match ordered? with
    | none => `(none)
    | some flag => match flag.getId with
      | `false => `(none)
      | `true =>
        withRef flag <| checkPartialOrder type variants
        `(some fun (a b : $(mkIdent type)) => decide (a ≤ b))
      | _ => throwErrorAt flag "`ordered` is `true` or `false`"
  let (payloadType, payloadExpr, render) ← match payload? with
    | none => pure (← `(Unit), ← `(none), ← `(fun _ => none))
    | some type =>
      let type ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo type
      pure (mkIdent type, ← `(some (Lean.mkConst $(quote type))),
        ← `(fun p => some (Lean.toMessageData p)))
  let descr := doc?.map (·.getDocString.replace "\n" " " |>.trimAscii.toString)
    |>.getD s!"The switch `{name}`."
  let variantTerms ← variants.mapM fun (n, c) => `(($(quote n), $c))
  elabCommand <| ← `($[$doc?:docComment]? public meta initialize $id :
      Ab.Switch $(mkIdent type) $payloadType ←
    Ab.registerSwitch $(quote name) $(quote descr) $(quote type) #[$variantTerms,*]
      $(quote default) $(quote (type == ``Bool)) $payloadExpr $render (le? := $le))
  -- The kind of the attribute is under `Ab.SwitchAttr`, where the unused-variable linter finds it.
  withScope ({ · with currNamespace := .anonymous }) do
    elabCommand <| ← `(syntax (name := $(mkIdent (`Ab.SwitchAttr ++ name)))
      $(Syntax.mkStrLit (name.toString ++ " ")):str $(mkIdent ``switchAttrArgs):ident : attr)

/--
Whether the attribute syntax `inner` replaces the code of the declaration, which then need not use
its parameters.
-/
def isForeignAttr (inner : Syntax) : Bool :=
  inner.isOfKind ``Parser.Attr.extern ||
    (inner.isOfKind ``Parser.Attr.simple && inner[0].getId.eraseMacroScopes == `implemented_by)

/--
The parameters of a declaration with a switch attribute that applies `extern` or `implemented_by`
are not linted as unused, as for `extern` and `implemented_by` themselves, since its kernel
definition need not use them.
-/
@[unused_variables_ignore_fn]
def ignoreSwitchParams : Linter.IgnoreFunction := fun _ stack _ =>
  stack.matches [`null, none, `null, none, none, ``Parser.Command.declaration] &&
  (stack[3]? |>.any fun (stx, _) =>
    stx.isOfKind ``Parser.Command.optDeclSig || stx.isOfKind ``Parser.Command.declSig) &&
  (stack[5]? |>.any fun (stx, _) => (stx[0].find? fun attr =>
    attr.getKind.getPrefix == `Ab.SwitchAttr && isForeignAttr attr[1][2]).isSome)

end Ab

end -- public meta section
