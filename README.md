# A/B Testing in Lean

Ab is a lightweight framework for doing A/B testing in Lean, built with its metaprogramming facility.
With Ab, we can mark the places in Lean code whose compiled code a build can choose between, records every such place, and reports them.

## Switches

A *switch* should be thought as an experiment.
It has *variants* that the build can choose among, given by a user-defined enum type (i.e., inductive types with no payloads).
A *site* is a place where the A/B test happens.
At each site, one choose certain compiled code based on the active variant of current build.

```lean
-- MyLibrary/Switches.lean
module
public meta import Ab.Declare
public meta import MyLibrary.Types   -- `HashImpl` (`reference | fnv | wyhash`), `HashNote`
public import MyLibrary.Types

/-- Which hash function the tables use. -/
declare_ab_switch hash (variants := HashImpl) (default := fnv) (payload := HashNote)
```

`declare_ab_switch name` declares the switch `name` in the current namespace, the option `ab.<name>` that sets its variant, and the attribute `@[name attr]`.
The three of them exist in the modules that import the declaring one.
The variant type, set with `(variants := ...)`, defaults to `Bool` if not set.
If a build does not set the option, it uses the default variant declared in `(default := ...)`, which is `fnv` in this case.
Each site carries the payload type in `(payload := ...)`, and the reports render them through `ToMessageData`.
If not set, the payload type would be `Unit`.
Both types are used at the meta phase, so they can come from a module imported with `meta import`, or from a `meta section**.

## Sites

An experiment site can be registered in one of the following three forms.

### Attribute

We can wrap an attribute with the switch, so its effectiveness is controlled.
In the example below, the `implemented_by` is controlled by the `hash` switch, and only takes effect when the active variant is `fnv` or `wyhash`.
The payload here is chosen to be a text note.

```lean
-- An attribute, applied in the variants `fnv` and `wyhash` only.
@[hash (variants := fnv, wyhash) (payload := { note := "3x, short keys" }) implemented_by hashFast]
def hashKey (k : Key) : UInt64 := ...
```

### Meta Code

There are two ways to register an experiment site in metaprograms.
They both require a target, that is the name of the definition, given in the Lean `Name` type, and a label, given as a plain string.
The target is the definition that the switch affects, and will be used in the experiment report.
The label is any string chosen by the user to label for convenience.

Both form start with `ab%` and the switch declared, then with the target and label.
The difference is that the first form takes a list of variants after the switch, written in `ab%[<sw>|<variants>, ...]` while the second form provides a pattern matching syntax.
The first form's continuation runs if the active variant of current build is in the list, and the second form is intuitively pattern matching on the variant.

```lean
-- A continuation that runs in some variants only, as when adding to a registry.
ab%[MyLibrary.hash| .fnv, .wyhash] ``hashKey "my_registry" do registerFolder ...

-- Branches as of a `match` on the variant, as when an elaborator generates code.  The branch of
-- the variant of the build runs, and its right-hand side is a `do` sequence.
ab%[MyLibrary.hash] ``hashKey "my_elab"
| .reference => ...
| _ => ...
```

A module that writes `ab%` imports `Ab.Syntax` with `meta import`.

## Ordered Switches

The variants of a switch can carry an order, such as how much a build trusts, so that each site takes effect from some variant up, or up to some variant.
`(ordered := true)` orders the variants by the `LE` instance of the variant type, whose `≤` must be decidable and a partial order, which Ab checks when the switch is declared.

```lean
-- MyLibrary/Types.lean
public inductive Trust where
  | kernel | trivial | extern | compiler
deriving BEq, Inhabited, Ord

public instance : LE Trust := leOfOrd

-- MyLibrary/Switches.lean
/-- How much code the kernel does not check that a build attaches. -/
declare_ab_switch trust (variants := Trust) (default := compiler) (ordered := true)
```

A site of an ordered switch names its variants by a bound, in the attribute and in `ab%`, both bounds inclusive:

| Gadget | Variants | Example, on the order above |
| --- | --- | --- |
| `upset a, b` | those above `a` or `b`, an up-set | `upset extern` is `extern`, `compiler` |
| `downset a, b` | those below `a` or `b`, a down-set | `downset trivial` is `kernel`, `trivial` |

```lean
-- The twin is attached in the levels `trivial`, `extern` and `compiler`.
@[trust (upset := trivial) implemented_by hashKeyUnsafe]
def hashKey (k : Key) : UInt64 := ...

-- The folder is registered in the level `compiler` only.
ab%[MyLibrary.trust| upset .compiler] ``hashKey "my_registry" do registerFolder ...

-- The reference code is checked in the levels `kernel` and `trivial` only.
ab%[MyLibrary.trust| downset .trivial] ``hashKey "my_check" do checkReference ...
```

A site of an ordered switch takes effect in an up-set or a down-set of the order, however it names its variants, and any other set is an error.
So, going up the order, a site switches on or off once, and never back.
The branches of the pattern-matching form of `ab%` cover every variant together, so they are not checked.
Several bounds are for a partial order, where the variants above `a` or `b` need not be those above a single variant.
The reports name such a set by its generators as an array, `upset #[a, b]` with its minimal elements or `downset #[a, b]` with its maximal elements.

## Setting the Active Variant

The variant is a setting of the build of a whole library, since a site takes effect when its module is compiled.
Each module records the variant it was compiled in the first time it asks for it, and its importers follow that variant.
Combining modules built in different variants of a switch, or setting the option against the recorded variant, is an error.
In the lakefile of the library:

```lean
package myLibrary where
  leanOptions := #[⟨`weak.ab.hash, "fnv"⟩]   -- or `-D weak.ab.hash=fnv`
```

## Reporting the Experiments

`#print ab` lists all the switches in scope, each as a node of the infoview with its variants, the default and the variant of this build marked, and its sites, folded.
`#print ab <sw>` lists one switch, with its sites unfolded.
The modules and the sites under them are folded, so that the branches of a site show when it is opened.
The report tree roots in the switch, `[<sw>]`, with its description, and `[variants]` list all the variants as well as labeling the default and the active ones.

Below that are the site reports, grouped by Lean modules.
Each site is under its attribute (if registered on attributes) or label (if registered with `ab%`), with a node for each of its branches.
A `[skip]` node stands for the branch in which nothing runs, happens in the non-pattern matching form of `ab%`.
On an ordered switch, a set of variants that is an up-set or a down-set shows as `upset #[...]` or `downset #[...]` of its generators.
The bullet shows which branch of the site is enabled.
The payload, if exists, is rendered under the `[payload]` node.
The variants hover as their constructors, the description as the switch, and "Go to Definition" on a site opens where it is written.

```
[hash] Which hash function the tables use.
  [variants] reference (default), fnv (this build), wyhash
  [sites] 2/2 active
    [module] MyLibrary.Table
      [implemented_by] hashKey
        [branch] ● #[fnv, wyhash]
        [skip] ○ #[reference]
        [payload] 3x, short keys
      [my_elab] hashKey
        [branch] ○ #[reference]
        [branch] ● #[fnv, wyhash]
```
