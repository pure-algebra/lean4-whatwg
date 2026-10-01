import Lean
import WhatwgGates.Trust.Config

/-!
# Gates.Trust.Environment

The audited trees, modules and declarations, and the environment pass of the
trust gate (contract section 4.1 of
`test/contracts/trust-gate-hardening.contract.md`, step 3 of section 3).

Everything here reads an `Environment` handed in by the host and nothing else:
the module headers, each audited module's own constant list, the kernel
declarations, and the parametric attributes behind `isExtern` and
`getImplementedBy?`, which answer for an imported constant from its module's
entries. An import fills those entries in whether or not it loads the
extensions, so an environment imported with `loadExts := false` is judged the
same as the one the in-tree command elaborates in.

The module imports `Lean` whole, as the gate module it was moved from does, so
that its definitions elaborate in the context they were written in.
-/

namespace Gates.Trust

open Lean

/-- `native_decide` mints a per-declaration auxiliary axiom whose name carries a
`_native` component (Lean 4.33.1 records `t._native.native_decide.ax_1_1` for a
theorem `t`). Such an axiom is forbidden by shape, whatever declaration it
hangs off. -/
def isNativeAuxiliaryAxiom (axiomName : Name) : Bool :=
  axiomName.anyS fun component => component == "_native"

/-- The synthesised values Lean gives an `opaque` with no body
(`default_or_ofNonempty%`, `Lean/Elab/DefView.lean`). -/
def synthesizedOpaqueBodies : List Name :=
  [``Inhabited.default, ``Classical.ofNonempty]

/-! ## Trees, modules and declarations -/

def treeOf? (config : Config) (moduleName : Name) : Option Name :=
  config.auditedTrees.find? (·.isPrefixOf moduleName)

def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

/-- The strict prefix a module is under: the longest that matches, if any. -/
def strictPrefixOf? (config : Config) (moduleName : Name) : Option Name :=
  config.strictCeilingPrefixes.foldl (init := none) fun best candidate =>
    if candidate.isPrefixOf moduleName then
      match best with
      | some current => if current.getNumParts < candidate.getNumParts then some candidate else best
      | none => some candidate
    else best

/-- One constant of an audited module. -/
structure AuditedDeclaration where
  name : Name
  moduleName : Name
  tree : Name

/-- Every constant of every audited module, read from the modules' own constant
lists rather than by materialising the whole constant map. A constant that
more than one module realises (an equation lemma that several modules unfold)
appears once, under the module `getModuleIdxFor?` records, exactly as the
environment's constant map holds it once. -/
def auditedDeclarations (config : Config) (environment : Environment) :
    Except String (Array AuditedDeclaration) := do
  let header := environment.header
  if header.moduleNames.size != header.moduleData.size then
    throw s!"Whatwg trust gate: the environment records {header.moduleNames.size} module names and {header.moduleData.size} module data entries"
  let mut found : Array AuditedDeclaration := #[]
  for index in [0:header.moduleNames.size] do
    let some moduleName := header.moduleNames[index]?
      | throw s!"Whatwg trust gate: module index {index} has no name"
    let some tree := treeOf? config moduleName | continue
    let some data := header.moduleData[index]?
      | throw s!"Whatwg trust gate: audited module {moduleName} has no module data"
    for name in data.constNames do
      if (environment.getModuleIdxFor? name).map (·.toNat) == some index then
        found := found.push { name, moduleName, tree }
  return found

def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-- The body under every leading `fun` binder and metadata wrapper. -/
def lambdaBody : Expr → Expr
  | .lam _ _ body _ => lambdaBody body
  | .mdata _ inner => lambdaBody inner
  | value => value

/-- Whether an `opaque` value is the one Lean synthesised for a missing body:
its head constant, under the binders a parameterised `opaque` puts in front,
is `Inhabited.default` or `Classical.ofNonempty`. An authored body that is
literally `default` is refused with them, by design (contract section 4.1). -/
def isSynthesizedOpaqueBody (value : Expr) : Bool :=
  match (lambdaBody value).getAppFn with
  | .const name _ => synthesizedOpaqueBodies.contains name
  | _ => false

/-- Whether a string is empty after trimming ASCII whitespace. -/
def isBlank (text : String) : Bool :=
  text.toList.all Char.isWhitespace

/-! ## The environment pass -/

/-- Pass 3: what each audited constant is (contract section 4.1). The parametric
attributes behind `isExtern` and `getImplementedBy?` answer for an imported
constant from its module's entries, which an import fills in whether or not it
loads the extensions. -/
def environmentFindings (environment : Environment)
    (declarations : Array AuditedDeclaration) : Array String := Id.run do
  let mut findings : Array String := #[]
  for declaration in declarations do
    let name := declaration.name
    if isGeneratedSafeRecursor environment name then continue
    let info ← match environment.find? name with
      | some info => pure info
      | none =>
          findings := findings.push
            s!"Whatwg trust gate: declaration {name} of module {declaration.moduleName} is missing from the environment"
          continue
    if info.isUnsafe then
      findings := findings.push s!"Whatwg trust gate: declaration {name} is unsafe"
    if info.isPartial then
      findings := findings.push s!"Whatwg trust gate: declaration {name} is partial"
    if let .axiomInfo _ := info then
      if isNativeAuxiliaryAxiom name then
        findings := findings.push
          s!"Whatwg trust gate: declaration {name} is a native-evaluation axiom (native_decide auxiliary)"
      else
        findings := findings.push
          s!"Whatwg trust gate: declaration {name} is an axiom; no audited tree declares one"
    if isExtern environment name then
      findings := findings.push
        s!"Whatwg trust gate: declaration {name} is `@[extern]`; host code replaces its checked body"
    if (Compiler.getImplementedBy? environment name).isSome then
      findings := findings.push
        s!"Whatwg trust gate: declaration {name} is `@[implemented_by]`; another declaration replaces its checked body in compiled code"
    if let .opaqueInfo opaqueInfo := info then
      if isSynthesizedOpaqueBody opaqueInfo.value then
        findings := findings.push
          s!"Whatwg trust gate: declaration {name} is an `opaque` with no authored body; Lean synthesised its value, so it denotes an inhabitant nobody chose"
  return findings

end Gates.Trust
