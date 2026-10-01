import WhatwgGates.Trust.Environment

/-!
# Gates.Trust.Axioms

The axiom pass of the trust gate with both ceilings and the strict-ceiling
exception checks (contract section 6 of
`test/contracts/trust-gate-hardening.contract.md`, step 4 of section 3).

The pass does not collect axioms itself: the host hands it `axiomsOf`, the
axioms one constant reaches, in the host's own monad. The in-tree command
passes `Lean.collectAxioms`, which reads the per-module axiom tables of the
loaded extension `exportedAxiomsExt`; a host that imports with
`loadExts := false` has no such table and passes its own traversal of each
constant's kernel type and value (addendum V2e.5, step 4). Everything else the
pass reads is the configuration and the environment.
-/

namespace Gates.Trust

open Lean

/-- A ceiling as its diagnostics spell it, on one line. -/
def ceilingText (separator : String) (ceiling : List Name) : String :=
  separator.intercalate (ceiling.map toString)

/-- The three compiler-trust axioms. With `sorryAx` they are the axioms no
audited constant may reach, and the trust-token pass refuses all four by name. -/
def forbiddenTrustAxioms : List Name :=
  [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Axioms no audited constant may reach. -/
def forbiddenAxioms : List Name :=
  ``sorryAx :: forbiddenTrustAxioms

/-- The checks every strict-ceiling exception passes once it names a
declaration (contract section 6): its module is under a strict prefix, and it
reaches `Classical.choice`. `axiomsOf` gives the axioms a constant reaches. -/
def strictExceptionTargetFindings {m : Type → Type} [Monad m] (config : Config)
    (axiomsOf : Name → m (Array Name)) (environment : Environment) (declaration : Name) :
    m (Array String) := do
  if !environment.contains declaration then
    return #[s!"Whatwg axiom gate: strict-ceiling exception names missing declaration {declaration}"]
  let moduleName := (moduleOf? environment declaration).getD environment.mainModule
  if (strictPrefixOf? config moduleName).isNone then
    return #[s!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; its module {moduleName} is under no strict prefix"]
  if !(← axiomsOf declaration).contains ``Classical.choice then
    return #[s!"Whatwg axiom gate: stale strict-ceiling exception for {declaration}; it does not reach Classical.choice"]
  return #[]

/-- Validate the strict prefixes and every strict-ceiling exception; return the
findings and the declarations the exceptions name. -/
def strictCeilingFindings {m : Type → Type} [Monad m] (config : Config)
    (axiomsOf : Name → m (Array Name)) (environment : Environment)
    (declarations : Array AuditedDeclaration) : m (Array String × Array Name) := do
  let mut findings : Array String := #[]
  for strictPrefix in config.strictCeilingPrefixes do
    if !(`Whatwg).isPrefixOf strictPrefix then
      findings := findings.push
        s!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} is outside the Whatwg tree; ruling R-V1 keeps WhatwgTest and WhatwgGates under R-11" -- R-V3(c), 2026-10-01
    if !(declarations.any fun declaration => strictPrefix.isPrefixOf declaration.moduleName) then
      findings := findings.push
        s!"Whatwg axiom gate: strict-ceiling prefix {strictPrefix} covers no audited module"
  let mut excepted : Array Name := #[]
  for entry in config.strictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        s!"Whatwg axiom gate: strict-ceiling exception for {entry.declaration} carries no reason"
    findings := findings ++
      (← strictExceptionTargetFindings config axiomsOf environment entry.declaration)
    excepted := excepted.push entry.declaration
  for entry in config.privateStrictCeilingExceptions do
    if isBlank entry.reason then
      findings := findings.push
        s!"Whatwg axiom gate: strict-ceiling exception for {entry.original} (private to {entry.owner}) carries no reason"
    let owned := declarations.filter fun declaration =>
      declaration.moduleName == entry.owner &&
        privateToUserName? declaration.name == some entry.original
    match owned.toList with
    | [declaration] =>
        findings := findings ++
          (← strictExceptionTargetFindings config axiomsOf environment declaration.name)
        excepted := excepted.push declaration.name
    | [] =>
        findings := findings.push
          s!"Whatwg axiom gate: strict-ceiling exception names missing declaration {entry.original} (private to {entry.owner})"
    | _ =>
        findings := findings.push
          s!"Whatwg axiom gate: private strict-ceiling exception {entry.owner}/{entry.original} matched {owned.size} declarations; expected exactly one"
  let mut seen : NameSet := {}
  let mut repeated : NameSet := {}
  for name in excepted do
    if seen.contains name && !repeated.contains name then
      repeated := repeated.insert name
      findings := findings.push
        s!"Whatwg axiom gate: strict-ceiling exception for {name} is listed more than once"
    seen := seen.insert name
  return (findings, excepted)

/-- Pass 4, the axiom pass (contract section 6): the strict prefixes and every
strict-ceiling exception are checked first; then, over every audited constant,
the forbidden axioms and every native-evaluation auxiliary are refused, R-11's
ceiling binds every audited tree, and the strict ceiling binds every constant
whose module is under a strict prefix unless an exact exception names it.
`axiomsOf` gives the axioms a constant reaches. Returns the findings and the
constants that reach `Classical.choice`. -/
def axiomPassFindings {m : Type → Type} [Monad m] (config : Config)
    (axiomsOf : Name → m (Array Name)) (environment : Environment)
    (declarations : Array AuditedDeclaration) :
    m (Array String × Array AuditedDeclaration) := do
  let repositoryCeilingText := ceilingText ", " config.repositoryCeiling
  let strictCeilingText := ceilingText " and " config.strictCeiling
  let (exceptionFindings, excepted) ←
    strictCeilingFindings config axiomsOf environment declarations
  let mut axiomFindings := exceptionFindings
  let mut choiceReachers : Array AuditedDeclaration := #[]
  for declaration in declarations do
    let name := declaration.name
    let axioms ← axiomsOf name
    for axiomName in axioms do
      if isNativeAuxiliaryAxiom axiomName then
        axiomFindings := axiomFindings.push
          s!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName} (native_decide auxiliary)"
      else if forbiddenAxioms.contains axiomName then
        axiomFindings := axiomFindings.push
          s!"Whatwg axiom gate: declaration {name} reaches forbidden axiom {axiomName}"
      else if !config.repositoryCeiling.contains axiomName then
        axiomFindings := axiomFindings.push
          s!"Whatwg axiom gate: declaration {name} reaches unexpected axiom {axiomName}; the ceiling is {repositoryCeilingText}"
    if axioms.contains ``Classical.choice then
      choiceReachers := choiceReachers.push declaration
      if let some strictPrefix := strictPrefixOf? config declaration.moduleName then
        if !excepted.contains name then
          axiomFindings := axiomFindings.push
            s!"Whatwg axiom gate: declaration {name} reaches Classical.choice under the strict ceiling of {strictPrefix}, which admits {strictCeilingText} only, and no exact exception names it"
  return (axiomFindings, choiceReachers)

end Gates.Trust
