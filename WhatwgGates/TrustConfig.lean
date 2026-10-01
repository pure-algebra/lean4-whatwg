import WhatwgGates.Trust.Config

/-!
# Gates.TrustConfig

This repository's data for the trust gate (addendum V2e.3 of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-W7(a)): the audited
trees, the two ceilings, the strict prefixes and the exact lists, each anchored
list below the comment line after which `lake exe whatwg_trustselftest` plants
its entries. `config` is the one value the gate library reads. The in-tree
command `#whatwg_streams_axiom_gate` of `WhatwgTest/Audit/AxiomGate.lean` hands
it to every pass, and the executable gate is to hand it the same value, so both
judge with one copy.

The module declares data only and imports only `WhatwgGates.Trust.Config`. It is
imported by `WhatwgTest.Audit.AxiomGate`, which keeps it in the test root's
import closure, and by nothing else in the audited trees: not by the umbrella
`WhatwgGates`, not by any `WhatwgGates.Trust` module and not by anything a
census battery imports (ruling R-W14(b)). An after-anchor plant therefore
rebuilds this module, the gate module and the test root, and no census battery,
which would read `vendor/` and `docs/` that the self-test's probe does not
copy. The module is audited like every tooling module and is not a
metaprogramming module.
-/

namespace Gates.TrustConfig

open Lean (Name)
open Gates.Trust

/-- The audited trees, disjoint under `Name.isPrefixOf`, which compares whole
components. The SHA-256 lane that used to be a fourth is the required `hash`
package since step 6 of `docs/HASH-PACKAGE-PLAN.md`; its own gate audits it
there, and nothing under a dependency is inspected here. -/
def auditedTrees : List Name :=
  [`Whatwg, `WhatwgTest, `WhatwgGates] -- R-V3(c), 2026-10-01

/-- Ruling R-11's ceiling, Lean's standard base, binding every audited tree. -/
def repositoryCeiling : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Ruling R-V1's strict ceiling, binding every constant whose module is under a
prefix of `strictCeilingPrefixes`. -/
def strictCeiling : List Name :=
  [``propext, ``Quot.sound]

/-- Module prefixes under the strict ceiling (ruling R-V1). A prefix joins when
its measured residue, the constants under it that reach `Classical.choice`, is
zero or wholly covered by exact exceptions the coordinator accepts as debts.
Adding a prefix is one line; the build then fails with one error per residue
declaration, which is the measurement.

The five prefixes below have zero residue at the lane V landing; `Whatwg.Streams`
joined at integration, with the R-V5 repair. `Whatwg.Html.Print` and the
`String`-borne definitions of `Whatwg.Infra.{Namespaces,Text.Scalar,Text.String}`
stay under R-11: they reach `Classical.choice` through core's `String` API. A
prefix must lie inside the `Whatwg` tree, since R-V1 keeps `WhatwgTest` and
`WhatwgGates` under R-11, and must cover at least one audited module, so that a
misspelt prefix cannot make the strict ceiling vacuous. -/
def strictCeilingPrefixes : List Name :=
  [ `Whatwg.Ecma262
  , `Whatwg.WebIdl
  , `Whatwg.Url
  , `Whatwg.Infra.Text.Utf8
  , `Whatwg.Streams
  ]

/-- Exact strict-ceiling exceptions, one declaration each, written
`` ⟨`Full.Name, "reason"⟩ :: `` on its own line below the anchor comment, where
`lake exe whatwg_trustselftest` plants its entries too. The gate refuses an
entry that names no declaration, one whose module is under no strict prefix,
one whose declaration does not reach `Classical.choice`, one with a blank
reason, and one listed twice. Empty at the V2 landing. -/
def strictCeilingExceptions : List StrictCeilingException :=
  -- trust-selftest: strict-ceiling exception entries are inserted below this line
  []

/-- Private strict-ceiling exceptions. Each must resolve to exactly one audited
declaration and then passes the same checks as `strictCeilingExceptions`.
Empty at the V2 landing. -/
def privateStrictCeilingExceptions : List PrivateStrictCeilingException :=
  []

/-- Source-token exemptions by exact module name, written
`` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor comment. The
gate refuses an entry that names no audited module source, one that names an
entry point under `whatwgbin/` (none can be exempted), one whose source carries
no refused word in code, one with a blank reason, and one listed twice. Empty at
the V2 landing: the gate spells its word lists as literals. -/
def sourceTokenExemptions : List SourceTokenExemption :=
  -- trust-selftest: source-token exemption entries are inserted below this line
  []

/-- Metaprogramming modules by exact module name (ruling R-V10, addendum V2c.2),
written `` ⟨`Full.Module, "reason"⟩ :: `` on its own line below the anchor
comment, where `lake exe whatwg_trustselftest` plants its entries too. The gate
refuses an entry that names no audited module source, one whose source spells no
metaprogramming keyword and whose module registers nothing, one with a blank
reason, one listed twice, and one that names an entry point under `whatwgbin/`.
It holds eleven modules: the eight that declare a `#…` gate command, the two
constructive-contract batteries that run a receipt in `run_cmd` (both groups
since the V2c landing), and, since the W6 landing (ruling R-W7(b), addendum
V2d), `WhatwgTest.Audit.Freeze`, which declares the registry command
`#whatwg_freeze`. A battery that only uses that command registers nothing and
needs no entry. The list moved here from `WhatwgTest/Audit/AxiomGate.lean` with
the factor of addendum V2e.3, entries and reasons unchanged; the gate library
lists no module of its own. -/
def metaprogrammingModules : List MetaprogrammingModule :=
  -- trust-selftest: metaprogramming-module entries are inserted below this line
  ⟨`WhatwgTest.Audit.Freeze, "declares the registry command #whatwg_freeze with syntax and command_elab"⟩ ::
  ⟨`WhatwgTest.Audit.AxiomGate, "declares this gate's command and elaborator, and its post-command linters with initialize (V2c.5)"⟩ ::
  ⟨`WhatwgTest.Audit.SpecCoverage, "declares the gate command #spec_coverage_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.CensusProfileIdentity, "declares the gate command #census_profile_identity_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.WebIdl.CensusContract, "declares the gate command #webidl_census_contract_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.WebIdl.CensusQ2Contract, "declares the gate command #webidl_census_q2_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.CensusContract, "declares the gate command #ecma262_census_contract_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.CensusQ2Contract, "declares the gate command #ecma262_census_q2_gate with elab"⟩ ::
  ⟨`WhatwgTest.Audit.Ecma262.EcmarkupScanner, "declares the gate command #ecmarkup_scanner_gate with elab"⟩ ::
  ⟨`WhatwgTest.Infra.IntegerConstructiveContract, "runs receipt INFRA-INTEGER-CE-001 in run_cmd: Lean.collectAxioms over nine range proofs"⟩ ::
  ⟨`WhatwgTest.Infra.ScalarConstructiveContract, "runs receipt INFRA-SCALAR-CE-001 in run_cmd: Lean.collectAxioms over nine declarations"⟩ ::
  []

/-- This repository's configuration of the trust gate: the one value the in-tree
command and the executable gate hand the gate library. -/
def config : Config where
  auditedTrees := auditedTrees
  repositoryCeiling := repositoryCeiling
  strictCeiling := strictCeiling
  strictCeilingPrefixes := strictCeilingPrefixes
  strictCeilingExceptions := strictCeilingExceptions
  privateStrictCeilingExceptions := privateStrictCeilingExceptions
  sourceTokenExemptions := sourceTokenExemptions
  metaprogrammingModules := metaprogrammingModules

end Gates.TrustConfig
