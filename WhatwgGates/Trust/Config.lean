/-!
# Gates.Trust.Config

The type of one repository's data for the trust gate (addendum V2e.3 of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-W7(a)). This
repository's value is `Gates.TrustConfig.config` in
`WhatwgGates/TrustConfig.lean`. The gate library takes a `Config` as an
argument and imports no configuration, so a plant into the config module
rebuilds the config module and its importers, never the library.

This module declares types only and imports nothing beyond `Init`, so that the
config module, which imports it and nothing else, stays data.
-/

namespace Gates.Trust

open Lean (Name)

/-- An exact admission of one declaration under the strict ceiling to
`Classical.choice`, with the reason the coordinator accepted it as a debt. -/
structure StrictCeilingException where
  declaration : Name
  reason : String

/-- A strict-ceiling exception for a private declaration, identified by its
exact owning module and its original spelling, never by Lean's private-name
counter. -/
structure PrivateStrictCeilingException where
  owner : Name
  original : Name
  reason : String

/-- An exact admission of one module's source to the trust-token pass, and to
no other check, with the reason it must name a refused word in code. -/
structure SourceTokenExemption where
  moduleName : Name
  reason : String

/-- An exact admission of one audited module to rule 1 of addendum V2c, with
the reason it declares syntax, a macro or an elaborator, or runs a metaprogram.
It relaxes the metaprogramming-keyword refusal and the registration refusal for
that module and nothing else: a listed module stays bound by every trust word. -/
structure MetaprogrammingModule where
  moduleName : Name
  reason : String

/-- One repository's data for the trust gate: what it audits, the two
ceilings, and the exact lists, every entry with its reason. Nothing here is
code; every check the data feeds is the library's. -/
structure Config where
  /-- The audited trees, disjoint under `Name.isPrefixOf`, which compares whole
  components. -/
  auditedTrees : List Name
  /-- Ruling R-11's ceiling, binding every audited tree. -/
  repositoryCeiling : List Name
  /-- Ruling R-V1's strict ceiling, binding every constant whose module is under
  a prefix of `strictCeilingPrefixes`. -/
  strictCeiling : List Name
  /-- Module prefixes under the strict ceiling (ruling R-V1). -/
  strictCeilingPrefixes : List Name
  /-- Exact strict-ceiling exceptions, one declaration each. -/
  strictCeilingExceptions : List StrictCeilingException
  /-- Strict-ceiling exceptions for private declarations. -/
  privateStrictCeilingExceptions : List PrivateStrictCeilingException
  /-- Source-token exemptions by exact module name. -/
  sourceTokenExemptions : List SourceTokenExemption
  /-- Metaprogramming modules by exact module name (ruling R-V10). -/
  metaprogrammingModules : List MetaprogrammingModule

end Gates.Trust
