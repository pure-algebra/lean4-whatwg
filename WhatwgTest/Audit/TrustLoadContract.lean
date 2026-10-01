import WhatwgGates.Trust.Load

/-!
# The trust-gate loader contract (addendum V2e.4)

Frozen RED by the W10 trust breaker seat of review lane W on 2026-10-01, on
branch `review/w10-load-breaker`, stacked on `review/w10-trust-breaker`
(rulings R-W7 and R-W9). The contract is addendum V2e.4 of
`test/contracts/trust-gate-hardening.contract.md`; this battery is its
executable half for the loader, `WhatwgGates/Trust/Load.lean`, which the
executable trust gate, `whatwg_declsnapshot` and `whatwg_ledger` share.

The battery is red only because the module it imports does not exist yet. It
is declared in `test/fixtures/trust-gate/known-red.txt`; the loader's builder
removes that entry and adds this module's root import the moment it is green.
A builder may repair elaboration without changing an ascription, a sample or
an expected value; turning the battery green by weakening one is a refusal,
not a landing.

Two parts:

1. the exact ascription of every public signature V2e.4 freezes; and
2. `#guard` rows for the loader's pure parts, `parseTrace`,
   `TraceRecord.recordedOptions` and `leanBuildDir`, over traces measured at
   the base with Lake 5.0.0: the trace of the umbrella module `Whatwg` as
   `lake build` wrote it (the build log's command line and the source's
   absolute path shortened, nothing else changed), the same module built with
   `moreLeanArgs` and with the library's own `leanOptions` (rows V2e-O2 and
   V2e-O3 of the addendum plant the same settings), and malformed texts.

A `#guard` is a finite executable probe evaluated by compiled code
(V2c.7 of the contract): it pins the parse on these inputs and claims nothing
beyond them.
-/

namespace WhatwgTest.Audit.TrustLoadContract

/-! ## Frozen public signatures -/

#check (@Gates.Trust.leanBuildDir : System.FilePath → System.FilePath)
#check (@Gates.Trust.loaderSearchPath :
  System.FilePath → System.FilePath → IO System.SearchPath)
#check (@Gates.Trust.initLoaderSearchPath : System.FilePath → IO Unit)
#check (@Gates.Trust.sourceModules :
  System.FilePath → List Lean.Name → IO (Array Lean.Name))
#check (@Gates.Trust.importBuilt : Array Lean.Name → IO Lean.Environment)
#check (@Gates.Trust.moduleDeclarations : Lean.Environment → Nat → Array Lean.Name)
#check (@Gates.Trust.rawEntries :
  Lean.Environment → Nat → Lean.Name → Array Lean.EnvExtensionEntry)
#check (@Gates.Trust.extensionsWithEntries :
  Lean.Environment → Nat → Array (Lean.Name × Nat))
#check (@Gates.Trust.TraceRecord.mk :
  Lean.Name → String → Array String → Array String → Array (String × String) →
    Gates.Trust.TraceRecord)
#check (@Gates.Trust.TraceRecord.moduleName : Gates.Trust.TraceRecord → Lean.Name)
#check (@Gates.Trust.TraceRecord.sourceHash : Gates.Trust.TraceRecord → String)
#check (@Gates.Trust.TraceRecord.options : Gates.Trust.TraceRecord → Array String)
#check (@Gates.Trust.TraceRecord.leanArgs : Gates.Trust.TraceRecord → Array String)
#check (@Gates.Trust.TraceRecord.libs :
  Gates.Trust.TraceRecord → Array (String × String))
#check (@Gates.Trust.parseTrace : String → Except String Gates.Trust.TraceRecord)
#check (@Gates.Trust.TraceRecord.recordedOptions :
  Gates.Trust.TraceRecord → Array String)
#check (@Gates.Trust.sourceHash : System.FilePath → IO String)
#check (@Gates.Trust.traceOf :
  System.FilePath → System.FilePath → Lean.Name → IO (Bool × Array String))

/-! ## Measured traces -/

/-- The trace head every sample shares: outputs, a shortened build log, and the
`deps` and `libs` inputs of the umbrella module `Whatwg` at the base. -/
def traceHead : String :=
  "{\"synthetic\": false,\n \"schemaVersion\": \"2025-09-10\",\n" ++
  " \"outputs\":\n {\"o\": [\"6a181fbaf6175dec.olean\"],\n  \"m\": false,\n" ++
  "  \"i\": \"6d7bde8ccf17db79.ilean\",\n  \"c\": \"a5fae806ed269575.c\"},\n" ++
  " \"log\":\n [{\"message\": \".> lean.exe /probe/Whatwg.lean --json\",\n" ++
  "   \"level\": \"trace\"}],\n" ++
  " \"inputs\":\n [[\"deps\",\n" ++
  "   [[\"whatwg/Whatwg:extraDep\"," ++
  " [[\"@whatwg:extraDep\", \"00000000000006bb\"]]],\n" ++
  "    [\"imports\",\n" ++
  "     [[\"Whatwg.Infra transitive imports (legacy)\", \"ac0f4277d85c12de\"],\n" ++
  "      [\"Whatwg.Infra:importAllArts\", \"3e25923a1e63a0bd\"],\n" ++
  "      [\"Whatwg.Url transitive imports (legacy)\", \"e21e8f8b5d798b7e\"],\n" ++
  "      [\"Whatwg.Url:importAllArts\", \"77895bcffb2ef69c\"]]]]],\n" ++
  "  [\"libs\",\n" ++
  "   [[\"import dynlibs\", \"00000000000006bb\"],\n" ++
  "    [\"package external libraries\", \"00000000000006bb\"],\n" ++
  "    [\"module dynlibs\", \"00000000000006bb\"],\n" ++
  "    [\"module plugins\", \"00000000000006bb\"]]],\n" ++
  "  [\"Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6\",\n" ++
  "   \"0051240b7c23c453\"],\n" ++
  "  [\"/probe/Whatwg.lean\",\n   \"dad9acc4a8b1bba6\"],\n"

/-- The `options` input of the package's `leanOptions`, as every audited module
records it at the base. -/
def packageOptions : String :=
  "  [\"options\",\n" ++
  "   [[\"-DwarningAsError=true\", \"a61e1d61617d04e8\"],\n" ++
  "    [\"-DrelaxedAutoImplicit=false\", \"74a2b5546b55be80\"],\n" ++
  "    [\"-DautoImplicit=false\", \"4a85acb881fd49d0\"]]],\n"

/-- The trace tail: the module's flags, its name and its `leanArgs` label. -/
def traceTail (leanArgsLabel : String) : String :=
  "  [\"isModule: false\", \"feefd2a0d3a1847e\"],\n" ++
  "  [\"Module.name: Whatwg\", \"d65fc0cd0fa64214\"],\n" ++
  "  [\"Package.id?: (some whatwg)\", \"ec66aaa2bec4c383\"],\n" ++
  "  [\"" ++ leanArgsLabel ++ "\", \"00000000000006bb\"]],\n" ++
  " \"depHash\": \"fa5ff3bfe45a7157\"}"

/-- The base trace of `Whatwg`. -/
def baseTrace : String :=
  traceHead ++ packageOptions ++ traceTail "Module.leanArgs: #[]"

/-- The same module built with `moreLeanArgs` (row V2e-O2's settings, with
`-DwarningAsError=false` added). -/
def moreLeanArgsTrace : String :=
  traceHead ++ packageOptions ++ traceTail
    ("Module.leanArgs: #[-DwarningAsError=false, -Ddebug.skipKernelTC=true, " ++
      "-Dwarn.sorry=false, -j1]")

/-- The same module built with the library's `leanOptions = { warningAsError =
false }` (row V2e-O3): the library's value replaces the package's. -/
def libraryOptionsTrace : String :=
  traceHead ++
  "  [\"options\",\n" ++
  "   [[\"-DwarningAsError=false\", \"19509ee60cb6b1e0\"],\n" ++
  "    [\"-DrelaxedAutoImplicit=false\", \"74a2b5546b55be80\"],\n" ++
  "    [\"-DautoImplicit=false\", \"4a85acb881fd49d0\"]]],\n" ++
  traceTail "Module.leanArgs: #[]"

/-- Whether a text parses, and the parsed record passes `check`. -/
def parsesTo (text : String) (check : Gates.Trust.TraceRecord → Bool) : Bool :=
  match Gates.Trust.parseTrace text with
  | .ok record => check record
  | .error _ => false

/-- Whether a text is refused. -/
def refused (text : String) : Bool :=
  match Gates.Trust.parseTrace text with
  | .ok _ => false
  | .error _ => true

/-! ## `parseTrace` and `recordedOptions` on measured traces -/

#guard parsesTo baseTrace (·.moduleName == `Whatwg)
#guard parsesTo baseTrace (·.sourceHash == "dad9acc4a8b1bba6")
#guard parsesTo baseTrace (·.options ==
  #["-DwarningAsError=true", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false"])
#guard parsesTo baseTrace (·.leanArgs == #[])
#guard parsesTo baseTrace (·.libs ==
  #[("import dynlibs", "00000000000006bb"),
    ("package external libraries", "00000000000006bb"),
    ("module dynlibs", "00000000000006bb"),
    ("module plugins", "00000000000006bb")])
#guard parsesTo baseTrace (·.recordedOptions ==
  #["-DwarningAsError=true", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false"])

#guard parsesTo moreLeanArgsTrace (·.leanArgs ==
  #["-DwarningAsError=false", "-Ddebug.skipKernelTC=true", "-Dwarn.sorry=false",
    "-j1"])
#guard parsesTo moreLeanArgsTrace (·.recordedOptions ==
  #["-DwarningAsError=true", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false",
    "-DwarningAsError=false", "-Ddebug.skipKernelTC=true", "-Dwarn.sorry=false"])
#guard parsesTo moreLeanArgsTrace (·.sourceHash == "dad9acc4a8b1bba6")

#guard parsesTo libraryOptionsTrace (·.options ==
  #["-DwarningAsError=false", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false"])
#guard parsesTo libraryOptionsTrace (·.recordedOptions ==
  #["-DwarningAsError=false", "-DrelaxedAutoImplicit=false", "-DautoImplicit=false"])

/-! ## Refusals: not JSON, no inputs, no module name, not one source -/

#guard refused "not a trace"
#guard refused "{}"
#guard refused "{\"inputs\": 3}"
#guard refused (traceHead ++ packageOptions ++
  "  [\"Module.leanArgs: #[]\", \"00000000000006bb\"]]}")
#guard refused (traceHead ++ "  [\"/probe/Other.lean\", \"0123456789abcdef\"],\n" ++
  packageOptions ++ traceTail "Module.leanArgs: #[]")
#guard refused ("{\"inputs\": [[\"Module.name: Whatwg\", \"d65fc0cd0fa64214\"]]}")
#guard refused (traceHead ++ "  [\"options\", \"0123456789abcdef\"],\n" ++
  traceTail "Module.leanArgs: #[]")

/-! ## `leanBuildDir` -/

#guard Gates.Trust.leanBuildDir "root" ==
  ("root" : System.FilePath) / ".lake" / "build" / "lib" / "lean"

end WhatwgTest.Audit.TrustLoadContract
