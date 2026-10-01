/-!
# Gates.Trust.Report

The findings and the report of the trust gate (addendum V2e of
`test/contracts/trust-gate-hardening.contract.md`, ruling R-W7(a)).

A finding is one diagnostic line. Every pass of the gate library returns its
findings as `String`s, in the order it finds them, and the host prints each
verbatim: the in-tree command `#whatwg_streams_axiom_gate` logs each as one
error, and the executable gate is to print each as one line. The texts are the
contract's frozen fragments, letter for letter (sections 4, 6, V2b.3 and V2c.2
to V2c.6). A token pass first records a `TokenHit` at a `SourcePosition` and
words its finding from it. A run with no finding reports the counts of
`Summary`, which `Summary.line` prints in the template of the contract's
section 7.

This module declares data and one printer, and imports nothing beyond `Init`.
-/

namespace Gates.Trust

/-- A position in a source, one-based in both coordinates, as diagnostics print it. -/
structure SourcePosition where
  line : Nat
  column : Nat

/-- One refused token of one source, at a one-based line and column. -/
structure TokenHit where
  word : String
  line : Nat
  column : Nat

def SourcePosition.hit (position : SourcePosition) (word : String) : TokenHit :=
  { word, line := position.line, column := position.column }

/-- The counts of the summary line (contract section 7), in its order. -/
structure Summary where
  sourceCount : Nat
  declarationCount : Nat
  whatwgReached : Nat
  whatwgTotal : Nat
  testReached : Nat
  testTotal : Nat
  gatesReached : Nat
  gatesTotal : Nat
  prefixCount : Nat
  exceptionCount : Nat
  exemptionCount : Nat

/-- The summary line: one line, counts only, in the template of contract
section 7. -/
def Summary.line (summary : Summary) : String :=
  s!"Whatwg module and axiom gate: checked {summary.sourceCount} source files and {summary.declarationCount} declarations; Classical.choice is reached by {summary.whatwgReached} of {summary.whatwgTotal} declarations in Whatwg, {summary.testReached} of {summary.testTotal} in WhatwgTest and {summary.gatesReached} of {summary.gatesTotal} in WhatwgGates; strict ceiling propext and Quot.sound over {summary.prefixCount} module prefix(es) with {summary.exceptionCount} exact exception(s); {summary.exemptionCount} source-token exemption(s)" -- R-V3(c), 2026-10-01

end Gates.Trust
