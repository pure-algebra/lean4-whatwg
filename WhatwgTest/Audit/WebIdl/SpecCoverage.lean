import Gates
import WhatwgTest.Audit.WebIdl.SpecCoverageRows

/-!
# Web IDL specification-coverage numerator

`docs/SPEC-COVERAGE.md` owns the metric; this module is its numerator side for
the `webidl` standard, landed by slice Q2 of `docs/PROMISE-PACKAGE-PLAN.md` and
frozen by section 6 of `test/contracts/webidl-census-q2.contract.md`.

**Claim boundary.** At Q2 every row is `absent` and no row carries a witness.
`emit` is exactly the generated all-`absent` scaffold
`WhatwgTest/Audit/WebIdl/SpecCoverageRows.lean`, which
`lake exe census --standard webidl --write` writes beside
`generated/webidl-census.tsv`, so the row ids and the joined dispositions are
the census's and are not retyped here. The block
`lake exe census --standard webidl --report` prints therefore says that nothing
is proved about `Whatwg.WebIdl`; quoting it as coverage is a defect. Slice Q3 is
where the first witness lands, and until then
`Gates.Census.verifyEmit` refuses a witness on an `absent` row and a
non-`absent` state on a row outside the denominator.

**Why the totals sit here.** `expectedRowTotal` and `expectedDenominator` are
the freeze `WhatwgTest/Audit/SpecCoverage.lean` carries for Streams: a census
change that invalidates them fails this module's elaboration, so it is repaired
in the same edit rather than discovered later. The cost is the one
`Gates/AGENTS.md` records — building the census executable, and so every mode
of it, needs this module to elaborate — and `--write` still does not read an
emit, so a census the numerators have not caught up with is still regenerable.

Unlike the Streams numerator this module reads no file and declares no
theorem, so it stays out of `MetaM` and needs no entry in
`WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`.
-/

namespace WhatwgTest.Audit.WebIdl.SpecCoverage

open Gates.Census

/-- Census rows frozen for this commit; section 4 of the Q2 addendum. -/
def expectedRowTotal : Nat := 124

/-- Rows inside the coverage denominator, that is, rows whose disposition is
not `evidenceOnly`, `refused` or `targetOnly`. -/
def expectedDenominator : Nat := 116

/-- The generated all-`absent` scaffold: one entry per census row, carrying the
census row id and the joined disposition, state `absent`, witness list empty. -/
def rows : Array CoverageRow := SpecCoverageRows.rows

/-- The numerator's rows. At Q2 it is the scaffold unchanged: no state is above
`absent` and no row carries a witness. `bin/Census.lean` hands this to
`Gates.Census.cli` under the key `webidl`, which cross-checks it against a
fresh census regeneration before `--report` prints a number. -/
def emit : Array CoverageRow := rows

/-! ## The freeze

Checked at elaboration: the generated scaffold carries the row total and the
denominator this module records, and every one of its rows is `absent` with no
witness. A census change that invalidates any of the three fails this module,
and so fails the census executable, in the same edit. -/

#guard rows.size == expectedRowTotal

#guard
  (rows.foldl (fun acc row => if row.disposition.excluded then acc else acc + 1) 0)
    == expectedDenominator

#guard rows.all fun row => row.state == CoverageState.absent && row.witnesses.isEmpty

end WhatwgTest.Audit.WebIdl.SpecCoverage
