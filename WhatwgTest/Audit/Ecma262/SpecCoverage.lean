import Gates
import WhatwgTest.Audit.Ecma262.SpecCoverageRows

/-!
# ECMA-262 specification-coverage numerator

`docs/SPEC-COVERAGE.md` owns the metric; this module is its numerator side for
the `ecma262` standard, landed by slice Q2 of `docs/PROMISE-PACKAGE-PLAN.md`
and frozen by section 3 of `test/contracts/ecma262-census-q2.contract.md`.

**Claim boundary.** At Q2 every row is `absent` and no row carries a witness.
`emit` is exactly the generated all-`absent` scaffold
`WhatwgTest/Audit/Ecma262/SpecCoverageRows.lean`, which
`lake exe census --standard ecma262 --write` writes beside
`generated/ecma262-census.tsv`, so the row ids and the joined dispositions are
the census's and are not retyped here. The block
`lake exe census --standard ecma262 --report` prints therefore says that
nothing is proved about `Whatwg.Ecma262`; quoting it as coverage is a defect.
In particular the Q2 move of `clause.promise-objects` from `evidenceOnly` to
`owned` puts that row inside the denominator so that it can be *owed* a
witness; owed is not held, and the row is `absent` here like every other.

**Why the totals sit here.** `expectedRowTotal` and `expectedDenominator` are
the freeze `WhatwgTest/Audit/SpecCoverage.lean` carries for Streams: a census
change that invalidates them fails this module's elaboration, so it is repaired
in the same edit rather than discovered later. `--write` still does not read an
emit, so a census the numerators have not caught up with is still regenerable.

This module reads no file and declares no theorem, so it stays out of `MetaM`
and needs no entry in `WhatwgTest/Audit/AxiomGate.lean`'s
`auditImplementationModules`.
-/

namespace WhatwgTest.Audit.Ecma262.SpecCoverage

open Gates.Census

/-- Census rows frozen for this commit; section 2 of the Q2 addendum leaves the
row total at the Q1 count and moves one row between two dispositions. -/
def expectedRowTotal : Nat := 77

/-- Rows inside the coverage denominator, that is, rows whose disposition is
not `evidenceOnly`, `refused` or `targetOnly`. -/
def expectedDenominator : Nat := 75

/-- The generated all-`absent` scaffold: one entry per census row, carrying the
census row id and the joined disposition, state `absent`, witness list empty. -/
def rows : Array CoverageRow := SpecCoverageRows.rows

/-- The numerator's rows. At Q2 it is the scaffold unchanged: no state is above
`absent` and no row carries a witness. `bin/Census.lean` hands this to
`Gates.Census.cli` under the key `ecma262`, which cross-checks it against a
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

end WhatwgTest.Audit.Ecma262.SpecCoverage
