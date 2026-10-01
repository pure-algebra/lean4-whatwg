# Receipts log of `INFRA-PG-SCALAR`

This log holds the history of `docs/INFRA-SCALAR-ASSURANCE.md`. Under ruling R-V4 the V4
documents seat moved each block below out of that document verbatim on
2026-09-30, from commit `325d5d5`, in its original order and under its
original heading. The line under each heading says where the block came
from and is the only line added. The current state of every edge is the
"Current state" section of `docs/INFRA-SCALAR-ASSURANCE.md`.

## Assurance graph: INFRA-PG-SCALAR

Moved verbatim from the edge table of this section of `docs/INFRA-SCALAR-ASSURANCE.md` at `325d5d5`; the section's prose stays there and its "Current state" section supersedes the table.

| Edge | State | Obligation |
| --- | --- | --- |
| identity | `required-open` | Canonical source/carrier and adapter roles are frozen above; join them to the future Infra census and declaration snapshot. |
| construction | `required-closed` | The frozen nine ascriptions pass; checked constructors and all conversion definition bodies are unchanged. |
| semantics | `required-closed` | Independent review matches the two source spans to the canonical range/surrogate definitions and `Char.valid`, including all surrogate boundaries and U+10FFFF. |
| laws | `required-closed` | The general validity helpers and both exact inverse theorems elaborate unchanged; actual constructive receipts are below. |
| representation | `required-closed` | Independent diff review confirms only two helper proof bodies changed; canonical types and runtime conversions are unchanged. |
| counterexamples | `required-closed` | `INFRA-SCALAR-CE-001` was red for six actual choice dependencies at `9cf3216`; all nine frozen checks now pass and remain imported by the common test root. |
| bridges | `required-closed` | Both inverse laws hold over the exact checked scalar and native Char values with the recorded axioms; this says nothing about the separate string adapters. |
| targets | `not-applicable` | No target language, generated code or host implementation is introduced. |
| trust | `required-closed` | All nine declarations meet `[propext, Quot.sound]`; default common audit and repository gates pass. No repository-wide ceiling or exemption changed. |
| coverage | `required-open` | No Infra/URL coverage report or category claim follows from this local proof-term repair; census joins remain open. |

## Proof repair and receipts

Moved verbatim from `docs/INFRA-SCALAR-ASSURANCE.md` at `325d5d5`.

Breaker commit: `9cf32166b59851b8c978ced0a61c71e04eeaa235`, based on
`5e913760043989d8e5096e20067db0ee12b0cde7`. The red run elaborated all nine
ascriptions, then printed and rejected choice in six declarations. There
were no syntax or import failures. The builder changes only the two
authorized proof bodies. They use constructive decisions about natural
number bounds, explicit cases for the two surrogate intervals, and ordinary
arithmetic lemmas. No theorem statement or conversion body changes.

The unchanged frozen battery prints these actual transitive axiom sets:

| Declaration in `Whatwg.Infra` | Axioms |
| --- | --- |
| `CodePoint.char_toNat_le` | `[propext, Quot.sound]` |
| `CodePoint.ofChar` | `[propext, Quot.sound]` |
| `CodePoint.ofChar_isSurrogate` | `[propext, Quot.sound]` |
| `ScalarValue.isValidChar` | none |
| `ScalarValue.toChar` | none |
| `ScalarValue.ofChar` | `[propext, Quot.sound]` |
| `ScalarValue.toNat_ofNatAux` | `[propext]` |
| `ScalarValue.ofChar_toChar` | `[propext, Quot.sound]` |
| `ScalarValue.toChar_ofChar` | `[propext, Quot.sound]` |

`lake build WhatwgTest.Infra.ScalarConstructiveContract` passes all exact
ascriptions and the actual axiom whitelist. `lake build` passes 270 jobs;
the common audit checks 131 modules and 6887 declarations, including 1898
tooling declarations. `lake exe vendorseal`, `lake exe citations`,
`lake exe tyxmlschema`, `lake exe census` and `lake exe urlinventory` pass.
Independent source/signature review and post-red proof review found no
outstanding defect. No frozen breaker file was changed.

This closes the local constructive proof obligations above. Identity and
coverage joins remain open; the full Infra and URL assurance routes are
not closed by this repair. The wider URL reification goal remains active.

## Current-state table as hand-written before the ledger, 2026-10-01

Moved verbatim from the "Current state" section of `docs/INFRA-SCALAR-ASSURANCE.md` at `5999363`; the ledger entry `WhatwgTest/Ledger/InfraScalar.lean` and its projection `generated/graphs/INFRA-PG-SCALAR.md` supersede it.

This table describes commit `325d5d5` on 2026-09-30 for the graph
`INFRA-PG-SCALAR`. No edge has moved since the repair and its independent
review of 2026-09-05, and no ruling in `COORDINATION.md` changes one. Ruling
R-V4 sets the rule: an edge is `required-closed` only when every ground this
document or a ruling states for keeping it open is discharged by something
named in the ground cell.

| Edge | Status | Ground |
| --- | --- | --- |
| identity | `required-open` | The joins of the frozen source, carrier and adapter roles to the Infra census rows and to the generated declaration snapshot, which has no generator (debt D47). The Infra definition census exists (`lake exe whatwg_census --standard infra`) and has no numerator |
| construction | `required-closed` | The nine frozen ascriptions of `WhatwgTest/Infra/ScalarConstructiveContract.lean` pass; checked constructors and all conversion definition bodies are unchanged (receipt "Proof repair and receipts") |
| semantics | `required-closed` | Independent review matched the two source spans to the canonical range and surrogate definitions and `Char.valid`, including all surrogate boundaries and U+10FFFF |
| laws | `required-closed` | The general validity helpers and both exact inverse theorems, `ScalarValue.ofChar_toChar` and `ScalarValue.toChar_ofChar`, elaborate unchanged with constructive receipts |
| representation | `required-closed` | Independent diff review confirmed that only two helper proof bodies changed; canonical types and runtime conversions are unchanged |
| counterexamples | `required-closed` | `INFRA-SCALAR-CE-001` is `CLOSED` in `test/counterexamples/REGISTER.md`: red for six choice dependencies at `9cf3216`, and all nine frozen checks now pass in the common test root |
| bridges | `required-closed` | Both inverse laws hold over the exact checked scalar and native `Char` values with the recorded axioms; this says nothing about the separate string adapters |
| targets | `not-applicable` | No target language, generated code or host implementation is introduced |
| trust | `required-closed` | All nine declarations meet `[propext, Quot.sound]`, checked by `Lean.collectAxioms` in the frozen battery at every build. The two declarations of `Whatwg/Infra/Text/Scalar.lean` and `String.lean` that reach `Classical.choice` at `325d5d5`, `JsString.ofString` and `JsString.ofLiteral`, are string adapters outside this repair fence |
| coverage | `required-open` | No Infra or URL coverage report follows from this proof-term repair; the census joins remain open |
