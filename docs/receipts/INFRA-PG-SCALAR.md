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
