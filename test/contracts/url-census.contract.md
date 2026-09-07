# URL source-to-census assignment contract (U2b)

Status: FROZEN / RED, independent breaker process, 2026-09-05.

The declaration record and acceptance authority is
`docs/URL-CENSUS-INTERFACE.md`. This packet freezes the finite executable
battery in `WhatwgTest/Url/CensusContract.lean` before implementation of
`Gates.UrlCensus`. The builder may repair elaboration but must not weaken,
delete, or replace a frozen input, output, or acceptance condition.

## Ownership and claim boundary

The single production owner is `Gates.UrlCensus.assign`. It joins authored
source rows and explanations to every candidate returned by the existing
`Gates.UrlInventory.scan`. `SourceRow` adapts the existing canonical
`Gates.Census.Row` and `Gates.Census.Disposition`; `Explanation` records an
authored explanatory region; `Assignment` is a derived candidate view.
These are tooling declarations with the relationship and assurance records
in the interface. They introduce no second URL semantic carrier.

The WHATWG URL source pin remains owned by `SPEC-MANIFEST.md`; the separate
authored semantic-source review is recorded in `docs/URL-SOURCE-REVIEW.md`.
This battery uses small, literal source fixtures. It checks the join's
acceptance conditions without granting any classification to the pinned
standard and without claiming that the assigned spans contain all normative
meaning. It establishes no URL execution observation mask, host result,
coverage denominator, or semantic theorem.

Its finite evidence contributes to the open `URL-PG-CENSUS` graph in
`docs/URL-CENSUS-DAG.md`. Source review, fixed-pin classification,
deterministic projection, per-declaration assurance joins and the
numerator/report integration retain their own obligations after these
probes pass.

## Frozen declaration

The battery uses this exact, fully qualified ascription:

```lean
#check (@Gates.UrlCensus.assign : ByteArray → Array Gates.UrlCensus.SourceRow →
  Array Gates.UrlCensus.Explanation → Array String →
  Except String (Array Gates.UrlCensus.Assignment))
```

The interface record is the single owner of the row ID, anchor, UTF-8 span,
origin, interval-forest, dependency, explanation and assignment rules. This
packet's test expectations instantiate those rules rather than duplicating
their definition. The input supplies no candidate array, so it cannot
silently select a truncated inventory. Error wording is not frozen;
rejection means `Except.error`.

Every fixture source row explicitly supplies its canonical row fields,
disposition, parent, dependencies and origins. Success expectations compare
complete `Assignment` records: candidate kind, byte start/end, label and
section, plus owner and reason. Expected byte offsets are independently
fixed literal numbers; no production scanner, label helper, row search or
span finder computes an expected result. The explanation reason is compared
verbatim, including its intentional whitespace.

## Finite acceptance and rejection groups

The executable witnesses live once in the Lean battery. These IDs identify
preimplementation acceptance groups, not discovered semantic counterexamples.
If a witness changes a declaration or cutover decision, the coordinator
registers the concrete case in `test/counterexamples/REGISTER.md` and links
the retained source.

| Probe | Frozen cases |
| --- | --- |
| `URL-CEN-P01` | Empty and plain-text success; one owned definition; disjoint rows with reversed authored order still produce scanner order; host-only disposition retains ownership; a candidate with no owner or explanation fails. |
| `URL-CEN-P02` | Structural headings, explained prose and semantic definitions all retained; explanation may surround a semantic row; adjacent explanations; verbatim reason; a heading may instead belong to a semantic row; missing prose ownership fails. |
| `URL-CEN-P03` | Three-level immediate-parent forest selects the smallest containing owner; one algorithm row retains algorithm and definition candidates as distinct origins. |
| `URL-CEN-P04` | Reject unused semantic/heading/suffix explanatory regions, overlapping or equal regions, blank/whitespace reasons, empty/reversed/out-of-input regions. |
| `URL-CEN-P05` | Reject empty IDs, empty suffixes, missing or wrong kind prefixes and duplicate row IDs. |
| `URL-CEN-P06` | Valid Unicode byte offsets; reject empty/out-of-range row spans, misplaced/empty/out-of-span/repeated anchors, a span or anchor splitting UTF-8, an explanatory region splitting UTF-8, malformed input UTF-8 and scanner errors. |
| `URL-CEN-P07` | Reject empty, zero, missing, repeated or outside origins; reject cross-row origin duplication and a unique parent origin ultimately assigned to a nested child. |
| `URL-CEN-P08` | Reject crossing/equal row spans, absent or non-immediate parents, root parent, self/missing/cyclic parents and a parent pointer inventing disjoint containment. |
| `URL-CEN-P09` | Accept mutual row dependencies and a used external identity; reject unresolved/duplicate/self dependencies and unused/duplicate/empty/colliding external identities. |

The source spans in the valid three-level fixture have strictly separated
endpoints, so the probe adds no convention about shared endpoints beyond
the interface. Adjacent disjoint rows and explanations are separately tested.
The dependency-cycle success is intentional: dependency identities do not
inherit the acyclicity requirement of the parent forest.

All assertions are finite `#guard` executable probes, and all test helpers
are private. They introduce no theorem about arbitrary inputs and no added
proof axiom. These checks do not audit the semantic justification of an
explanation or a dependency's external API, pin or assurance route.

## Fence and verification

Frozen breaker files:

- `test/contracts/url-census.contract.md`
- `WhatwgTest/Url/CensusContract.lean`

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entry
`WhatwgTest.Url.CensusContract`. The builder removes that entry immediately
after the battery becomes green. No previous frozen battery is modified.
The breaker edits no implementation, authored fixed-pin row data, central
counterexample register, vendored bytes, or generated projection.

Narrow command:

```text
lake build WhatwgTest.Url.CensusContract
```

The preimplementation red cause is the absent `Gates.UrlCensus` module.
That run cannot elaborate the downstream probes; the builder must run them
after adding the implementation. The breaker handoff records the actual
command result, commit and stopped Lake process. After the narrow battery
passes, the coordinator runs the default build, actual axiom receipt and
repository gates. No axiom receipt is claimed during the missing-module
red phase, and passing these finite probes does not close the U2 graph.
