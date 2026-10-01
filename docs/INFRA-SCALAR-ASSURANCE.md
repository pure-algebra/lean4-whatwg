# Infra scalar/Char constructive proof record

Status: frozen declaration and trust target; constructive proof repair
verified and independently reviewed, 2026-09-05, base `5e91376`.
This is the constructive dependency repair for
the URL lane's added choice-minimization objective. It does not admit the
wider Infra census or any URL algorithm.

## Current state

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

## Owner, source and existing representations

The canonical owners remain `Whatwg.Infra.CodePoint` and
`Whatwg.Infra.ScalarValue` in `Whatwg/Infra/Text/CodePoint.lean`.
`ScalarValue` is the existing checked subtype of a code point whose
surrogate predicate is false. No carrier is added or replaced. The existing
`Whatwg/Infra/Text/Scalar.lean` conversions are adapters to and from Lean's
native `Char`, whose validity field excludes the surrogate interval.

The semantic source is the Infra pin owned by `SPEC-MANIFEST.md`:
`vendor/whatwg-infra-3f984adc/infra.bs`. The code-point range/value span is
`[37758,38058)`, SHA-256
`9e64899eeb92c78b78c5ee9cdea0e7aa8fbfd4e0149530b72b245ec4815d5f61`.
The leading/trailing surrogate, surrogate and scalar-value definitions are
`[39322,39741)`, SHA-256
`56d42d081bddac24e9e638109dd6f4ea7fec9a9ade69f6e34523ff09dbd17977`.
These span digests were independently computed from the sealed bytes for
this authored record. The native representation is the installed pinned
Lean 4.33.1 `Char`, not a browser or JavaScript string object.

## Frozen declarations and repair fence

All names below are in `Whatwg.Infra`, owned by the existing Scalar module,
with `owned` disposition for their Infra operation/bridge role. They are
derived helpers or adapters of the canonical carriers above, not duplicate
semantic owners. Constructors and generated proof auxiliaries inherit that
relationship. No signature, definition body, or theorem statement changes;
only the proofs of `CodePoint.ofChar_isSurrogate` and
`ScalarValue.isValidChar` may be replaced by the builder.

```lean
CodePoint.char_toNat_le (c : Char) : c.toNat ≤ 0x10FFFF
CodePoint.ofChar (c : Char) : CodePoint
CodePoint.ofChar_isSurrogate (c : Char) : (CodePoint.ofChar c).isSurrogate = false
ScalarValue.isValidChar (s : ScalarValue) : Nat.isValidChar s.val.val
ScalarValue.toChar (s : ScalarValue) : Char
ScalarValue.ofChar (c : Char) : ScalarValue
ScalarValue.toNat_ofNatAux (n : Nat) (h : n.isValidChar) : (Char.ofNatAux n h).toNat = n
ScalarValue.ofChar_toChar (s : ScalarValue) : ScalarValue.ofChar (ScalarValue.toChar s) = s
ScalarValue.toChar_ofChar (c : Char) : ScalarValue.toChar (ScalarValue.ofChar c) = c
```

The observation is the underlying Unicode number and the exact scalar/Char
values in the two inverse laws. No stream observation mask or host profile
is involved. The laws quantify over all inputs of their stated checked
types; a finite character sample cannot replace them.

The stronger trust target is that every one of these nine declarations has
transitive axioms contained in `[propext, Quot.sound]`. Check their exact
signatures and actual `Lean.collectAxioms` results, including dependencies
in types and generated proofs. `Classical.choice` and all compiler/native
auxiliary axioms fail this local target. Do not change the repository-wide
ceiling, delete a declaration, hide the receipt or weaken its statement to
make this check pass. The initial shortest dependency paths from the two
helper theorems reach their generated `_proof_1_7`, then
`Classical.propDecidable` and `Classical.choice`.

The separate breaker owns `test/contracts/infra-scalar-constructive.contract.md`
and `WhatwgTest/Infra/ScalarConstructiveContract.lean`. It commits the exact
ascriptions and failing trust check before the proof repair, declares the
module in `known-red.txt`, and reports its red cause. The coordinator records
the retained witness as `INFRA-SCALAR-CE-001`. Narrow command:
`lake build WhatwgTest.Infra.ScalarConstructiveContract`.

## Assurance graph: INFRA-PG-SCALAR

The native representation bridge requires a graph. This local record owns
its constructive repair obligations, while the wider Infra census and
declaration-snapshot joins remain open in the Infra plan.

The edge table of this graph is the "Current state" section above; the table
this section held at the repair is in the receipts log.

The `JsString.ofLiteral`, `ofString` and `toString?` adapters are outside
this repair fence. Their string-library dependencies must remain visible
in their own later receipts, even if the scalar helper proofs become
constructive.

## Receipts

`docs/receipts/INFRA-PG-SCALAR.md` holds this record's history, moved there
verbatim under ruling R-V4: the edge table of 2026-09-05 and the section
"Proof repair and receipts", with the breaker commit, the actual transitive
axiom set of each of the nine declarations, the build and gate results and the
review. This document still owns that repair receipt and keeps it in that log,
so references to the repair recorded in `docs/INFRA-SCALAR-ASSURANCE.md`
resolve there. The frozen declarations and the stricter trust target stay in
"Frozen declarations and repair fence" above.
