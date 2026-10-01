# Infra scalar/Char constructive proof record

Status: frozen declaration and trust target; constructive proof repair
verified and independently reviewed, 2026-09-05, base `5e91376`.
This is the constructive dependency repair for
the URL lane's added choice-minimization objective. It does not admit the
wider Infra census or any URL algorithm.

## Current state

The status of every edge of this graph is recorded in the ledger module
`WhatwgTest/Ledger/InfraScalar.lean`, rendered to
`generated/graphs/INFRA-PG-SCALAR.md` by `lake exe whatwg_ledger --write`, and
checked by `lake exe whatwg_ledger`. The table this section held before the
ledger is in `docs/receipts/INFRA-PG-SCALAR.md`.

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
