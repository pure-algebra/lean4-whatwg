# Infra scalar/Char constructive proof record

Status: frozen declaration and trust target; constructive proof repair
verified and independently reviewed, 2026-09-05, base `5e91376`.
This is the constructive dependency repair for
the URL lane's added choice-minimization objective. It does not admit the
wider Infra census or any URL algorithm.

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

The `JsString.ofLiteral`, `ofString` and `toString?` adapters are outside
this repair fence. Their string-library dependencies must remain visible
in their own later receipts, even if the scalar helper proofs become
constructive.

## Proof repair and receipts

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
