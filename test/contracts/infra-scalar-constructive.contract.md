# Infra scalar/Char constructive proof contract

Status: FROZEN / RED, independent breaker process, 2026-09-05, based on
`5e913760043989d8e5096e20067db0ee12b0cde7`.

The declaration, source and assurance authority is
`docs/INFRA-SCALAR-ASSURANCE.md`. The executable frozen contract and retained
`INFRA-SCALAR-CE-001` witness live in
`WhatwgTest/Infra/ScalarConstructiveContract.lean`. The coordinator records
the stable counterexample centrally in `test/counterexamples/REGISTER.md`.

## Fixed carriers, statements and observations

The canonical representations remain `Whatwg.Infra.CodePoint` and
`Whatwg.Infra.ScalarValue`. Their existing Scalar-module adapters connect
checked scalar values to the pinned Lean 4.33.1 `Char`. No new carrier,
adapter, definition body, theorem statement or public signature is admitted
by this repair. The semantic anchors and digests are owned by the assurance
record at the Infra source pin in `SPEC-MANIFEST.md`.

The battery independently ascribes all nine existing declarations with their
fully qualified types:

| Declaration in `Whatwg.Infra` | Frozen obligation |
| --- | --- |
| `CodePoint.char_toNat_le` | Every native character's number is at most `0x10FFFF`. |
| `CodePoint.ofChar` | Existing `Char → CodePoint` adapter. |
| `CodePoint.ofChar_isSurrogate` | Its surrogate predicate equals `false` for every `Char`. |
| `ScalarValue.isValidChar` | Every checked scalar's number satisfies `Nat.isValidChar`. |
| `ScalarValue.toChar` | Existing `ScalarValue → Char` adapter. |
| `ScalarValue.ofChar` | Existing `Char → ScalarValue` adapter. |
| `ScalarValue.toNat_ofNatAux` | `Char.ofNatAux` returns the number supplied with its validity proof. |
| `ScalarValue.ofChar_toChar` | Exact general inverse law on `ScalarValue`. |
| `ScalarValue.toChar_ofChar` | Exact general inverse law on `Char`. |

The Lean ascriptions are the exact statement authority for this packet;
the descriptions above do not replace them. The observations are the
underlying Unicode number and the exact checked scalar/Char values in the
inverse laws. No stream mask or host profile is involved. Character samples
cannot replace the universally quantified statements.

## INFRA-SCALAR-CE-001 — choice enters validity proofs

The reviewed proof terms of `CodePoint.ofChar_isSurrogate` and
`ScalarValue.isValidChar` reach generated proof auxiliaries, then
`Classical.propDecidable` and `Classical.choice`. The conversions and
inverse theorems inherit that dependency. This violates the stronger local
trust target fixed for the user's choice-minimization objective.

The frozen check calls the actual `Lean.collectAxioms` for each of the nine
ascribed declarations. It prints every returned transitive axiom set and
rejects every name outside `[propext, Quot.sound]`. It collects all offenders
before raising an error, so the red receipt names the full affected set.
There is no diagnostic-text matching, swallowed expected error, hard-coded
axiom receipt, or source-only search in this acceptance check.

The whitelist rejects `Classical.choice` and every other unlisted axiom,
including compiler/native proof auxiliaries. It checks dependencies in both
types and declaration values through Lean's collector. It imposes no
stronger axiom claim on the audit implementation itself or on any unlisted
declaration. The repository-wide ceiling is unchanged.

## Builder fence and assurance route

The builder may change only the proof bodies of
`CodePoint.ofChar_isSurrogate` and `ScalarValue.isValidChar` in
`Whatwg/Infra/Text/Scalar.lean`, under the assurance record's claim. It must
retain all nine signatures and the conversion definition bodies. The
breaker packet and acceptance check must not be weakened, deleted or hidden
to obtain a passing receipt.

This packet contributes to `INFRA-PG-SCALAR` in the assurance record. Its
trust receipt is about the actual proof dependencies of the named general
statements, not a finite character probe. Semantic-source review, unchanged
representation review, ordinary repository gates and future census and
declaration-snapshot joins remain separate obligations. In particular,
`JsString.ofLiteral`, `ofString` and `toString?` remain outside the repair
fence, with their dependencies visible in later receipts.

## Breaker files and verification

Frozen breaker files:

- `test/contracts/infra-scalar-constructive.contract.md`
- `WhatwgTest/Infra/ScalarConstructiveContract.lean`

`test/fixtures/trust-gate/known-red.txt` declares
`WhatwgTest.Infra.ScalarConstructiveContract` while the check is red. The
builder removes that entry immediately after the constructive receipt
passes and imports the retained battery from the test root.

The exclusive narrow red/green command is:

```text
lake build WhatwgTest.Infra.ScalarConstructiveContract
```

The initial run must elaborate all exact ascriptions and fail on the actual
unlisted transitive axiom, naming `Classical.choice` and every affected
declaration. Missing imports or syntax errors do not establish this witness.
The breaker handoff records the commit, exact output and stopped Lake run.
The coordinator owns implementation repair, independent review, the default
build and repository gates after the narrow check becomes green.
