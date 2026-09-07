# Infra integer constructive proof record

Status: frozen before independent breaker; proof repair verified,
2026-09-05, base `8a2b608`.
The user has paused URL implementation to remove `Classical.choice` first.
This record freezes a proof-only repair of the nine existing range theorems
in `Whatwg/Infra/Primitive/Integer.lean`. No carrier, signature, theorem
statement, runtime definition or existing docstring changes.

## Existing owners and source

The canonical Infra aliases remain `Unsigned8`, `Unsigned16`, `Unsigned32`,
`Unsigned64`, `Unsigned128`, `Signed8`, `Signed16`, `Signed32`, `Signed64`.
Their native representations remain `UInt8`, `UInt16`, `UInt32`, `UInt64`,
`BitVec 128`, `Int8`, `Int16`, `Int32`, `Int64`, respectively. The ownership
decision is INFRA-R11 in `docs/INFRA-PROOF-PLAN.md`. They have `owned`
disposition as Infra's fixed-width carrier views; no duplicate type is added.
Their `.inRange` theorems are derived helpers of those canonical aliases.
Generated proof auxiliaries inherit the same role and trust requirement.

The semantic owner is section `numbers` of the pinned Infra source in
`SPEC-MANIFEST.md`. The exact ranges below are anchored to raw UTF-8 bytes
in `vendor/whatwg-infra-3f984adc/infra.bs`; hashes were independently
computed with Python `hashlib.sha256` over those slices.

| Alias in `Whatwg.Infra` | Inclusive bounds of `toNat` or `toInt` | Span | SHA-256 |
| --- | --- | --- | --- |
| `Unsigned8` | 0, 255 | `[31511,31636)` | `ef07293052e27ebf9c243c3538e5132c7a3607ce2c167c0e20da2ba6501fad7d` |
| `Unsigned16` | 0, 65535 | `[31638,31766)` | `5525e7ebb296555c9093636260e8dfe2b4c0ce197c0d7df7a3296a315e6f63d1` |
| `Unsigned32` | 0, 4294967295 | `[31768,31901)` | `fb26f268fca7f212e7134dae6d3a1cc49f4d1be3337a93053efbc5265852f611` |
| `Unsigned64` | 0, 18446744073709551615 | `[31903,32046)` | `59a70d755b4eac528523699e797bc6f895a4d74f891587ee79da1be9106971cb` |
| `Unsigned128` | 0, 340282366920938463463374607431768211455 | `[32048,32212)` | `16c93346fdd13db360e0334fff696b144e7f8e4c9568ea89ffcc5bdea4afb000` |
| `Signed8` | -128, 127 | `[32335,32486)` | `b63fee5cd0be3310397ddf3440d48d7e525cf771651f0df826da671ef006f75d` |
| `Signed16` | -32768, 32767 | `[32488,32645)` | `837913a164dec4cf5bbdb05da64a2ef3c44f511f6ce04e3c2963300993d71598` |
| `Signed32` | -2147483648, 2147483647 | `[32647,32814)` | `386edf12291b92ef1e30dfa0752d5156996ff7f78a18a47a9c86a9d018f8e806` |
| `Signed64` | -9223372036854775808, 9223372036854775807 | `[32816,33001)` | `e77680f36961b0367fb96d44531245627cf0f04f3762a4131c094b00d3bc2c73` |

For each alias `T`, the exact existing public statement is
`T.inRange (x : T) : lower ≤ x.toNat ∧ x.toNat ≤ upper` for unsigned
types, or the same conjunction over `x.toInt` for signed types, with the
literal bounds above. All nine quantifiers, conjunctions and inclusive
bounds remain fixed. Their observation is the native numeric value of an
arbitrary input; no host or stream observation mask applies.

## Frozen trust target and assurance route

The standalone leaf receipt `INFRA-LF-INTEGER` covers these existing
nonrecursive fixed-width carrier views and their local range facts. This
repair adds no admission function, operational judgment, interpreter,
composition or cross-language equivalence. Wider Infra identity and
coverage joins remain open; this leaf cannot close those joins.

The breaker freezes exact ascriptions of all nine theorems and inspects
their actual transitive axioms with `Lean.collectAxioms`. Every theorem
must have an axiom set contained in `[propext, Quot.sound]`, including
dependencies in statements and generated proofs. The initial audit found
`Classical.choice` in all nine proofs and nine generated auxiliaries.
Only the nine proof bodies are in the builder fence. The existing theorem
types and all aliases remain byte-for-byte unchanged. A weaker statement,
deleted theorem, new axiom, audit exemption or renamed replacement cannot
satisfy the packet.

The separate breaker owns `test/contracts/infra-integer-constructive.contract.md`
and `WhatwgTest/Infra/IntegerConstructiveContract.lean`, commits the packet
and known-red entry before repair, and reports the actual red result.
The retained witness ID is `INFRA-INTEGER-CE-001`. Narrow command:
`lake build WhatwgTest.Infra.IntegerConstructiveContract`.

Closure requires all frozen signatures and constructive receipts, the
default build, repository gates and independent proof/source review.
No full choice-removal claim follows from this local repair.

## Repair and verification receipt

Breaker commit `d755ba63fa82d691f3629fae61804dcdbb6dec58` first elaborated
all nine alias equalities and exact theorem signatures, then rejected all
nine actual choice dependencies. The builder changed only those nine proof
bodies. Unsigned bounds use the native natural-number upper bound directly.
Signed proofs unfold the native numeric interpretation, split its two
branches and construct the conjunction before solving the arithmetic leaves.
This avoids the choice dependencies of the stock signed bound lemmas too.

| Proofs | Actual transitive axioms |
| --- | --- |
| `Unsigned8.inRange`, `Unsigned16.inRange`, `Unsigned32.inRange`, `Unsigned64.inRange`, `Unsigned128.inRange` | none |
| `Signed8.inRange`, `Signed16.inRange`, `Signed32.inRange`, `Signed64.inRange` | `[propext, Quot.sound]` |

`lake build WhatwgTest.Infra.IntegerConstructiveContract` passes unchanged;
the retained module is imported by the test root and its known-red entry
is removed. `lake build` passes all 278 jobs; the common audit checks 135
modules and 7015 declarations, including 1966 tooling declarations.
`lake exe vendorseal`, `citations`, `tyxmlschema`, `census`, `urlinventory`
and `urlcensus` all pass. Existing generated projections remain unchanged.
The post-repair exhaustive axiom audit finds no remaining choice-bearing
declaration in the Integer module, including generated/private declarations.

Independent review confirms the nine source anchors and proof reasoning.
Reversing only the nine proof-body edits reconstructs the original Git blob
`8010ed37f4a2e11ce32e6a205eccff0514824e3a`, confirming that all other bytes,
including statements, aliases and docstrings, are unchanged.

These receipts close the local range-signature and constructive-proof
obligations of `INFRA-LF-INTEGER`. Wider Infra identity/coverage joins and
the remaining repository/core string dependencies stay open. The user
requested stopping here; `docs/CHOICE-REMOVAL.md` records that boundary.
