# Comma splitting: the trailing delimiter (INFRA-TEXT-CE-001)

Status: `CLOSED`, 2026-09-05. The separate breaker process froze the three
finite witnesses below; the coordinator compiled them and integrated them
into the common audit root without changing their statements or proofs.

## Authority and attacked statement

The semantic owner is `whatwg/infra` commit
`3f984adcd24a6d5c53cc26b3e737701808003f3e`, section `strings`, definition
`split on commas`, in `vendor/whatwg-infra-3f984adc/infra.bs`.
The algorithm span is bytes `[62430, 63598)`, SHA-256
`f128d4ae1e956dda5cc54b39e8976a11c5ae9b4754aac71925741ef982717962`.
It starts at the paragraph defining comma splitting and ends immediately
before the paragraph defining concatenation; the intervening whitespace is
included in the digest.

At repository base `c1c7caa9b68ba4ff72ac379f4aedcc84385e5f28`, the source
example in `Whatwg/Infra/Text/Scan.lean` asserted:

```lean
splitOnCommas (ofLiteral " a , ,b,") =
  [ofLiteral "a", ofLiteral "", ofLiteral "b", ofLiteral ""]
```

The pinned algorithm and the existing implementation produce three tokens.
For this eight-code-point input, the first iteration collects positions
0 through 2, strips their surrounding spaces, and advances over the comma
at position 3. The second collects the space at position 4, producing an
empty token, then advances over the comma at position 5. The third collects
`b` at position 6 and advances over the final comma at position 7. Position
8 is past the final code point, so no fourth iteration occurs. Empty input
enters no iteration and returns the initially empty token list.

This behavior differs from the separate `strictlySplit` algorithm, whose
initial collection and delimiter loop retain a final empty token. Correcting
the comma-splitting source example must not change either algorithm.

## Witnesses and verification

The source is `WhatwgTest/Infra/Counterexamples/CommaSplit.lean`, namespace
`WhatwgTest.Infra.Counterexamples.CommaSplit`:

| Declaration | Frozen proposition |
| --- | --- |
| `ce001_correct_result` | the input above yields exactly `a`, the empty string, and `b` |
| `ce001_original_result_false` | the negation of the exact original four-token proposition |
| `ce001_empty_input` | empty input yields an empty token list |

Each theorem has an exact `#check (@name : proposition)` ascription in the
witness module, freezing its full statement independently of its proof body.
The three ascriptions repeat the original theorem statements without changes.

The observation is the full ordered `List JsString` result. These are finite
probes over the production definitions and have no host assumptions. They
do not prove a general correspondence between comma splitting and the
specification or close the Infra text proof graph. Every proof uses
`decide +kernel`; the module prints an axiom receipt for each theorem.

Narrow verification command:

```text
lake build WhatwgTest.Infra.Counterexamples.CommaSplit
```

The coordinator must also import this module from `WhatwgTest.lean` and run
the common axiom gate before closing the register row. No intentionally red
module is introduced: the retained false statement appears under negation.
Coordinator verification: `lake build WhatwgTest.Infra.Counterexamples.CommaSplit`
and `lake build` both PASS. Each of the three printed axiom receipts is
`[propext, Classical.choice, Quot.sound]`, inside the common ceiling.
The common module/axiom gate passes over 124 modules and 6,529 declarations.
The source example now expects three tokens; the original four-token
statement remains under negation in `ce001_original_result_false`.
