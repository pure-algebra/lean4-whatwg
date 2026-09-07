# Infra integer constructive proof contract

Status: FROZEN / RED, independent breaker process, 2026-09-05, based on
`8a2b608c7e60616a52e77f0f5d3fabe6e55bb9f5`.

The declaration, source and local assurance authority is
`docs/INFRA-INTEGER-CONSTRUCTIVE.md`. The executable frozen contract and
retained `INFRA-INTEGER-CE-001` witness live in
`WhatwgTest/Infra/IntegerConstructiveContract.lean`. The coordinator records
the stable counterexample centrally in `test/counterexamples/REGISTER.md`.
The user has paused URL implementation to remove `Classical.choice` first.

## Fixed aliases and universally quantified statements

The existing aliases in `Whatwg.Infra` retain their native representations:
`Unsigned8`, `Unsigned16`, `Unsigned32`, `Unsigned64`, and `Unsigned128`
are `UInt8`, `UInt16`, `UInt32`, `UInt64`, and `BitVec 128`; `Signed8`,
`Signed16`, `Signed32`, and `Signed64` are `Int8`, `Int16`, `Int32`, and
`Int64`. The battery checks each alias's definitional equality to that
native representation by an explicitly ascribed `rfl`. No replacement
carrier, wrapper, runtime definition or conversion is introduced.

The semantic source is the pinned Infra `numbers` section. The declaration
record owns each raw source span and its digest; `SPEC-MANIFEST.md` owns the
source pin. Each exact statement remains the existing `.inRange` theorem
for an arbitrary input of its canonical alias, using the literal inclusive
bounds below. Unsigned observations use `toNat`; signed observations use
`toInt`.

| Theorem in `Whatwg.Infra` | Lower bound | Upper bound |
| --- | --- | --- |
| `Unsigned8.inRange` | 0 | 255 |
| `Unsigned16.inRange` | 0 | 65535 |
| `Unsigned32.inRange` | 0 | 4294967295 |
| `Unsigned64.inRange` | 0 | 18446744073709551615 |
| `Unsigned128.inRange` | 0 | 340282366920938463463374607431768211455 |
| `Signed8.inRange` | -128 | 127 |
| `Signed16.inRange` | -32768 | 32767 |
| `Signed32.inRange` | -2147483648 | 2147483647 |
| `Signed64.inRange` | -9223372036854775808 | 9223372036854775807 |

The fully qualified Lean ascriptions freeze each exact quantifier, alias,
numeric projection, conjunction and inclusive inequality. Numeric samples,
smaller ranges or a one-sided bound cannot replace these general statements.
The observation is the native numeric value of an arbitrary carrier input;
there is no host boundary or stream observation mask in this local receipt.

## INFRA-INTEGER-CE-001 — choice enters existing range proofs

The reviewed implementation uses `omega` in all nine range proofs. The
initial dependency audit reported that each theorem reaches
`Classical.choice` through its generated proof dependencies. This violates
the frozen local ceiling `[propext, Quot.sound]` even though the statements
already elaborate under the broader repository ceiling.

The frozen check invokes the actual `Lean.collectAxioms` separately for
every ascribed range theorem. It prints all returned transitive axiom sets
and accumulates every declaration/axiom pair outside the allowed set before
raising an error. Dependencies in theorem types, proof bodies and generated
proof auxiliaries are included by Lean's collector. No diagnostic substring,
source-text search, hard-coded receipt, swallowed error or substitute theorem
is an acceptance oracle.

The whitelist rejects `Classical.choice` and any other unlisted axiom,
including compiler/native proof axioms. The collector's own metaprogramming
implementation is not the target of this local receipt. Successful checks
establish the actual axiom dependencies of these named general proofs, not
a finite integer sample and not a repository-wide choice-removal result.

## Builder fence and assurance route

The builder may change only the nine `.inRange` proof bodies in
`Whatwg/Infra/Primitive/Integer.lean`. Every existing alias, theorem type,
runtime definition and docstring stays unchanged. It must retain the frozen
packet and all executable acceptance conditions. A deleted theorem, changed
statement, renamed replacement, new axiom or audit exemption cannot satisfy
this contract.

This is the `INFRA-LF-INTEGER` local leaf receipt for existing nonrecursive
fixed-width carrier views and their range facts. It introduces no operational
judgment, admission function, interpreter, composition or cross-language
equivalence. Wider Infra identity/coverage joins and all other outstanding
choice dependencies remain separate obligations.

## Breaker files and verification

The breaker owns this packet and
`WhatwgTest/Infra/IntegerConstructiveContract.lean`, plus its exact
coordination claim and known-red entry. The entry is
`WhatwgTest.Infra.IntegerConstructiveContract` in
`test/fixtures/trust-gate/known-red.txt`. The coordinator owns implementation,
central registration and test-root integration.

The exclusive narrow red/green command is:

```text
lake build WhatwgTest.Infra.IntegerConstructiveContract
```

The initial run must elaborate all nine carrier equalities and all nine
exact theorem signatures, then fail on the actual unlisted axiom while
reporting every affected declaration. Missing imports or syntax failures
do not establish this witness. The breaker commits before that run and
reports the commit, exact result and stopped Lake process before repair.

After the local check passes, the builder removes its known-red entry and
keeps the battery imported from the test root. Independent proof/source
review, the default build, actual axiom receipts and repository gates remain
required; this packet alone does not close any broader choice-removal goal.
