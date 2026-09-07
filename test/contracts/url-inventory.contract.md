# URL source inventory contract (U2a)

Status: FROZEN / RED, separate breaker process, 2026-09-05.

The declaration and behavior authority is
`docs/URL-INVENTORY-INTERFACE.md`. This packet freezes the independently
authored finite battery in `WhatwgTest/Url/InventoryContract.lean` before
implementation. The builder may repair elaboration but must not weaken,
delete, or replace its input, output, or acceptance conditions.

## Scope and authority

This slice inventories lexical source candidates. The input authority is
`vendor/whatwg-url-55d66993/url.bs`, WHATWG URL commit
`55d6699373ba68a16ec182f34222a74ed8bc3dac`, SHA-256
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`.
Its exact pin is owned by `SPEC-MANIFEST.md`; its fetch evidence is owned by
`docs/PROVENANCE.md`.

The unique implementation owner is `Gates.UrlInventory`. Its `TokenKind`,
`Token`, `Kind`, and `Entry` are tooling data. Existing `Gates.Census.Row`
remains the classified census carrier; the inventory does not replace it.
This packet contributes finite lexical evidence to `URL-PG-CENSUS` under
the assurance route in the interface record. It grants no semantic census
classification, coverage denominator, arbitrary-source parsing theorem,
URL algorithm theorem, or host-conformance claim. No observation mask is
asserted because these are source-inventory probes, not URL execution.

## Frozen surface and behavior

The battery ascribes these exact production signatures using fully qualified
names, so an accidental local shadow cannot satisfy them:

```lean
Gates.UrlInventory.tokenize :
  ByteArray → Except String (Array Gates.UrlInventory.Token)
Gates.UrlInventory.checkPartition : Nat → Array Gates.UrlInventory.Token → Bool
Gates.UrlInventory.scan : ByteArray → Except String (Array Gates.UrlInventory.Entry)
```

The interface record is the single owner of label derivation, UTF-8 byte
span boundaries, token partition rules, candidate ordering, optional
paragraph ends, and IDL line accumulation. Expectations in the battery
instantiate that record on literal sources. In particular, IDL inventory
retains delimited members without claiming to validate Web IDL grammar.

No fixture assumes a general HTML tree builder or browser error recovery.
Malformed lexical input and unfinished inventory/IDL containers must return
`Except.error`; exact diagnostic wording is not frozen. The scanner must not
silently truncate occurrences at a fixed count. The finite battery does not
prove the absence of every possible implementation cap.

## Frozen finite probes

Each source fixture and expected result lives once, in the Lean battery.
The following IDs identify acceptance-probe groups rather than discovered
semantic counterexamples. If implementation reveals a witness that changes a
declaration or cutover decision, the coordinator must register it in
`test/counterexamples/REGISTER.md` and link the retained Lean witness.

| Probe | Obligation exercised |
| --- | --- |
| `URL-INV-P01` | Empty input; exact full partition; refusal of missing tokens, initial gaps, interior gaps, overlaps, empty spans, reversed spans, overrun, and uncovered suffix. |
| `URL-INV-P02` | Single/double/bare/boolean attributes; a quoted `>`; a self-closing tag; exact UTF-8 byte offsets for `é`; definition `id` label precedence. |
| `URL-INV-P03` | A comment containing fake definition markup is one comment token and contributes no definition row. |
| `URL-INV-P04` | Entire nested algorithm spans, including ordinary nested divs; source ordering; algorithm value, ID, and first-definition fallback labels. |
| `URL-INV-P05` | Retain ignored and argument definitions; first `lt` alternative; owner prefix; empty owner; visible markup removal and normalized whitespace. |
| `URL-INV-P06` | Refuse unterminated quotes/tags/comments, missing attribute values, invalid UTF-8, and unclosed definition/algorithm/table/list/heading containers. |
| `URL-INV-P07` | `pre` IDL class token; interface/header and member extended attributes; constructors, static members, stringifier attributes, multiline iterable; an `&lt;` semicolon at line end cannot terminate the member; exact outer-trimmed source spans. |
| `URL-INV-P08` | `xmp` IDL and bare stringifier; `idl` is a class token, not a substring. |
| `URL-INV-P09` | Retain syntactically delimited opaque members; refuse unsupported top-level forms, stray top-level members, missing header/member terminators, unclosed interfaces and unclosed `pre`/`xmp`. |
| `URL-INV-P10` | Optional paragraph end at next paragraph, container close, and EOF; explicit paragraph close; heading visible text/entities and nearest heading ID, including an unlabelled heading resetting the section. |
| `URL-INV-P11` | Entire balanced table, ordered, unordered and definition-list spans; nested list ordering; preceding section propagation. |

The projection helper first checks `b < e ≤ input.size` for every emitted
entry, then compares its kind, label, section and exact source-byte slice.
The fixtures use distinct source snippets where nested spans are compared.
Token tests independently check numerical UTF-8 boundaries. The expected
results never call production label or span helpers.

All tests are `#guard` finite executable probes. They add no theorem claiming
a general scanner law, and no proof axiom. Every test helper is private.
Only the pinned production module supplies scanner behavior; there is no
mock scanner in the battery.

## File fence and validation

Breaker-owned and frozen:

- `test/contracts/url-inventory.contract.md`
- `WhatwgTest/Url/InventoryContract.lean`

Red-phase registration, removable by the builder immediately on green:

- `test/fixtures/trust-gate/known-red.txt`, entry
  `WhatwgTest.Url.InventoryContract`

Builder implementation: `Gates/UrlInventory.lean`; gate/root/executable and
projection integration are coordinated by the root seat's separate claim.
No vendored bytes or generated projections belong to the breaker fence.

Narrow red/green command:

```text
lake build WhatwgTest.Url.InventoryContract
```

The expected preimplementation red cause is the absent `Gates.UrlInventory`
module. That missing-module check does not elaborate the downstream probes;
the builder must run them after adding the scanner. Once the narrow battery
is green, remove its known-red entry, run the default build and actual axiom
receipt, and run repository gates under the pinned toolchain. U2's semantic
classification, dependency, proof-graph and coverage-join obligations remain
open after the lexical inventory battery passes.

The breaker ran no host observations. Axiom evidence is deferred to the
postimplementation build because no scanner declarations exist during red.
