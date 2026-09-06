# URL authored census input and projection contract (U2c)

Status: FROZEN / RED, independent breaker process, 2026-09-05, based on
`9c8cb49d92393ed289fa034128a5e031b1fe0c8c`.

The declaration, format and acceptance authority is
`docs/URL-CENSUS-INPUT-INTERFACE.md`. This packet freezes
`WhatwgTest/Url/CensusInputContract.lean` before the implementation of
`Gates.UrlCensusInput`. The builder may repair elaboration but must not
weaken, delete or replace a frozen fixture or acceptance condition.

## Ownership and assurance

`Gates.UrlCensusInput.Inputs` is the raw authored-file view. Its results reuse
`Gates.UrlCensus.SourceRow` and `Assignment`, which remain the existing
canonical census/join carriers. No second production row or semantic URL
carrier is declared by this packet. The existing U2a and U2b contracts and
their independently frozen batteries remain unchanged.

The source authority remains the URL pin in `SPEC-MANIFEST.md`. The fixtures
here are deliberately small independent sources; they do not classify the
pinned standard. This tooling contributes to the open `URL-PG-CENSUS` graph.
A successful input/projection fixture grants no URL coverage state,
denominator, execution theorem, host observation or proof of a dependency's
semantics. Fixed-pin source review, declaration/numerator joins and semantic
assurance remain separate obligations.

## Frozen public surface

The battery exactly ascribes the fully qualified `Inputs` type, its
six-string constructor and all six field projections, together with:

```lean
#check (@Gates.UrlCensusInput.build : ByteArray → Gates.UrlCensusInput.Inputs →
  Except String (Array Gates.UrlCensus.SourceRow × Array Gates.UrlCensus.Assignment))
#check (@Gates.UrlCensusInput.project :
  ByteArray → Gates.UrlCensusInput.Inputs → Except String (String × String))
#check (@Gates.UrlCensusInput.cli : List String → IO UInt32)
```

The interface is the single owner of format syntax, field retention,
disposition priority, unused-input refusals, anchor selection, the U2b join,
projection bytes and CLI behavior. The Lean battery instantiates those rules
without inventing default classification or suppressing any join error.
Rejection means `Except.error`; diagnostic text is not an acceptance oracle.

## Independent finite expectations

Every successful `build` fixture compares all canonical row fields: kind,
ID, anchor start/end, span start/end, disposition, parent, dependencies and
origins. It also compares every complete `Assignment`, including the entire
candidate record, owner and exact reason. Expected byte positions, orders
and fields are independently authored literals. The test helpers construct
or compare records; no production parser, scanner, row resolver, anchor
finder, sorter, escape function or hash function computes an expected value.

Projection expectations compare both returned strings in full, including
header order, the six input-digest lines, every data field, escapes and final
LF. The independent SHA-256 literals were computed with .NET
`System.Security.Cryptography.SHA256.HashData` over explicit UTF-8 fixture
bytes using `System.Text.Encoding.UTF8.GetBytes`, separate from Lean's
`Gates.Sha256.hexDigest`. The main source has 57 bytes, the section source
34 bytes and the escaping source 29 bytes. The expected source/span/anchor
and authored-input digests live alongside their literal fixtures in the
battery.

The tests include a changed source-input comment and an LF-to-CRLF change in
dispositions. Both retain the same parsed rows but require distinct hashes
of the exact authored strings. Thus the expected digest is not a normalized
summary or a re-rendered row list.

## Frozen probe groups

These IDs identify preimplementation finite acceptance groups, not discovered
semantic counterexamples. The coordinator registers any later witness that
changes a declaration or cutover decision centrally and links the retained
Lean source.

| Probe | Frozen cases |
| --- | --- |
| `URL-INP-P01` | Empty inputs, short full-row anchors, blank lines, whole-line comments after ASCII whitespace, and CRLF parsing. |
| `URL-INP-P02` | Canonical ASCII natural numbers and identity tokens; nonempty origin lists; exact field counts for all six files; no field trimming, inline comments, or duplicate span IDs. |
| `URL-INP-P03` | Exactly one dependency entry and resolved disposition per row; no missing, duplicate or unused metadata, override or external entry; override justification; external `ext.` namespace; U2b dependency refusals and used external success. |
| `URL-INP-P04` | Punctuation-bearing section IDs; strict disposition vocabulary and keys; no ancestor fallback; exact-kind rule over wildcard and row override over rules, with every selected input accounted for. |
| `URL-INP-P05` | In-span anchors only; repeated entire spans fail rather than borrow source suffix; invalid source/spans fail; repeated 24-byte prefixes extend to 32; overlapping matches count; UTF-8 boundary alignment; full-row fallback after earlier attempts remain nonunique; stable same-kind row ordering. |
| `URL-INP-P06` | Full U2b assignment and refusals, including missing ownership, invalid/duplicate origins, incorrect parent, unused explanations, blank FF reason, and exact literal explanation text; nested row ownership and sorted rows with authored list order retained. |
| `URL-INP-P07` | Exact empty and nested census/assignment TSVs; source, span, anchor and all input hash headers; sort order, parent, origins and dependencies; comments alter raw-input hash; project rejects unchecked input. |
| `URL-INP-P08` | Exact backslash/tab/LF/CR escapes, preserved ordinary vertical bar, exact explanation text, absent-owner spelling and escaping-source digest. |
| `URL-INP-P09` | Nonempty disposition-input hashes; structural heading assignments; exact section field; raw CRLF sensitivity with parsed-row identity retained. |

All assertions are finite `#guard` executable probes, and all helper
declarations are private. No new theorem or proof axiom is introduced.
Successful finite probes are not a general parser, anchor or projection law.

## Fence and verification

Frozen breaker files:

- `test/contracts/url-census-input.contract.md`
- `WhatwgTest/Url/CensusInputContract.lean`

`test/fixtures/trust-gate/known-red.txt` declares
`WhatwgTest.Url.CensusInputContract` during red. The breaker also records its
exact claim in `COORDINATION.md`. It edits no implementation, fixed-pin
authored census files, central counterexample register, vendored source or
generated projection.

The sole narrow red/green command is:

```text
lake build WhatwgTest.Url.CensusInputContract
```

Before implementation, the red cause is the absent `Gates.UrlCensusInput`
module. This check does not elaborate the downstream probes; the builder
must run the actual battery after the module exists. The breaker reports
the exact result, commit and stopped Lake run before returning the slot.

Once green, remove the known-red entry and retain the battery in the test
root. CLI filesystem behavior requires separate integration verification
under the frozen interface: argument handling, strict source/input reads,
source-pin check, both outputs, drift diagnostics, writes and exit codes.
The pure battery only ascribes the CLI signature and does not run those
side effects. The coordinator owns this integration check, default build,
actual axiom receipts, fixed-pin data review and repository gates. No U2
coverage cutover follows from these fixtures alone.
