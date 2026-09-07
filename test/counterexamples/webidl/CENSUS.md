# Web IDL census attack shapes

Seeded by the promise census breaker seat, 2026-09-06, alongside
`test/contracts/webidl-census.contract.md` and its frozen battery
`WhatwgTest/Audit/WebIdl/CensusContract.lean`.

Every attack below is already encoded in that battery: as a `#guard` over a
literal fixture where the attacked behaviour is pure, and as a clause of the
projection gate where it is a property of the generated file. None has a stable
ID yet. The coordinator assigns the `WEBIDL-CEN-CE-nnn` ids and adds the rows to
`test/counterexamples/REGISTER.md` at landing; the placeholders below are the
order in which they should be assigned. This file adds no row to that register.

The area token is `WEBIDL` under the scheme in `test/counterexamples/README.md`:
the owning standard's token replaces `WS` for a standard added to the shared
package. Witnesses stay in the battery rather than moving to a
`Counterexamples/` module, because each attacks the census generator rather
than a semantic declaration.

## WEBIDL-CEN-CE-001 — the prefix rule silently drops 45 algorithm blocks

Attacked: `Gates.Census.scanOps` and `Gates.Census.algorithmBlocks`, which key
on the byte prefix `<div algorithm`. The pinned Web IDL source writes 201
`<div>` tags carrying an `algorithm` attribute and only 156 of them put the
attribute first; the other 45 write `id=` first. One of the 45 is in scope,
`<div id="js-to-promise" algorithm="convert a JavaScript value to promise">` at
byte 346692. Under the prefix rule the census silently holds 25 `op` rows
instead of 26 and no error fires. This is the same defect one level up that
`SPEC-MANIFEST.md` already records for keying on the closing bracket.

Encoded as: the frozen row `op.js-to-promise` at 346692–347209 and the frozen
`op` count of 39. Forced repair: key on the attribute, which the identity
packet shows is byte-neutral for Streams (248 tags either way) and Infra (18).

## WEBIDL-CEN-CE-002 — `scanRequirements` aborts every other Bikeshed standard

Attacked: `Gates.Census.build`, which calls `scanRequirements bs ops`
unconditionally in the non-definition-keyed branch, and `scanRequirements`,
which opens with a literal search for `<div algorithm="ReadableStreamPipeTo">`
and returns `.error` when it is absent. Any second algorithm-keyed standard
therefore fails with a message about the Streams pipe-to block.

Encoded as: `requirementMarker := none` in the frozen `webidl` profile, the
frozen `requirement` count of 0, and the whole projection existing at all.
Forced repair: gate the scanner on the marker. The identity packet holds the
seven Streams `requirement` rows fixed across the change.

## WEBIDL-CEN-CE-003 — an unrecognised IDL header aborts the run

Attacked: `Gates.Census.scanIdl`. The `QuotaExceededError` block at byte 213511
accumulates the header `[Exposed=*, Serializable] interface QuotaExceededError
: DOMException {`, whose word list after `stripExtendedAttribute` matches none
of the three admitted shapes, so the whole run returns
`census: unrecognised IDL header`. Interface inheritance is unsupported.

Encoded as: the frozen row `idl.quota-exceeded-error` at 213527–213598. Forced
repair: accept the five-word form `interface <Name> : <Base> {`.

## WEBIDL-CEN-CE-004 — a trailing `//` comment swallows a whole IDL block

Attacked: `Gates.Census.scanIdl`. The `DOMException` header line ends
`interface DOMException { // but see below note about JavaScript binding`, so
the accumulator never sees a terminating `{`, `owner` is never set, and all 30
following statements are counted as skipped top-level statements. Thirty rows
disappear and the only trace is a number in a summary line.

Encoded as: the 30 frozen `idl.dom-exception*` rows, the frozen `idl` count of
37, and the acceptance condition that the reported count of IDL statements
outside the row vocabulary is 0. Forced repair: strip a trailing `//…` comment
from each line before the terminator test and before the span end is taken.

## WEBIDL-CEN-CE-005 — `const` members are named by their value

Attacked: `Gates.Census.scanIdl`'s member-naming ladder, which has no case for
`const`. `const unsigned short INDEX_SIZE_ERR = 1;` falls through to
`trailingIdent` of the whole body and is named `1`, giving
`idl.domexception-1` … `idl.domexception-25`.

Encoded as: the 25 frozen `idl.domexception-*-err` rows, each named for the
constant it declares. Forced repair: take `trailingIdent` of the part before
` = `.

## WEBIDL-CEN-CE-006 — the whole error-names table becomes one span

Attacked: `Gates.Census.scanDefinitions`' span rule. The 32 error-name `<dfn>`
sit in `<td>` cells of `<table id="error-names">` at 200422–211136, and neither
the paragraph-opener rule nor the blank-line chunk separates them: all 32 rows
receive the same 10,714-byte span, and the generator anchors and digests that
span 32 times without any error.

Encoded as: the 32 frozen `type.*error` rows, each with its own `<tr>` span,
and the contract's statement that the longest row span is 2,333 bytes. Forced
repair: the innermost enclosing `<tr>` is step 2 of the frozen span ladder. It
is vacuous on Infra, which has 0 `<tr>`.

## WEBIDL-CEN-CE-007 — a colon reaches across 480 KB for a list

Attacked: `Gates.Census.scanDefinitions`' colon extension, which looks for the
next `<ol` anywhere after the chunk. `simple exception` at byte 194435 ends its
chunk with a colon and is followed by a Bikeshed markdown list, not an `<ol>`;
the next `<ol` in the file is at 676691, so the row's span becomes 482,258
bytes and swallows most of the standard.

Encoded as: the frozen row `op.dfn-simple-exception` at 194433–194721 (288
bytes) and the five frozen list-line rows `type.eval-error` … `type.uri-error`
inside it. Forced repair: step 4a of the frozen span ladder extends through a
markdown list when one begins at the first non-whitespace byte after the chunk.
Recomputed on Infra: of its 23 colon-branch definitions, 21 are followed
immediately by `<ol` and 2 by `<p`, never by a markdown list, so the step is
vacuous there.

## WEBIDL-CEN-CE-008 — the definition-keyed mode collides on four ids

Attacked: `Gates.Census.scanDefinitions`' naming ladder, which ignores the
Bikeshed dfn type. `DOMException`'s associated `name` and its `name` attribute
getter are two different definitions with the same name and the same `for`, and
so are `message`, `QuotaExceededError`'s `quota` and its `requested`. Replaying
the Infra mode over the whole file produces four duplicate ids and
`census: duplicate row id(s)`.

Encoded as: the frozen rows `op.dom-exception-name` and
`op.dom-exception-message` beside `idl.domexception-name` and
`idl.domexception-message`, and the acceptance condition that the projection is
strictly increasing in `kind.name ++ "|" ++ id`. Forced repair: read the
Bikeshed dfn type and let the IDL-block statement carry the
`const`/`attribute`/`constructor` definitions.

## WEBIDL-CEN-CE-009 — three definitions have no `<dfn>` tag at all

Attacked: any `<dfn`-keyed definition scanner. Bikeshed lets a heading be a
definition. `Promise` the interface type, `exception objects` and `DOMException`
the interface are defined by their headings' `interface` and `dfn` attributes at
bytes 252146, 664320 and 673398, and a `<dfn`-keyed scan produces no row for any
of them — so the census would carry 30 rows for `DOMException`'s members and
none for `DOMException`.

Encoded as: the frozen rows `type.idl-promise`, `op.js-exception-objects` and
`type.idl-dom-exception`, whose spans are the heading elements. Forced repair:
treat a line-opening heading carrying a bare Bikeshed definition marker as a
definition. Recomputed: 0 of the Streams source's 132 line-opening headings and
0 of the Infra source's 40 carry one, so the step is vacuous for both.

## WEBIDL-CEN-CE-010 — two `<h5>` sections collapse into one disposition

Attacked: `Gates.Census.scanHeadings`, which admits levels 2 to 4 only.
`js-promise-manipulation` and `js-promise-examples` are `<h5>`, so every row in
both resolves against the `js-promise` `<h4>` and the eleven promise operations
would take the same disposition as the seven worked examples.

Encoded as: `headingLevels := (2, 5)` in the frozen profile and the frozen
disposition split, 11 `owned` against 8 `evidenceOnly`. Recomputed: both
existing sources have 0 line-opening `<h5>`, so raising the ceiling is
byte-neutral for them.

## WEBIDL-CEN-CE-011 — six requirement bullets share one span

Attacked: `Gates.Census.scanRules`, whose span runs from the locator to the next
blank line. The six `idl-DOMException-derived-interfaces` bullets sit in one
blank-line paragraph, so six authored rule rows would all end at byte 212653
and five of them would nest inside the first.

Encoded as: the six frozen `rule.domexception-derived-*` rows with disjoint
spans 211607–211774, 211775–211921, 211922–212161, 212162–212318,
212319–212507 and 212508–212653, and the `parseRules`/`scanRules` probes.
Forced repair: R-P4's optional end locator, refused rather than widened when it
has no occurrence at or after the start locator.

## WEBIDL-CEN-CE-012 — an out-of-scope IDL block aborts an in-scope run

Attacked: the shape of the scope filter. The file holds twelve IDL blocks and
ten are out of scope; if the scanners run file-wide and the filter is applied to
rows afterwards, an error raised in one of the ten aborts a run for reasons that
have nothing to do with this lane.

Encoded as: the contract's requirement that the scope is a predicate the
scanners consult, together with the frozen `idl` count of 37, which is
reachable only from the two in-scope blocks.

## Scope

These are finite tooling probes over a pinned source. They contribute no Web
IDL semantic theorem, no coverage state, no denominator the numerator may
quote, no host observation and no axiom receipt. The narrow command is

```text
lake build WhatwgTest.Audit.WebIdl.CensusContract
```

and the coordinator owns the full build, the actual axiom receipt and the
repository gates.
