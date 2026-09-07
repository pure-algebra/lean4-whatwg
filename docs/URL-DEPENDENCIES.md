# URL dependency meanings and open obligations

Status: U2c authored dependency review, 2026-09-05. The canonical identity
list is `census/url/externals.tsv`; `dependencies.tsv` owns the source-row
edges. This document owns the meanings and remaining assurance obligations
behind those identities. `SPEC-MANIFEST.md` and `docs/PROVENANCE.md` retain
exclusive ownership of adopted pins and provenance. An identity join does
not admit an implementation, pin, dependency theorem or host result.

Every external group below remains open until its exact declarations,
parameters, data versions, source anchors and proofs are joined. Existing
Infra declarations are candidates under their existing owner; URL must not
copy their carriers. All future proof receipts follow the URL lane's
choice-minimization objective and inspect dependencies in statements too.

## Infra foundations

`ext.infra.standard` records the explicit Infra dependency. The `byte`,
`byte-sequence`, `code-point`, `scalar-value`, `scalar-value-string`,
`string`, `ascii-string`, `ascii`, `unsigned-integers`, `list`, `tuple`,
`map` and `struct` identities name Infra-owned types, restricted views and
vocabulary. A scalar-value string and an ASCII string are restrictions of
the canonical Infra string, not permission to replace it silently with
Lean `String`. The domain and opaque-host rows require nonempty ASCII
strings; their nonemptiness is a URL invariant.

`surrogate` and `noncharacter` name the Infra predicates explicitly excluded
by `op.url-code-points`. Existing `CodePoint.isSurrogate` and
`CodePoint.isNoncharacter` are reuse candidates; their exact source and
theorem joins remain required.

`strictly-split`, `string-operations`, `isomorphic-decode`, `list-sort` and
`code-unit-less-than` name the Infra operations invoked by the source.
The string-operations family includes the explicitly cited prefix/suffix,
length, code-point length and code-point substring operations. Each actual
call still needs a precise declaration/assurance mapping before semantic
cutover. URLSearchParams sorting uses Infra code-unit ordering and stable
ascending list sorting, not a locale comparator or byte order.

## Encoding

The standard, encoding type and UTF-8 identity are explicit dependencies.
The executable identities distinguish `utf8-encode`,
`utf8-decode-without-bom`, `utf8-decode-without-bom-or-fail`, `get-encoder`,
`io-queue`, `encode-or-fail`, and `get-output-encoding`. Their names do not
license an unconstrained callback in the URL model.

`op.percent-encode-after-encoding` creates one encoder and retains it across
repeated `encode or fail` calls. Encoding errors contribute URL's specified
percent-encoded decimal character reference. The assertion permits UTF-8,
or the special-query percent-encode set, or the form percent-encode set;
it is not an assertion of ASCII-compatible encoding. `op.parser-query`
retains the ISO-2022-JP encoder dependency as the reason to encode the
accumulated buffer instead of processing code points independently. It
also changes non-UTF-8 encodings to UTF-8 for nonspecial URLs and `ws`/`wss`.

The byte percent-decoder returns bytes; its warning about UTF-8 does not
turn it into a decoder invocation. Its edge to `utf8-decode-without-bom`
records that retained advisory dependency. The host parser's note allows the
without-BOM-or-fail alternative only with early failure. Rendering's
decoding has visibility and spoofing exceptions. Form parsing is UTF-8;
the note about unspecified legacy server `_charset` behavior does not
remove the separately specified serializer's encoding parameter.
`ext.html.document-encoding` records the document/query relationship in
the source note, not a new URL operation for acquiring a document encoding.

## Unicode domain processing

`ext.uts46.unicode-to-ascii` and `unicode-to-unicode` require the actual
UTS #46 algorithms, their Unicode-version-dependent tables and subsidiary
algorithms. No Unicode pin is inferred from the URL commit date.

The URL-owned ToASCII call passes `domain_name = domain`;
`CheckHyphens`, `UseSTD3ASCIIRules` and `VerifyDnsLength` equal `beStrict`;
`CheckBidi` and `CheckJoiners` are true; `Transitional_Processing` and
`IgnoreInvalidPunycode` are false. The ToUnicode call passes the domain,
sets `CheckHyphens` and `UseSTD3ASCIIRules` false, `CheckBidi` and
`CheckJoiners` true, and `Transitional_Processing` and
`IgnoreInvalidPunycode` false. It does not pass `VerifyDnsLength`.

`op.domain-to-ascii` remains a distinct URL-owned wrapper: it performs the
strict probe, records that validation failure without immediately returning,
and retains the nonstrict ASCII-lowercasing compatibility branch. A bare
ToASCII call does not implement that wrapper. ToUnicode records errors and
may return the original domain. Validation and rendering source rows reach
these algorithms through their local URL owners.

## Public suffix and origins

PSL identities distinguish public-suffix selection, registrable-domain
selection and rules data. The selected list version/profile must be named;
it is not a universal security boundary. URL's algorithms additionally
require ASCII output retaining the input's trailing dot and perform their
own null/equality checks. Neither the PSL algorithm nor its tables are
discharged by an unprofiled host query.

File API identities cover the blob URL entry, resolution and entry
environment. Resolution is host-state-sensitive, but its result must retain
the entry/environment/origin relationships and URL's cache behavior.
HTML identities distinguish the origin carrier, tuple origin, fresh opaque
origin, environment origin, same-origin relation, origin serialization and
the platform-object extraction hook. Fresh opaque origins need explicit
identity allocation; structural equality of empty records is insufficient.
The `file:` origin branch is expressly underspecified and requires a named
policy/profile instead of an invented universal result.

The same-site and schemelessly-same-site identities belong to security
advice addressed to other specifications. They are not new parser branches.

## Web IDL and other language boundaries

Every IDL source row retains the Web IDL binding dependency and its
interface context. More specific identities distinguish exposure, the
legacy window alias, USVString conversion, optional arguments, union,
sequence and record conversion, sequence-result type, SameObject, iterable,
stringifier, unsigned long, Boolean, undefined and nullable types.
Omitted arguments and provided values are not interchangeable.

Platform-object identity and creation are explicit. Both URL object-state
groups retain associated-object identity; constructor/setter errors retain
the TypeError operation. URLSearchParams iteration supplies the value-pairs
hook and does not itself implement all generated iterator machinery.
User-code effects encountered by binding conversion may be foreign
boundaries, but the specified conversion algorithm itself remains an
external semantic obligation. Native Lean values with similar names do
not by themselves satisfy a language binding.

The component encoding note's ECMA-262 `encodeURIComponent` equivalence
has its own bridge obligation on scalar-value-string inputs. Its HTML
registerProtocolHandler reference is usage context. A proof of the URL
algorithm alone cannot establish that external equivalence.

## Advice and evidence dependencies

IANA scheme registration is writing advice. Registry membership does not
become a parser acceptance condition. The Unicode bidirectional algorithm
dependency is a browser rendering property: behave as though text is in a
left-to-right embedding. The source does not prescribe one deterministic
URL renderer.

The confusable-character and UTR36 identities record cited advice, not a
requirement to execute every algorithm in UTS39/UTR36. RFC 5952 retains the
serializer's recommendation relationship; it does not replace URL's IPv6
serializer. Historical RFC goals and the RFC 5890 contrast are explanatory
source context, not competing semantic owners.

## Review evidence and remaining work

The independent source reviewer inspected all external groups and exact
invoking source IDs against the pinned bytes, including IDL attributes,
encoder state, domain flags, origin freshness and the `file:` policy gap.
The authored dependency rows also contain local operation/field and
parser-state links. The reader checks identity, uniqueness and use; it
cannot prove that a source-dependency edge is sufficient or that a linked
external implementation is faithful. Per-declaration ownership, imported
API/data pins, representative breaker contracts and proof graphs remain
required before the U2 semantic entry gate can close.
