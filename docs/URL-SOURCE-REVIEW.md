# URL semantic source-span review

Independent source review at worktree head `79c23294e0d4a4354f8376d9c83551635546af44`,
2026-09-05. The reviewer inspected the pinned `url.bs` directly and all 121
lexical definition candidates outside algorithm containers. This is a source
review, not a census denominator, proof, or host-conformance result. Byte
offsets below are `[b,e)` in the pin owned by `SPEC-MANIFEST.md`.

This document retains the reviewed semantic-span obligations. The authored
census inputs must resolve them; the source inventory alone does not. The
reviewer wrote no implementation, supplied no generated classifications, and
ran no Lake commands. The root independently inspected parser-state and IDL
boundaries. The census join's behavior is owned by
`docs/URL-CENSUS-INTERFACE.md`, and its graph by `docs/URL-CENSUS-DAG.md`.

## Computations outside algorithm wrappers

Retain integer serialization `[2898,2993)`, domain-label splitting
`[31873,32045)`, valid-domain checking `[41769,42182)`, the urlencoded string
parser `[135009,135355)`, URLSearchParams iteration `[158830,159004)`, and
its stringification behavior `[159004,159191)`. Valid-domain checking needs
its ordered steps. Iteration has neither a definition nor an algorithm
wrapper. Domain labels use Infra strict splitting, not URL parsing.

## Validation and parser notation

Validation-error definition/reporting advice is `[3022,3219)`, with the
error table at `[3634,14653)`. Each of its 31 definition candidates needs
the error description and failure column. Preserve conditional failure for
domain-to-ASCII and IPv4-out-of-range-part, and all three listed conditions
for IPv4-in-IPv6-invalid-code-point. The note `[3237,3398)` explains the
distinction between a validation error and parser termination.

Parser notation `[14685,15727)` defines conceptual EOF, a code-point pointer
that permits −1, and contextual `c` and `remaining` references with validity
conditions. They are not independent URL record fields or unrestricted
accessors.

## Percent encoding and hosts

Percent-encoded-byte syntax `[16209,16325)` accepts either hex case; byte
serialization emits uppercase. The definitions in `[18975,21624)` include
the general percent-encode-set concept and individual set predicates. Query does
not inherit fragment wholesale. Record their actual predicate dependencies.

Host representation `[31032,33095)` includes domain, domain labels, integer
IP representations, IPv6 pieces, opaque host and empty host. An IPv6 piece
shares its representation paragraph. Empty host is distinct from null.
The RFC references here are informative; URL's algorithms remain authoritative.
Forbidden-host and forbidden-domain predicates `[33146,33552)` differ.

Host-writing definitions require their whole grammar: valid IPv6 includes
the list `[42858,43362)` and valid opaque-host includes `[44421,44616)`.
Keep shortest decimal/hex representations, effective piece length, IPv4's
two-piece contribution and the compression bound. `valid domain string` is
a view of valid-domain checking. Valid opaque-host syntax is context-dependent,
and is not another alternative of the valid-host-string definition.

## URL representation and writing

The fourteen record-area definitions include the record, associated
components, path carrier, stored path segments and dot predicates. Field
spans must include initial values: empty strings, null and an empty list
are different. The blob URL entry needs its File API relationship. Link the
scheme/host table `[68748,69313)`, special-path note `[69726,69902)`, and blob
caching explanation `[70486,70786)` to their invariant/boundary obligations.
Stored `URL path segment` and grammatical `URL-path-segment string` have
different roles.

Special schemes and default ports require the paragraph and table together,
`[73140,73729)`, including the default-null rule for other strings. Preserve
credential, opaque-path and username/password/port restrictions. `is not
special` is the complement of `is special`; `base URL` is a role of an
existing record, not another carrier.

Windows-drive-letter definitions begin at `[74697,74850)` and
`[74850,74978)`. The starts-with predicate requires `[75113,75549)`, including
all three conditions and permitted third characters. A normalized drive
letter is a colon-constrained predicate, not a normalization algorithm.
Legacy vertical-bar parsing and conforming writing syntax must stay distinct.

The twenty-one URL-writing definitions in `[76518,84561)` form a connected
grammar. Absolute and relative syntax have separate trailing query clauses
at `[77730,77803)` and `[79026,79099)`; their meaning does not stop at the
preceding list end. Keep the base-scheme switch, opaque-base fragment
restriction, empty-port alternative, file grammar, dot alternatives and
URL-code-point exclusions. IANA registration advice is a writing obligation,
not a parser rejection rule for unregistered schemes.

## Parser states and IDL

The basic parser owns `[85843,119012)`. Its state cases require the complete
`dt`/`dd` clauses, with immediate-parent links to that parser. Host and
hostname have consecutive definition headers and one shared body;
`[100436,103274)` must not be cut at the second `dt`. The opaque-path state's
legacy ID is `cannot-be-a-base-url-path-state`; retain its current meaning
and alias instead of turning the old name into another state.

The URL and URLSearchParams IDL headers carry exposure and legacy alias
attributes. Their individual member rows retain extended attributes,
nullability, default arguments, optionality, stringifiers and iterable
types. Exposure/conversion/host identity have their own boundary obligations;
a corresponding URL algorithm does not discharge them by mere name matching.

## Requirements and API hooks

Security considerations `[27370,28343)`, public-suffix advice
`[36873,37445)`, and the rendering sections from `[125864,126201)` onward
need explicit dispositions. Rendering includes credential suppression,
conditional scheme omission, registrable-domain visibility, label elision,
domain-to-Unicode, constrained percent-decoding and bidi embedding. Preserve
audience, conditions and modal force. They do not define one deterministic
serializer. Advisory UTR36/UTS39 references differ from normative BIDI.

The form format is an ordered tuple list `[130324,130534)`; link its UTF-8
conformance note `[131201,131481)` to parsing scope. URL's associated-slot
list is `[136535,136740)`; URLSearchParams' is `[152363,152702)`, including
empty-list/null initialization. These fields are direct list-item content,
so paragraph-only extraction loses their types.

API support requirements `[135376,135671)` distinguish browsers, JavaScript
implementations and other languages. URL APIs elsewhere constrain string
exposure/USVString `[159242,159585)` and naming `[159692,160022)`. The
idempotence goal `[1944,2321)` and round-trip prose require reviewed law
scope, rather than automatic exclusion as explanation.

`lt`, `oldids` and grammatical spelling variants can be aliases. Namespaced
API slots remain substantive even with `noexport`. Notes/examples may be
explanatory, but useful invariant, boundary and law evidence needs retained
links to its semantic owner. No blanket non-algorithm-prose exclusion is
justified by this review.

## U2b authored-input review receipt

The independent reviewer subsequently checked `census/url/spans.tsv` and
`census/url/explanations.tsv` against the raw pin. The containing intervals
retain validation-table failure columns and conditional qualifiers, complete
grammar lists and trailing query clauses, parser-state bodies, API field
types/initial values, and rendering context. Origins remain assigned to
their declared smallest owner in the immediate-parent interval forest.

The prose pass keeps idempotence, host/URL operation contracts, encoding
relations, external requirements and audience-specific advice as source
rows. Explanatory regions retain example and rationale links. Review corrected
one rationale's owner (`op.valid-domain`) and a partial closing-tag boundary
in the URLSearchParams example. A second pass found no outstanding defect.

The one-time independent reader found an assignment for every inventory
candidate and no unused explanatory region. These are bounded source-data
checks, not a repository gate, proof, disposition admission or denominator.
The strict Lean join currently has its own finite fixture battery; a later
packet must read the authored files and join all classification metadata.

## U2c metadata review receipt

The independent reader reviewed the disposition rules and the dependency
list for every authored span against the same raw pin. It found no wrong
disposition or invented external pin. The 29 IDL rows retain their binding
dependencies, URL wrappers stay locally owned, and external semantics remain
open under `docs/URL-DEPENDENCIES.md`.

The review identified and then confirmed three repairs: explicit Infra
surrogate/noncharacter dependencies for URL code points; code-point,
code-point-length and EOF dependencies for the parser pointer; and the
retained UTF-8 advisory dependency for byte percent-decoding. The latter is
not a decoder invocation by its byte loop. All external identities are used;
broad operation families still need exact declaration mappings.

U2c's Lean reader now validates these authored inputs and generates both
the census and candidate-assignment projections. An independent Python
`hashlib`/raw-byte pass agrees with every generated span, minimal unique
anchor, assignment and input digest. Neither the review nor these source
projections establish a URL execution theorem or a coverage numerator.
