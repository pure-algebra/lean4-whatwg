# URL source inventory interface

U2a declaration record, 2026-09-05. This is tooling over source bytes, not a
URL semantic model or a coverage denominator. The unique owner is
`Gates.UrlInventory`. It uses the pinned `url.bs` from `SPEC-MANIFEST.md`;
the source digest is checked by its command-line gate. Existing
`Gates.Census.Row` describes classified census rows; this earlier inventory
retains source candidates before that classification and does not replace it.

## Frozen public scanner surface

```lean
namespace Gates.UrlInventory
inductive TokenKind where
  | text | comment | tag
  deriving Repr, BEq, DecidableEq, Inhabited
structure Token where
  kind : TokenKind
  b : Nat
  e : Nat
  name : String := ""
  closing : Bool := false
  selfClosing : Bool := false
  attrs : Array (String × String) := #[]
  deriving Repr, BEq, DecidableEq, Inhabited
inductive Kind where
  | definition | algorithm | idl | prose | table | list | heading
  deriving Repr, BEq, DecidableEq, Inhabited
structure Entry where
  kind : Kind
  b : Nat
  e : Nat
  label : String
  «section» : String
  deriving Repr, BEq, DecidableEq, Inhabited
def tokenize (bs : ByteArray) : Except String (Array Token)
def checkPartition (size : Nat) (tokens : Array Token) : Bool
def scan (bs : ByteArray) : Except String (Array Entry)
end Gates.UrlInventory
```

`[b,e)` is a UTF-8 byte span. Tokens cover the entire input, including text
and comments, in source order with no overlap, gap, or empty token. Empty
input has an empty valid partition. Tags support bare, single-quoted, and
double-quoted attributes and boolean attributes (stored with an empty value).
Quoted `>` is not a terminator. Malformed tags, comments, attributes, invalid
UTF-8, and unclosed inventory containers are errors. No fixed occurrence cap
may silently truncate the scan. This is a lexical Bikeshed-source reader,
not a general HTML parser or browser error-recovery algorithm.
`xmp` content is raw text up to its matching end tag (tag names are ASCII
case-insensitive): literal `<` in IDL generics is text, and apparent tags
inside it do not create source candidates. `pre` content uses ordinary markup.

Definition entries retain every `<dfn>`, including ignored and parameter
definitions. Their lexical span includes the opening and closing dfn tags;
it is not claimed to contain all text that gives the definition meaning.
Labels prefer `id`, then `for` plus the first `lt` alternative, then `for`
plus visible text. The owner separator is `/`; absent/empty owner contributes
no prefix. Markup is removed from visible text and whitespace is normalized.
Algorithm entries retain the entire balanced `<div algorithm>`, preferring
its nonempty `algorithm` value as label, then `id`, then its first definition's
label. Tables and ordered/unordered/definition lists retain their entire
balanced containers. Paragraph spans stop at the next block tag or explicit
paragraph end, following the source's optional paragraph closing tags.
For this lexical reader, paragraph block boundaries are opening or closing
tags named `address`, `article`, `aside`, `blockquote`, `body`, `caption`,
`center`, `colgroup`, `dd`, `details`, `dialog`, `dir`, `div`, `dl`, `dt`,
`fieldset`, `figcaption`, `figure`, `footer`, `form`, `h1` through `h6`,
`head`, `header`, `hgroup`, `hr`, `html`, `li`, `listing`, `main`, `menu`,
`nav`, `ol`, `p`, `pre`, `search`, `section`, `summary`, `table`, `tbody`,
`td`, `tfoot`, `th`, `thead`, `tr`, `ul`, and `xmp`. This is a source-scanning
boundary vocabulary; it is not a CSS display computation or an HTML tree builder.
Table/list labels are their lowercase tag name. Prose and heading labels
are the visible inner text with tags removed and whitespace normalized;
entities retain their source spelling rather than being HTML-decoded.
Lexical whitespace normalization and class-token separation include all five
ASCII whitespace characters: tab, LF, form feed, CR, and space.
Headings retain the full element; `section` is the nearest preceding heading's
`id` (empty when absent), including the heading itself for heading entries.

IDL is read from `pre` or `xmp` with `idl` among the class tokens. Accumulate
complete source lines until an interface header ending `{`, an interface
close `};`, or a member ending `;`. Emit interface headers and every member;
closing `};` emits no row. Preserve extended attributes in the header/member
span and label; normalized full statement text is the label.
IDL spans start at the first non-whitespace byte of the first statement line
and end after the last non-whitespace byte of the terminating line; the final
line ending is excluded. Intermediate whitespace and line endings are retained.
Unrecognized top-level forms, missing terminators, and unclosed interfaces are errors.
Inside an interface, retain every delimited member without validating the full
Web IDL grammar. Paragraphs may terminate at EOF or a containing block's closing tag.
The fixed URL source only has interfaces; other top-level IDL declarations
require a later contract extension. Semicolons in `&lt;` do not end a line.
An ordinary header is `interface Name {`, optionally `interface Name : Base {`,
after any extended attributes. Names are nonempty ASCII identifiers starting
with a letter or underscore and continuing with letters, digits, underscores,
or hyphens. An unnamed interface or an `interface mixin` is not a supported
header. This limited header recognition does not validate interface members.

Entries are sorted by byte start, then `Kind` constructor order. Projection
row ordinals identify candidates at this pin only; they are not semantic
declaration IDs. U2 must separately join every candidate to a reviewed
classification, containing semantic span, dependency/parent relationship,
and stable census identifier. Whole-source token coverage and candidate
counts do not prove that prose has been classified correctly.

## Assurance route

This tooling contributes to `URL-PG-CENSUS`, whose semantic coverage and
cutover obligations remain open in `docs/URL-CENSUS-DAG.md`.
U2a closes only lexical inventory evidence:
a separate breaker freezes finite positive and rejection probes before
implementation; the gate checks the input digest, token partition, full
fixed-pin candidate inventory, and deterministic projection; the common
module and axiom gate audits all tooling declarations. No theorem of lexical
HTML parsing or of URL semantics is claimed by a passing finite probe.

All generated constructors, recursors, projections, instances, and private
scanner helpers inherit this tooling ownership and the same assurance scope.

`Gates.UrlInventory.cli : List String → IO UInt32` is the command-line helper
for this same tooling owner. Its private generation/check helpers check the
source pin, token partition, independent fixed-pin candidate counts, valid
entry spans and nonempty definition/algorithm labels. It emits
`generated/url-source-inventory.tsv` with kind, byte bounds, span SHA-256,
label, and section for every candidate. `lake exe urlinventory --write`
regenerates; `lake exe urlinventory` checks exact projection bytes. Token
partition validation is performed on each run; the projection lists source
candidates, not a semantic classification of every source byte.
