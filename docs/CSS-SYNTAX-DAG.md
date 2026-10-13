# CSS syntax assurance graph (`CSS-PG-SYNTAX`)

Status: open, 2026-10-12. This document owns the graph for the tokens of CSS: the tokenizer, the
writer of tokens, and the round trip between them. `docs/CSS-PACKAGE-PLAN.md` owns the slices and
the rulings CS-1 to CS-10.

**Authority.** CSS Syntax Module Level 3, sealed at
`vendor/w3c-csswg-drafts-50337328/css-syntax-3/Overview.bs`: the algorithms under the heading
`tokenizer-algorithms`, and the section `serialization` with its table of pairs. How an identifier
and a string are written comes from CSSOM, sealed beside it (`cssom-1/Overview.bs`), with one rule
changed where that text does not round-trip with the tokenizer.

**Why a graph.** The tokenizer is an interpreter of the standard's algorithms, and the round trip
is a relation between a writer and a reader. Both are over the threshold of
`docs/AGENT-ROUTING.md`.

**What is proved.** For every list of tokens that passes the test `Writable`, tokenizing what the
writer wrote gives the tokens back, with each run of white space as one token
(`tokenize_serialize`), and exactly the tokens where no two white space tokens are adjacent
(`tokenize_serialize_eq`). That is the one requirement the standard makes of serialization.

**What the proof found in the sealed text.** The table of pairs is a note, and it misses two
cases. The identifier `--` before the delimiter `>` reads as the token that closes a comment of
HTML. The delimiters `<` and `!` before anything that opens with `--` read as the token that
opens one. The writer puts a comment in both places (`extraPairs`), apart from the sealed table.

**What is open.** The ledger lists it by edge. In short: tokens outside `Writable` (a URL token,
a unit that needs an escape, a range of code points); the parser and the tree of rules (slice
K4); the census of the standard's algorithms, so that coverage is reported and not claimed; the
gate that compares the writer's table with the extractor's.

The current state of every edge is `generated/graphs/CSS-PG-SYNTAX.md`, the projection of the
ledger module `WhatwgTest/Ledger/CssSyntax.lean`. The history is
`docs/receipts/CSS-PG-SYNTAX.md`.