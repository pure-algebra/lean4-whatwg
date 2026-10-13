# Receipts log of `CSS-PG-SYNTAX`

This log holds the history of `docs/CSS-SYNTAX-DAG.md` (ruling R-V4). The current state of every
edge is the ledger module `WhatwgTest/Ledger/CssSyntax.lean`.

## Slice K2, 2026-10-12

The graph opened. Slice K3 had landed the tree of tokens (`Whatwg/Css/Syntax/Tree.lean`) a
commit earlier. Slice K2 landed the tokenizer, one function for each algorithm of the standard
(`Tokenize.lean`); the writer of tokens with the table of pairs (`Serialize.lean`); seven modules
of laws by kind of token (`Laws/`); and the round trip (`Laws.lean`). Ruling R-S36 of
`COORDINATION.md` records what landed, the commands run and their results. No edge closed.

## Slice K4, 2026-10-13

The fence grew by twelve modules. Slice K4 landed the tree as tokens and text (`Write.lean`),
the parser, one function for each algorithm and entry point of the chapter `parsing`
(`Parse.lean`), the premises of its laws as tests that compute (`Readable.lean`), six modules of
laws from a component value to the lines of a stylesheet (`Parse/`), and the fold that gives
each declaration with the rules it stands under (`Located.lean`). With it landed the builders of
values and their laws (`Build.lean`, `Build/Laws.lean`), on which the picture kit now writes.
The item "the parser of the standard is not modelled" left the semantics edge; the item about
preprocessing left the laws edge, proved under `writableText`. Ruling R-S42 of `COORDINATION.md`
records what landed, the commands run and their results. No edge closed.
