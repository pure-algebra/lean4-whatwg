# Infra counterexamples

## WS-INFRA-CE-001 — a trailing comma does not add an empty token

The former `Whatwg/Infra/Text/Scan.lean` example asserted that splitting
`" a , ,b,"` on commas yields `['a', '', 'b', '']`. The pinned Infra
`split on commas` steps yield `['a', '', 'b']`: after the final token the
algorithm advances past the last comma, and the loop's end check prevents
another token. The implementation already transcribes that loop.

The independently reviewed repair changes the false example, not the
implementation. `WhatwgTest/Streams/Counterexamples/Infra/Split.lean` retains
the negation of the old claim and its exact positive result. The `",,"`
pair discriminates comma splitting (two empty tokens) from strictly
splitting (three); whitespace and empty-input controls separate the other
boundary cases. These are finite probes, not a general equivalence theorem.

Authority: the `op.split-on-commas` and `op.strictly-split` span digests in
`generated/infra-census.tsv`, generated from `whatwg/infra` `3f984adc`.
Evidence command: `lake build WhatwgTest.Streams.Counterexamples.Infra.Split`.
The full `INFRA-PG-TEXT` proof obligations remain open.
