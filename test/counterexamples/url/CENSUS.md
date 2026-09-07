# URL census assignment review witnesses

The independent breaker freezes these finite tooling probes before repair.
The coordinator owns the stable row in `test/counterexamples/REGISTER.md`;
the executable witness remains in
`WhatwgTest/Url/Counterexamples/Census.lean`.

## URL-CEN-CE-001 — form feed is accepted as an explanation

The attacked declaration is `Gates.UrlCensus.assign`, governed by
`docs/URL-CENSUS-INTERFACE.md`. An explanatory region must have a reason
containing something beyond ASCII whitespace. That vocabulary includes tab,
LF, form feed, CR and space.

Both fixtures use source `<dfn id=x>x</dfn>`, no semantic rows, no external
identities, and a region spanning bytes `[0,17)`. One reason consists only
of U+000C form feed; the other mixes all five ASCII whitespace characters.
Both calls must return `Except.error`. Exact diagnostic wording is not
frozen.

The reviewed implementation checks `Char.isWhitespace`, which does not
recognize form feed, and consequently accepts both otherwise blank reasons.
The repair must use the contracted whitespace vocabulary. The retained
witness constructs U+000C explicitly with `String.singleton (Char.ofNat 12)`
and matches `Except.error` directly; it does not derive its expectation from
the production whitespace check.

## Verification and scope

The narrow red/green command is:

```text
lake build WhatwgTest.Url.Counterexamples.Census
```

The breaker handoff records the pre-repair commit and actual failing
assertions. The builder retains both probes, adds the module to the test
root, and removes its known-red entry immediately after it becomes green.
The existing `WhatwgTest.Url.CensusContract` remains unchanged.

These finite executable refusals contribute tooling evidence to the open
`URL-PG-CENSUS` graph. They assert no URL semantic theorem, general join law,
coverage denominator, host result or axiom receipt. Full build and actual
axiom/gate receipts remain the coordinator's responsibility.
