# URL authored census input review witnesses

The independent breaker freezes these finite tooling probes before repair.
The coordinator owns the stable row in `test/counterexamples/REGISTER.md`;
the executable witness remains in
`WhatwgTest/Url/Counterexamples/CensusInput.lean`.
The original U2c contract and battery remain frozen and unchanged.

## URL-INP-CE-001 — a retained carriage return is stripped twice

The attacked declarations are `Gates.UrlCensusInput.build` and its dependent
`project`, governed by `docs/URL-CENSUS-INPUT-INTERFACE.md`. LF separates
authored lines and exactly one terminal CR per line is removed. Other field
text is retained verbatim; disposition tokens use the canonical vocabulary.

The fixture source is `<h2 id=s:1>H</h2><dfn id=x>x</dfn>`, 34 ASCII bytes.
It has a structural heading at `[0,17)` and a definition at `[17,34)`.
One `type.x` row owns origin 2, spans `[17,34)`, and has no parent or
dependencies. Its sole disposition rule is for section `s:1` and kind `type`;
all other authored inputs are empty except the required dependency entry.
The source positions, row fields and two assignments are independent literals.

Two positive assertions require `owned\r\n` and `owned\r` at the end of
the disposition line to produce that exact row and those exact assignments.
Two refusal assertions require `owned\r\r\n` and `owned\r\r` to return
`Except.error`: removing one terminal CR leaves a CR in the disposition
token, which is not the canonical `owned` spelling. A fifth assertion
requires `project` to reject the double-CRLF input as well. Diagnostic text
is not frozen, and a production parser computes no expected value.

The reviewed implementation calls `Gates.Common.lines` in `dataLines`,
then LF-joins the normalized lines and calls `Gates.Census.parseDispositions`.
That parser calls `Gates.Common.lines` again and removes the retained CR.
Consequently both malformed disposition inputs are accepted and can be
projected. The repair must preserve the already-normalized field text when
reusing the canonical parser, without rejecting normal CRLF inputs.

## Verification and scope

Frozen against the U2c implementation present after breaker base
`9e545357de635b5cccc6fe76cec934ec0253318c`. The implementation was still
uncommitted at review; the coordinator retains responsibility for its landing.
The exact pre-repair `Gates/UrlCensusInput.lean` bytes have SHA-256
`663871589702d186765ad916877a8ab076e20f1268eed3fa1a52d79b3983b82d`,
measured independently with PowerShell `Get-FileHash -Algorithm SHA256`.
This identifies the reviewed implementation beyond the committed base.
The narrow red/green command is:

```text
lake build WhatwgTest.Url.Counterexamples.CensusInput
```

The breaker commits this record, the new Lean module, its known-red entry
and its exact coordination claim before running the authorized narrow red
check. The handoff records the actual assertion failures and stopped process.
The builder keeps all five probes, imports the module into the test root,
and removes its known-red entry when green.

These finite executable format probes contribute tooling evidence to the
open `URL-PG-CENSUS` graph. They grant no URL semantic theorem, parser law,
coverage state, external semantic assurance or axiom receipt. CLI filesystem
integration, default build and actual axiom/gate receipts remain separate
coordinator checks.
