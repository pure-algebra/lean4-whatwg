# URL source inventory review witnesses

The independent breaker freezes these witnesses before the scanner repair.
Their stable IDs are registered by the coordinator in
`test/counterexamples/REGISTER.md`; this companion describes the attacks,
while the executable sources remain in
`WhatwgTest/Url/Counterexamples/Inventory.lean`.

The attacked owner is `Gates.UrlInventory.scan`, governed by
`docs/URL-INVENTORY-INTERFACE.md`. These are finite executable tooling
probes contributing to `URL-PG-CENSUS` lexical evidence. They are not URL
semantic theorems, general parsing proofs, or host observations. The
existing frozen inventory contract and its base battery are unchanged.

## URL-INV-CE-001 — comma-containing owner is truncated

The definition source has `for='URL,URLSearchParams'` and `lt=x`.
The interface derives the owner from the normalized entire `for` value;
only `lt` selects its first alternative. The expected definition label is
`URL,URLSearchParams/x`, with the complete definition source span.

The reviewed implementation selects the first comma-separated portion of
`for`, yielding `URL/x`. This silently discards source ownership text.
The repair must preserve the normalized whole owner; it must not change
the frozen witness to accept the truncated result.

## URL-INV-CE-002 — form feed is omitted from whitespace normalization

ASCII form feed, U+000C, separates the class tokens `idl` and `example` in
one fixture and the visible text characters `a` and `b` in another.
The IDL source must emit the `interface Example {` header and the
`stringifier;` member with their exact source spans. The paragraph source
must emit visible label `a b` with its original source span.

The reviewed implementation fails to recognize the class-token boundary and
retains form feed in the visible label. The repair must apply the contracted
ASCII whitespace convention to both cases. The Lean source constructs form
feed with `String.singleton (Char.ofNat 12)` so the witness is explicit and
does not depend on unsupported string escape syntax.

## URL-INV-CE-003 — xmp raw text is mistaken for markup

One `xmp class=idl` fixture contains the raw generic member
`iterable<USVString, USVString>;`. It must emit that complete member and
the `interface Example {` header. A second spelling uses uppercase
`</XMP>` and must retain the same entries. Another fixture places apparent
`dfn` markup in an ordinary `xmp`; it must emit no definition because those
bytes are literal raw text.

The reviewed tokenizer attempts to parse the generic angle brackets as
markup and inventories fake definitions in ordinary `xmp`. The repair must
apply raw-text handling through the matching `xmp` close. It must retain the
normal markup treatment of `pre`. This interpretation of the existing
`xmp` support is recorded in the interface by the coordinator before repair.

## URL-INV-CE-004 — interface prefix admits unsupported headers

The supported IDL top-level form is an ordinary named interface, with
optional named inheritance as recorded in the interface contract. The
fixtures `interface {` and `interface mixin M {`, each inside a closed
`pre class=idl` block and followed by `};`, must return an error.

The reviewed scanner accepts both because it checks only the `interface `
prefix and the final opening brace. The repair must validate the declared
header form without broadening the packet into a full Web IDL validator.
These two negative probes add no new requirement on delimited member bodies.

## URL-INV-CE-005 — ordinary block tags do not terminate paragraphs

The fixtures `<p>a<section>b</section><p>c` and
`<p>a<form>b</form><p>c` must each emit precisely two prose candidates:
`<p>a` with label `a` and `<p>c` with label `c`. The text in the intervening
`section` or `form` does not acquire an inventory candidate of its own.

The reviewed scanner omits `section` and `form` from its paragraph boundary
set and consequently swallows the intervening container into the first
paragraph. The repair must follow the explicit block-name set in the
interface, retaining the exact paragraph spans fixed by these probes.

## Verification and retention

Narrow red/green command:

```text
lake build WhatwgTest.Url.Counterexamples.Inventory
```

All ten expected outputs are frozen `#guard` assertions. The eight positive
expectations use a private projection; the two header refusals match
`Except.error` directly. The private projection checks each row's byte
bounds and compares kind, label, section,
and exact source bytes. No expected label calls the production normalizer.
The initial and follow-up red runs are recorded in the breaker handoffs;
they must report
failed assertions against the existing scanner, rather than missing imports
or malformed Lean syntax. The coordinator records the result and later
repair status centrally.

The builder retains this file and the witness module, imports the module in
the test root, and removes its known-red entry immediately after the narrow
battery becomes green. Full build and actual axiom/gate receipts remain the
coordinator's responsibility. No general proof or axiom receipt is asserted
by the finite red run.
