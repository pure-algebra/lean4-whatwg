# ECMA-262 census inputs

Authored input to `lake exe census --standard ecma262`, seeded from the
ECMA-262 clause-disposition table of `SPEC-MANIFEST.md` as amended by rulings
R-P3, R-P5, R-P6, R-P9 and R-P11 in `COORDINATION.md`. The frozen packet is
`test/contracts/ecma262-census.contract.md`; it owns every count below and
this directory owns none of them.

Nothing here is coverage. A census row is a byte span of
`vendor/ecma262-0248456c/spec.html` with a joined disposition, and every row of
this standard is `absent` until `Whatwg.Ecma262` has a declaration.

| File | Role |
| --- | --- |
| `sections.tsv` | the two root clause ids that fix the scope |
| `dispositions.tsv` | `<clause id>` TAB `<kind or *>` TAB `<disposition>`, keyed on each row's innermost enclosing clause |
| `overrides.tsv` | the three rows whose clause-level disposition is right for their siblings and wrong for them |
| `rules.tsv` | present and entry-free: this standard emits no `rule` row |
| `dependencies.tsv` | one line per row, naming the identities it consumes |
| `externals.tsv` | the external identities those lines name, by escape treatment |

## Two facts a reader should not have to rediscover

**The twenty `<emu-note>` blocks are not rows at all**, so they never reach the
denominator. That is a deliberate difference from a naive "every block is a
row" reading: the census counts one primary row per clause plus sub-rows for
table bodies, requirement bullets and terms, and a note is prose inside the
clause row that contains it.

**The five promise instance slots are `owned` here while the Streams census
keeps the same named slots `foreignBoundary`.** The two censuses answer two
ownership questions about two libraries: DB-11 puts the promise carrier in
`Whatwg.Ecma262`, and the Streams rows become references into it when P8 opens.
Ruling R-P5 records this, and `census/README.md`'s "Foreign internal slots"
paragraph is the cross-reference.
