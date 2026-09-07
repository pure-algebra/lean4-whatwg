# Census source-profile identity contract (P8-C0)

Status: FROZEN / RED, promise census breaker seat, 2026-09-06, based on
`03abfc579883d1c79492b0e4d1e933f71a830e68`.

Ruling R-P1 in `COORDINATION.md` replaces `Gates.Census.Standard.definitionKeyed
: Bool` with a source profile. This packet is the regression that the refactor
buys nothing at the cost of the two censuses that already exist. It freezes
`WhatwgTest/Audit/CensusProfileIdentity.lean` before that refactor. The builder
may repair elaboration but may not weaken, delete or replace a frozen digest,
count or spelling.

## Claim boundary

This is a tooling identity contract. It grants no coverage state, no
denominator, no Streams or Infra semantic claim and no host observation. It
says one thing: after the R-P1 refactor, the same four bytes-on-disk come out
of the generator.

## The acceptance condition

After the refactor, in a clean tree,

```text
lake exe census
lake exe census --standard infra
```

both print `PASS` — that is, each regenerates its two projections in memory
and finds them byte-identical to the files on disk — and

```text
lake exe census --write
lake exe census --standard infra --write
```

leave the working tree unchanged. The four files and their frozen identities
are:

| Path | Bytes | SHA-256 |
| --- | --- | --- |
| `generated/spec-algorithm-census.tsv` | 141352 | `1a3672789fb62d3ae68eb528efb20a211727e9ed2b18c3e751c5acf67cd37e02` |
| `generated/infra-census.tsv` | 55766 | `5041ef0035e087cb242a300a95398982351d766b39a4f24f28e94d9b853d5b18` |
| `WhatwgTest/Audit/SpecCoverageRows.lean` | 32032 | `d0e47fdfefdf412b88a51cfcbfa2ec573d6a8092faaba3462f68468ecb377476` |
| `WhatwgTest/Audit/Infra/SpecCoverageRows.lean` | 10607 | `94b04b5a9c23af20bc101be9504e2ccbd54b3e0002ccfb5ffd73c92ff7eef7b0` |

Each digest was computed with .NET
`System.Security.Cryptography.SHA256.ComputeHash` over
`[IO.File]::ReadAllBytes` of the working tree at the base commit. The battery
recomputes each one with `Gates.Sha256.hexDigest`, so the identity rests on two
implementations of SHA-256.

## The header format and the row-kind spellings

Neither header line moves:

```text
#census format=1 generator=Gates.Census input=vendor/whatwg-streams-b9ba9f49/index.bs input-sha256=24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440 rows=450 regenerate=lake exe census --write
#census format=1 generator=Gates.Census input=vendor/whatwg-infra-3f984adc/infra.bs input-sha256=7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb rows=176 regenerate=lake exe census --standard infra --write
```

`Gates.Census.formatVersion` stays `"1"`. The row line stays
`kind|id|anchor|start|end|sha256|excerpt` with `Gates.Census.escapeField`
escaping over `\`, `|`, LF, CR and tab. The six existing `Gates.Census.Kind`
constructors keep their spellings and stay at the head of `Kind.all`, so the
sort key `kind.name ++ "|" ++ id` of every existing row is unchanged and the
seven new ECMA-262 kinds of R-P2 cannot reorder either file:

| Standard | rows | idl | op | requirement | rule | slot | type | rowTotal | denominator |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Streams | 450 | 133 | 248 | 7 | 0 | 62 | 0 | 450 | 410 |
| Infra | 176 | 0 | 150 | 0 | 0 | 0 | 26 | 176 | 165 |

## The profile the two standards must declare

The battery ascribes these exact names and pins the two existing records
through them.

```lean
#check (@Gates.Census.Bikeshed : Type)
#check (@Gates.Census.Profile : Type)
#check (@Gates.Census.Profile.bikeshed : Gates.Census.Bikeshed → Gates.Census.Profile)
#check (Gates.Census.Profile.ecmarkup : Gates.Census.Profile)
#check (@Gates.Census.Standard.profile : Gates.Census.Standard → Gates.Census.Profile)
```

`Gates.Census.Standard.profile` occupies the field position
`definitionKeyed` occupies today. The two existing values are:

| Switch | `streams` | `infra` |
| --- | --- | --- |
| `algorithmRows` | `true` | `false` |
| `definitionRows` | `false` | `true` |
| `idlRows` | `true` | `false` |
| `slotRows` | `true` | `false` |
| `requirementMarker` | `some "<div algorithm=\"ReadableStreamPipeTo\">"` | `none` |
| `sectionScope` | `false` | `false` |
| `headingLevels` | `(2, 4)` | `(2, 4)` |
| `idlOpeners` | `#[("<xmp class=\"idl\">", "</xmp>")]` | `#[]` |

`streams.slotRows` is `true`: the Streams census has 62 `slot` rows and they
must survive. `Gates.Census.standards` keeps `streams` and `infra` as its first
two entries, in that order.

## What the refactor may and may not change

- `scanRequirements` must become gated on `requirementMarker`. It is called
  unconditionally today, and it opens with a literal search for
  `<div algorithm="ReadableStreamPipeTo">`, so any second Bikeshed standard
  aborts the whole run. The seven Streams `requirement` rows must be unchanged
  after the gating.
- `scanOps` and `algorithmBlocks` must key on a `<div>` tag that carries an
  `algorithm` attribute anywhere in its tag, not on the byte prefix
  `<div algorithm`. Recomputed on the sealed bytes at this pin: the Streams
  source has 248 such tags under either rule and the Infra source has 18 under
  either rule, so the change is byte-neutral for both and the Web IDL source
  gains the 45 blocks that write `id=` first.
- `scanIdl` must take its block openers from the profile. `#[("<xmp
  class=\"idl\">", "</xmp>")]` reproduces today's behaviour exactly.
- `scanHeadings` must take its level range from the profile. Recomputed at
  this pin: the Streams source has 132 line-opening headings at levels 2 to 6
  and the Infra source has 40, and **none** of either carries a Bikeshed
  definition marker, so admitting `<h5>` for another standard and reading
  heading-borne definitions are both byte-neutral here.
- `scanDefinitions` may gain the span-ladder steps the Web IDL packet freezes
  (enclosing `<tr>`; a Bikeshed markdown list-item line; a markdown list after
  a colon; the paragraph opener clamped to the definition's own blank-line
  chunk). Recomputed at this pin: the Infra source has 0 `<tr>`, 0 `<td>` and
  0 `<table>`; 0 of its 197 `<dfn>` sit on a markdown list line; 0 of its 177
  non-block `<dfn>` have a last paragraph opener earlier than their own chunk;
  and of its 23 colon-branch definitions, 21 are followed immediately by
  `<ol` and the other two by `<p`, never by a markdown list. Every one of the
  four steps is therefore vacuous on Infra.
- `parseRules` may gain the optional third field of R-P4. Both
  `census/rules.tsv` and `census/infra/rules.tsv` hold only comments and both
  projections carry zero `rule` rows, so the format extension is vacuous here.
- `Gates.Census.Kind` may gain the seven R-P2 constructors, appended after the
  existing six.

Anything that changes one of the four digests is a failure of this packet,
repaired in the generator, never by regenerating the projection.

## Fence and verification

Frozen breaker files:

- `test/contracts/census-profile-identity.contract.md`
- `WhatwgTest/Audit/CensusProfileIdentity.lean`

Red-phase registration: `test/fixtures/trust-gate/known-red.txt`, entry
`WhatwgTest.Audit.CensusProfileIdentity`, removed by the builder the moment
the battery is green. The breaker edits no implementation, no vendored bytes,
no generated projection and no authored census input.

Narrow command:

```text
lake build WhatwgTest.Audit.CensusProfileIdentity
```

## Freeze receipt

Observed in the breaker's worktree at the base commit, on Lean 4.33.1,
Windows x64. `lake --wfail build Whatwg Gates` completes 163 jobs with exit
code 0, so the baseline the packet is frozen against is green.

`lake build WhatwgTest` reports exactly three failing targets,
`WhatwgTest.Audit.CensusProfileIdentity`,
`WhatwgTest.Audit.WebIdl.CensusContract` and
`WhatwgTest.Audit.Ecma262.CensusContract`, which is exactly the declared red
set. `lake build WhatwgTest.Audit.CensusProfileIdentity` fails on its own.

Because Lean's `maxErrors` is 100 and is read once per file, the packet's
diagnostics were also collected with `lake env lean -DmaxErrors=5000` on the
same file, which reports the complete list: **17 errors, 0 warnings**. Every
one is one of these, and no other error class appears:

| Count | Diagnostic |
| --- | --- |
| 8 | `Unknown identifier 'Gates.Census.Bikeshed'` / `'Gates.Census.Profile'` / `'Gates.Census.Profile.bikeshed'` / `'Gates.Census.Profile.ecmarkup'`, in the five `#check` ascriptions of section 1 |
| 1 | `Unknown constant 'Gates.Census.Standard.profile'` |
| 4 | `Invalid field 'profile': The environment does not contain 'Gates.Census.Standard.profile'`, from the two `#guard`s over `streams.profile` and `infra.profile` |
| 2 | `Invalid dotted identifier notation: The expected type of '.bikeshed' could not be determined`, a consequence of the same missing field |
| 2 | `cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors`, the same two `#guard`s |

No probe in section 2 or section 3 of the battery fails: the six existing kind
spellings, the two regeneration commands, the standard order, the four frozen
digests and sizes, both header lines, both row counts, the per-kind counts and
both `rowTotal`/`denominator` pairs all pass today. The identity gate prints

```text
census profile identity: 4 frozen files, Streams 450 rows / denominator 410, Infra 176 rows / denominator 165
```

so the identity half of this packet is already green and the refactor has to
keep it that way. The only red is the absent profile.

The `Gates/` tree and the semantic/test tree share one axiom ceiling under
ruling R-11 (`WhatwgTest/Audit/AxiomGate.lean` gives `allowedAxioms` and
`implementationAxioms` the same three names), so this battery's
elaboration-time command needs no entry in `auditImplementationModules`.
