# lean4-whatwg

WHATWG standards reified in Lean 4, one library per standard: `Whatwg.Streams`, the Streams Standard; `Whatwg.Infra`, the Infra Standard's value universe (bytes, code points, strings and text helpers, with the Encoding Standard's UTF-8 codec in `Whatwg/Infra/Text/Utf8.lean`); `Whatwg.Ecma262` and `Whatwg.WebIdl`, the ECMA-262 promise objects and job queue and the Web IDL promise and exception vocabulary beneath Streams (ruling DB-11); `Whatwg.Url`, the URL Standard, whose percent-encoding packet is its first semantic declaration set; and `Whatwg.Html`, the HTML content model under the HTML Standard's authority, whose schema was bootstrapped from OCaml TyXML's row types and is authored source since 2026-09-06 (`docs/HTML-PACKAGE-PLAN.md`). The Streams library: the specification's
algorithms and internal state as first-order Lean data with proved laws, a
relational semantics over explicit decisions, an EffHOL-style logic layer
above it, and, later, a checked lowering of a closed combinator alphabet to
TypeScript.

The semantic authority is the specification source, `index.bs`, at one pinned
commit. The specification's own reference implementation is second-tier
evidence. Web Platform Tests are the host conformance corpus, replayed against
named host profiles. No host defines the model.

Current state at the review lane V landing, 2026-10-01: pre-release. The package
builds, the Lean-implemented gates run, the pinned sources are sealed, and the
libraries hold first-order models with proved laws for one bounded
representative per area: queue-with-sizes and the queuing strategies (P3), a
default readable stream after successful start (P4a), a default writable stream
with one attached writer (P5a), transform backpressure coupling (P6a), a
forward-error pipe shutdown fragment (P7a), the ECMA-262 promise objects and job
queue with the Web IDL promise and exception vocabulary (promise slices Q3 and
Q3b), the configuration-ordering restatement of P8a (Q4), the Infra text helpers
with the UTF-8 codec, URL percent-encoding (U3), and the HTML content model
(H1 to H4). Each representative is part of its phase, not the whole of it:
the graph ledger under `WhatwgTest/Ledger/`, rendered per graph in
`generated/graphs/`, names each graph's open edges, and `PLAN.md` keeps P4 to
P12 open. No host conformance is
claimed; the harness fixtures are finite observations under named host
profiles. Specification coverage is stated only by the blocks
`lake exe whatwg_census --report` prints. Review lane V (2026-09-30 to
2026-10-01) changed no theorem statement: it made every declaration of
`Whatwg.Ecma262`, `Whatwg.WebIdl`, `Whatwg.Url`, `Whatwg.Streams` and
`Whatwg.Infra.Text.Utf8` reach at most `propext` and `Quot.sound`, a ceiling
the axiom gate now enforces for those module prefixes, and hardened that gate
(`test/contracts/trust-gate-hardening.contract.md` states what it refuses and
what it does not catch);
`PLAN.md` records its slices.

## Build and gates

The toolchain is pinned by `lean-toolchain` to exactly
`leanprover/lean4:v4.33.1`. Three Lake dependencies, each at an exact commit:
`hash` ([lean4-hash](https://github.com/pure-algebra/lean4-hash)) at
`c906b15`, the proved SHA-256 every gate computes digests with; `effects`
([lean4-effects](https://github.com/pure-algebra/lean4-effects)) at `a4ee7a1`
(tag `v0.8.0`), the generic effect algebra the reification strategy builds the
stateful standards against; and `typescript`
([lean4-typescript](https://github.com/pure-algebra/lean4-typescript)) at
`6afc9b8` (version 0.6.0, untagged), the TypeScript syntax P11 lowers through.
These are lean4-effect4's pins (ruling R-V3(b)). The `WhatwgGates`
tooling imports `hash`; under `Whatwg/`, only the `Effects.Signature` face of
the ECMAScript agent, `Whatwg/Signatures/Ecma262.lean` in the library
`WhatwgSignatures`, imports `effects` (`Effects.Algebra.Sum`), and nothing
imports `typescript` yet. Every proof receipt in this
repository is stated against that kernel. Everything below runs from any directory inside the
checkout.

```text
lake build                                         # libraries, the elaboration-time axiom gate, the gate executables
lake build WhatwgStreams                           # one standard's library and its import closure; likewise WhatwgInfra, WhatwgEcma262, WhatwgWebIdl, WhatwgUrl, WhatwgHtml, WhatwgSvg
lake exe whatwg_vendorseal                         # vendor/ against generated/vendor-manifest.tsv, both directions
lake exe whatwg_citations                          # no line-numbered citation into a protected authored document
lake exe whatwg_urlinventory                       # generated/url-source-inventory.tsv against a regeneration from the sealed URL source
lake exe whatwg_urlcensus                          # the authored URL census and its source assignments against a regeneration
lake exe whatwg_htmlstandard                       # generated/html-standard-*.tsv and the generated Whatwg/Html/Schema modules against the sealed HTML Standard source
lake exe whatwg_svgdefinitions                     # generated/svg-*.tsv and the generated Whatwg/Svg/Schema modules against the sealed SVG 2 definitions
lake exe whatwg_census                             # the Streams census and coverage emit
lake exe whatwg_census --report                    # the Streams coverage block from the Lean emit
lake exe whatwg_census --standard infra            # the Infra definition census
lake exe whatwg_census --standard webidl           # the Web IDL promise and exception census
lake exe whatwg_census --standard webidl --report  # the Web IDL coverage block, all-absent
lake exe whatwg_census --standard ecma262          # the ECMA-262 promise and job census
lake exe whatwg_census --standard ecma262 --report # the ES2026 coverage block, all-absent
lake exe whatwg_trustgate                          # after lake build: the axiom gate's passes over the built modules, run from outside the tree
lake exe whatwg_ledger                             # after lake build: the graph ledger's references, and generated/graphs against a fresh rendering
lake exe whatwg_declsnapshot                       # after lake build: generated/declarations against a fresh snapshot of the production libraries
lake exe whatwg_trustselftest                      # planted trust-gate violations are each refused for the frozen reason
lake env leanchecker Whatwg WhatwgTest WhatwgGates # every built module under those three prefixes replays in the kernel
```

Every gate is Lean. Shell files, where they exist, only orchestrate.

`lake exe whatwg_trustselftest` (not a default target) plants known violations
in a throwaway copy and checks that the axiom gate rejects each. It tests the
gate's own code, so it runs after a change to the gate, its configuration, its
fixtures, `lakefile.toml` or a pin, and in CI from its own workflow on those
paths (ruling R-W25); it is not part of every change. The WP-7 rename-parity receipt was
retired on 2026-09-03: it had proved what it was written to prove.

## Where to start

- [`AGENTS.md`](AGENTS.md) routes all work in this repository.
- [`PLAN.md`](PLAN.md) owns the phases, their exit gates, and the current phase.
- [`SPEC-MANIFEST.md`](SPEC-MANIFEST.md) owns the authority pins and the
  section-by-section dispositions of the specification.
- [`docs/DESIGN-BASIS.md`](docs/DESIGN-BASIS.md) records the adopted
  architecture and the role of each primary source, including EffHOL.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) owns module boundaries.
- [`docs/PROVENANCE.md`](docs/PROVENANCE.md) records every pin with its
  digest, fetch command, and cross-check.
- [`docs/HASH-PACKAGE-PLAN.md`](docs/HASH-PACKAGE-PLAN.md) records the
  extraction of the SHA-256 lane and foldlab's SHA3-512 into lean4-hash, the
  shared proved hash library this repository now depends on; its
  `docs/SHA256-DAG.md` is the proof graph.
- [`docs/REIFICATION-STRATEGY.md`](docs/REIFICATION-STRATEGY.md) is the
  draft cross-standard design: three strata of one effects algebra, the
  specification dependency graph as a handler tower, two realizers per
  signature. A living document under refinement.
- [`docs/research/README.md`](docs/research/README.md) indexes the research
  passes and the findings decisions rest on.

## Process

This repository follows the breaker/builder discipline developed in
[lean4-effect4](https://github.com/mepuka/lean4-effect4): a contract packet
and red battery are frozen by a separate process before any implementation,
every declaration-changing counterexample receives a stable ID, every
semantic owner closes a ten-edge proof graph, and no claim uses the words
"sound", "equivalent", "preserves", or "complete" without naming the exact
judgment, observation mask, theorem, assumptions, and remaining host boundary.

## Licensing of vendored material

`vendor/whatwg-html-746f2ede/` carries the HTML
Standard source (CC-BY 4.0). `vendor/whatwg-streams-b9ba9f49/` carries the WHATWG Streams Standard source
(CC-BY 4.0, with BSD-3-Clause for portions incorporated into source code) and
its reference implementation (dual CC0 / MIT). `vendor/wpt-480fdfcd/` carries
the Web Platform Tests `streams/` directory (BSD-3-Clause).
`vendor/whatwg-webidl-a652053f/` carries the Web IDL Standard source and
`vendor/whatwg-encoding-67494fce/` the Encoding Standard source (both CC-BY
4.0). `vendor/ecma262-0248456c/` carries the ECMAScript 2026 specification
source under Ecma International's text copyright policy, read as a
specification source and never redistributed as a derived document. Each tree
keeps its upstream license file. Nothing under `vendor/` is edited.
