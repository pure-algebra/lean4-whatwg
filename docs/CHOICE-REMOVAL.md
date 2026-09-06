# Classical.choice removal

Status: stopped at the user's request, 2026-09-05, starting at `8a2b608`. The user paused URL
implementation and made removing all `Classical.choice` the first priority.
The full URL goal remains intact. This file owns the work order and evidence
for that priority; the per-family records own their frozen statements and
receipts. Existing repository ceilings are not silently treated as success.

The first audit imports the current `WhatwgTest` root, enumerates compiled
declarations by their owning module, and calls `Lean.collectAxioms` for each.
It includes private/generated declarations and dependencies in types.
There is no direct authored invocation of `Classical.choice` in the flagged
declarations; transitive paths, not source-text searches, decide this work.

| Family | Initial evidence | Next action |
| --- | --- | --- |
| Infra integer ranges | All nine public range theorems and nine generated proof auxiliaries reach choice | Frozen proof-only repair in `docs/INFRA-INTEGER-CONSTRUCTIVE.md` |
| Infra string adapters and namespace constants | `JsString.ofLiteral`, `JsString.ofString` and six namespace definitions reach choice through native string traversal | Trace exact core proof paths and preserve the existing public behavior |
| HTML string escaping/rendering | Two escaper adapters and rendering operations/laws reach choice; several theorem statements mention `String.toList` | Distinguish local proof dependencies from dependencies already in frozen statements; investigate constructive core repair without weakening statements |
| Tests | Existing comma-split theorem statements and some finite fixture helpers inherit string dependencies | Retain the original statements and witnesses; repair their actual dependencies |
| Gate and audit implementation | Native String and metaprogramming dependencies remain | Trace exact external roots; do not claim removal by excluding tooling or changing receipts |

The earlier scalar/Char repair in `docs/INFRA-SCALAR-ASSURANCE.md` already
has constructive receipts for all nine retained declarations. It remains
part of the baseline and must not regress.

Completion requires an exhaustive current-state axiom audit with no remaining
choice dependency in the requested scope, preserved semantics and theorem
statements, passing repository checks and independent review. Any external
core restriction must be documented with its actual path; it does not become
an implicit exception or a completed removal.

## Stopping receipt

The user said to wrap up after the integer repair and before an isolated
standard-library rebuild. No core patch, toolchain change or rebuild was
started. URL implementation remains paused; do not resume either line of
work without a new user instruction.

All nine integer range proofs now satisfy the frozen constructive ceiling:
the five unsigned proofs have no axioms and the four signed proofs use
`[propext, Quot.sound]`. Their names, aliases, statements, bounds and
docstrings are unchanged. The exhaustive post-repair audit no longer
reports any declaration owned by `Whatwg.Infra.Primitive.Integer`.

Remaining dependencies are real, including occurrences in theorem types.
For stock Lean 4.33.1, the independently confirmed path is
`String.toList` → `String.Internal.toArray` → its validity proof →
`ByteArray.isSome_utf8Decode?_iff` → the private decoder-loop validity
theorem → `ByteArray.utf8DecodeChar?_eq_utf8DecodeChar?_extract` → a generated
iff proof → `Classical.propDecidable` → `Classical.choice`.
`String.fromUTF8?` and `ByteArray.utf8Decode?` reach the same root;
`String.ofList` itself has no axioms. String pattern-search proofs provide
another path in tooling. Replacing a local proof cannot clear a stock
constant already named in its unchanged theorem statement.

Source review identified possible constructive core proof replacements
(explicit cases for compound arithmetic goals and decidable logic lemmas),
but none was implemented or tested. Preserving existing theorem statements
while removing these imported dependencies would require separately pinned
proof patches and rebuilding the dependent core artifacts and their axiom
receipts. No audit exclusion or altered cache is a substitute for that work.
