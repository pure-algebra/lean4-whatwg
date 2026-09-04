# Where `Whatwg.Html` spends its elaboration budget

Performance review, 2026-09-03, by a read-only Opus agent at the operator's
request after slice H7.3 of `docs/HTML-PACKAGE-PLAN.md`. It establishes no
semantic claim. Every number below was measured against this repository at
commit `e278982` ("H7.3: attribute-dependent categories"); every unverified
statement is marked INFERRED.

**State measured, so you can reproduce.** Work started while another seat was
landing H7.3; the object files were rebuilt at 22:16–22:17 and every number in
this report was taken after that, against a working tree that is now exactly
`e278982` (`git status --short` empty, `git diff | shasum -a 256` the empty
digest). This matters because H7.3 changed the shape of the per-node
obligation: `Ctx.admits ctx t` became `Ctx.admitsWith ctx t (rawAttrs e.attrs)`
(`Whatwg/Html/Node/Typed.lean:98`, `Whatwg/Html/Node/Combinators.lean:41`), and
the five baselines quoted in the brief moved with it: 317 → 353, 478 → 490,
136 → 143, 675 → 681, 234 → 250. The brief's numbers are the pre-H7.3 ones.

**Method.** Nothing under `Whatwg/`, `Gates/`, `WhatwgTest/` or `generated/`
was modified. Every experiment is a throwaway file under the scratchpad,
compiled with `lake env lean`. `lake build` was not run (another seat ran one
at 22:16; that build is what the measurements sit on). Three instruments,
which do not see the same thing — §1 explains why, and it is the single most
important methodological fact in this report.

---

## 0. Executive summary

Ranked by measured saving times breadth, divided by risk.

| # | Recommendation | Measured saving | Risk |
| --- | --- | --- | --- |
| R1 | Give `Seq.deriv` smart constructors (or generate a DFA). The derivative terms are never simplified, so a `<dl>` of 100 groups costs **9.3 s** of kernel time and a `<table>` of 100 rows **1.6 s**; the growth is between quadratic and cubic in the child count. With smart constructors the derivative term size is **constant** (5 for `table`, 9 for `dl`, at every length measured) instead of 1516 at 32 `tr` and 3395 at 16 `dt`/`dd` pairs. | `dl` 100: 9.28 s → O(n) kernel; heartbeats 3387 → INFERRED linear | medium: `seqOk` is part of the definition (HP-13), so the new matcher needs an agreement theorem |
| R2 | Replace the two linear scans behind one attribute: `Attr.ofName?` (a 234-arm `String` match) and `rowsFor` (a `filter` over 271 rows). Measured **49 ms** and **32 ms** of kernel time per distinct attribute per declaration, and the cost tracks the attribute's alphabetical position exactly (49.8 ms for `accesskey`, 284 ms for `onwheel`). | one attribute on a document: 45–280 ms → ~1 ms | low–medium: both tables are generated; the `Attr` analogue of `ofName?_markupName` costs 4.9 s once at build |
| R3 | Rewrite `Ctx.excluded` without lists. It builds two 15-element `List Bool`s, zips them and folds; that is **0.73 ms of kernel time per distinct admission obligation**, which is the entire per-obligation cost. A short-circuiting boolean is **0.13 ms** (5.4×) and a `Nat` bitmask **0.023 ms** (32×). | every node of every document | low for the boolean form; medium for the bitmask (representation change) |
| R4 | Document, and route around, the 33-child cliff. At 33 children a `[…]` literal switches to core's `let`-based `%[…]` desugaring (`Init/Data/List/Notation.lean:58`), and the combinator surface falls off a cliff: 32 children elaborate in 11.7 ms, 33 in **2.02 s**, 40 in 139 142 thousand heartbeats. `#[…].toList` is worse (4.95 s at 40). Chunked `++` at 25 per chunk is linear (200 children, 103 ms). `html!` is immune. | 33-wide: 2.02 s → 0.02 s | none (documentation and a helper); the cliff itself is core's |
| R5 | Have `html!` emit reduced `Ctx` literals for inner contexts instead of `Ctx.child` chains. The elaborator already holds the reduced value (`Whatwg/Html/Syntax/Elaborator.lean:244`) and already has `ctxExpr` (line 125), so it costs the elaborator nothing. Chained obligations down a spine cost 0.93 ms each; identical literal obligations cost ~0 after the first. | deep documents: 37.2 ms → 1.1 ms of kernel for 40 levels | low |
| R6 | Collapse the three combinator auto-parameters into one obligation. Measured on a 17-node tree: 328 → 256 thousand heartbeats (−22%); on a 32-node tree 712 → 521 (−27%). The kernel cost does not move; this is purely elaborator and tactic overhead. | −22% to −27% of the combinator budget | low |
| R7 | Reconsider `whatwg.html.memo`. It never dedupes across declarations (six identical documents cost 531 ms against 70.6 ms for one, with it on), it costs 2.8× the kernel time on a deep document (117 ms vs 41.7 ms at depth 40), and it buys budget only on deep documents (78 vs 118 thousand heartbeats there). On wide documents it is a small loss on both axes. | mixed; see §7 | low |
| R8 | Leave the compiler alone; state the budget. LCNF is 0.76 heartbeats and 0.01 ms per emitted constructor, linear, with no shape that avoids it. It is 39% of the heartbeat budget of a computable 400-item document and 15% of its wall time. | none available | — |

Two facts frame all of it. First, **the kernel, not the elaborator, is the
larger wall-clock cost of every shape measured except the wide combinator
list**; the heartbeat budget users hit is a different quantity and ranks the
costs differently. Second, **`html!` is between eleven and twenty-eight times cheaper per node
than the combinator surface** — 0.29 thousand heartbeats per node on a wide
document and 1.9 on a deep one, against 8.0 and 20.8 — and the gap is
elaborator overhead, not proof strength.

---

## 1. Three instruments, and what each of them cannot see

`maxHeartbeats` counts small allocations in the *current task*. Since Lean
4.33 elaborates declaration bodies in asynchronous tasks (`Elab.async`,
default `true`), the kernel's re-checking and the compiler's work happen in a
task the command elaborator has already returned from. Measured:

| Instrument | What it sees |
| --- | --- |
| `probe.sh` / `bisect.sh` — bisect `maxHeartbeats` until the file compiles | the number a user hits at the default budget of 200. This is the user-facing figure and the one `WhatwgTest/Html/MarkupBenchmark.lean:12` pins |
| `count!` — a `#count_heartbeats`-style command wrapper reading `IO.getNumHeartbeats` around `elabCommand` | the *synchronous* prefix only. With `Elab.async true` it misses the kernel and the compiler entirely; with `Elab.async false` it sees the total |
| `set_option profiler true` | wall time, split into `elaboration`, `tactic execution`, `type checking` (the kernel) and `compilation (LCNF …)` |

The calibration that proves it: the 501-node computable document
(`mk_memo`) measures **148** thousand heartbeats under `count!` with async on
and **1225** with async off, while bisection puts it at **681**. The same
document noncomputable measures 148 either way and bisects at 143. So the
compiler's ~540 thousand heartbeats live in a task of their own.

Heartbeats and wall time are not proportional, and the discrepancy is not
noise: heartbeats are allocations, and the three phases allocate at very
different rates. From the `Elab.async false` totals and the profiles of the
same files: the compiler is about **80 thousand heartbeats per millisecond**
(908 for 11.4 ms of LCNF on the 400-item list), elaboration about **30**, and
the kernel about **17** (the 400-item list's 1394 total, less elaboration, over
43.1 ms). So a `<dl>` of 50 groups spends 2.14 s in the kernel and bisects at
3387, while a computable 400-item `html!` list spends 76 ms in total and
bisects — as `mk_memo` does at a comparable size — at several hundred.
**A recommendation that only cites heartbeats will mis-rank the kernel work,
and one that only cites milliseconds will mis-rank the compiler.** Both are
given below.

---

## 2. Baselines at `e278982`

Bisected (largest failing, smallest passing, in the option's thousands), and
profiled (milliseconds, `Elab.async` left at its default):

| Shape | Nodes | Heartbeats | elab | tactic | kernel | LCNF |
| --- | --- | --- | --- | --- | --- | --- |
| 15 nested `div` through combinators (`deep`) | 17 | 350 / 353 | — | — | — | — |
| 30 nested `div` through combinators (`cd30`) | 32 | — | 14.6 ms | 8.0 ms | **31.2 ms** | 3.7 ms |
| `ul` with 30 `li` through combinators (`wide`) | 61 | 487 / 490 | — | — | — | — |
| `ul` with 30 `li`, chunked, 200 items (`cwch200`) | 401 | 3465 / 3468 | 103 ms | 46.2 ms | 3.3 ms | 2.1 ms |
| 501-node `html!` document, noncomputable | 501 | 140 / 143 | — | — | — | — |
| 501-node `html!` document, computable | 501 | 678 / 681 | — | — | — | — |
| the same with two attributes on every `li` | 501 | 246 / 250 | — | — | — | — |
| `html!` `ul` with 400 `li`, noncomputable | 801 | — | 21.5 ms | — | 43.1 ms | — |
| `html!` `ul` with 400 `li`, computable | 801 | — | 21.9 ms | — | 43.2 ms | 12 ms |
| `html!` `<table>` with 50 rows | 151 | 750 / 753 | 16.8 ms | — | 431 ms | — |
| `html!` `<dl>` with 50 groups | 201 | 3384 / 3387 | 132 ms | — | 2.14 s | — |
| `html!` 40 nested `div`, memo on | 42 | 75 / 78 | 7.0 ms | — | 117 ms | — |
| `html!` 40 nested `div`, memo off | 42 | 115 / 118 | 5.0 ms | — | 41.7 ms | — |

Per node, the combinator surface is 8.0 thousand heartbeats wide (490 over 61
nodes; 3468 over the 401 of `cwch200` is 8.65) and 20.8 deep (353 over 17),
which is why the default budget holds about a dozen nested nodes, as
`Whatwg/Html/Node/Typed.lean` records. `html!` is 0.29 per node wide and
noncomputable, 1.36 wide and computable, and 1.9 deep.

### 2.1 The 33-child cliff

This is the sharpest thing in the report and it is not in any ledger row.

Core's list-literal macro switches strategy at 64 `elemsAndSeps`, i.e. at 33
elements (`Init/Data/List/Notation.lean:49–61`): above it, `[a, b, c]` becomes
`%[a, b, c | List.nil]`, which builds the list through nested `let` bindings.
The combinator surface does not survive the switch. Elaboration heartbeats,
`count!` with async on:

| Children of one `ul` | 31 | 32 | **33** | 34 | 40 |
| --- | --- | --- | --- | --- | --- |
| `E.el (E.li [E.txt "item"])` | 441 | 455 | **53 839** | 66 044 | 139 142 |
| `E.el (E.li [])` | — | 313 | **1 533** | — | — |
| `E.txt "x"` under a `p` | — | 145 | **187** | — | — |

Profiled, the cost is entirely in the elaborator, not in the tactic or the
kernel: 33 `li` give `elaboration 2.02 s`, `tactic execution 16.3 ms`,
`type checking 4.6 ms`, with 608 ms of it inside `process pre-definitions`;
32 `li` give 11.7 ms of elaboration. The severity scales with how large each
child term is, which is consistent with the `let` bindings defeating the
expected-type propagation the typed tree depends on
(`Whatwg/Html/Node/Typed.lean:16–20`) and forcing repeated work over big
terms. The mechanism beyond that is INFERRED; the numbers are not.

`#[…].toList` is not an escape (40 children: 4.95 s of elaboration).
Chunking is: `E.ul ([…25…] ++ […25…] ++ …)` is linear and cheap (200
children: 103 ms of elaboration, 3.3 ms of kernel, 3468 thousand
heartbeats). `html!` is immune, because it builds the list `Expr` itself with
`mkListLit` (`Whatwg/Html/Syntax/Elaborator.lean:278–284`).

A `ul` of 33 list items is an ordinary document. This should be a note in
`Whatwg/Html/Node/Combinators.lean`'s module docstring and a row in
`WhatwgTest/Html/DecideBenchmark.lean`, with the chunking form spelled out.

---

## 3. Question 1: the per-obligation kernel cost

The obligations are `Ctx.admitsWith (Ctx.child (Ctx.child ctx t₁) t₂) t₃ attrs
= true` proved by `Eq.refl true`. I measured the kernel directly, by putting
*n* such equations in one declaration as a right-nested conjunction proved by
`⟨rfl, …, rfl⟩` and reading `type checking` from the profiler under
`Elab.async false`. Baseline for the declaration shell is about 1.0 ms.

| Probe | Obligations | Kernel |
| --- | --- | --- |
| one `admits` at chain depth 1 / 10 / 40 / 80 | 1 | 1.41 / 1.95 / 3.85 / 6.52 ms |
| *n* copies of the **same** depth-20 chain (`ksib`) | 10 / 20 / 40 | 2.62 / 2.54 / 2.64 ms |
| *n* copies of the **same** reduced literal (`klit`) | 10 / 20 / 40 | 1.11 / 1.16 / 1.10 ms |
| a spine: one obligation at each depth 1…d (`ksp`) | 10 / 20 / 30 / 40 | 8.71 / 17.4 / 26.5 / 37.2 ms |
| 20 / 40 **distinct** reduced literals (`klitd`) | 20 / 40 | 16.5 / 32.0 ms |

Three readings, all measured.

**The whnf cache does share chain prefixes, completely, within one
declaration.** Forty sibling obligations at depth 20 cost the same as one
(2.6 ms); extending a single chain from depth 40 to depth 80 costs
0.067 ms per level. So a wide document pays for its chain once, which is why
`cwch200`'s kernel time is 3.3 ms for 401 nodes.

**The chain is not the cost; `Ctx.admits` is.** A spine of 40 distinct chained
obligations costs 37.2 ms, i.e. 0.93 ms each — but 40 distinct *fully reduced
literal* obligations cost 32.0 ms, i.e. 0.80 ms each. Replacing chains with
literals removes 14% of the per-obligation cost, not 90%. What it does remove
is *duplication*: in a real document the reduced contexts at different depths
usually coincide (every level of a `div` spine reduces to
`⟨.flow, {}, []⟩`), so literals turn 40 distinct obligations into one, and
40 identical literals cost 1.1 ms in total rather than 32.0 ms. **That is a
33× saving on deep documents, and it comes from deduplication by value, not
from cheaper reduction.**

Prototyped end to end: a 30-deep tree written with an explicit reduced-literal
type ascription at every level (`lit30`) has kernel time 7.84 ms against
31.2 ms for the same tree through the plain combinators (`cd30`), a 4×
reduction. Its *heartbeat* figure is worse (1084 against about 710), because
the prototype pays the elaborator for 30 ascriptions and 30
`Ctx.child L .div =?= L` unifications. That elaborator cost is an artifact of
the prototype, not of the idea: inside `html!` the reduced `Ctx` value is
already in hand at `Whatwg/Html/Syntax/Elaborator.lean:244` and `ctxExpr`
(line 125) already turns one into a literal, so emitting `ctxExpr inner`
instead of `mkApp2 (mkConst ``Ctx.child) ctxE tE` (line 245) is free. For the
generated combinators the same change is *not* available: their signature is
`List (Child (ctx.child .tag))` written once and polymorphically
(`Whatwg/Html/Node/Combinators.lean:45`), and there is no elaborator there to
compute the reduction. **Recommend it for `html!` only.**

**The interaction with `mkAuxLemma` is the opposite of what the H5 ledger row
assumed, and it is the reason deep `html!` documents are expensive.** With
`whatwg.html.memo` on (the default), each distinct obligation type becomes its
own auxiliary lemma (`Elaborator.lean:139–141`), hence its own declaration,
hence its own kernel invocation with a *cold* whnf cache; the sharing measured
above is destroyed. A 40-deep `html!` document costs 117 ms of kernel time
with memoization and 41.7 ms without. With reduced literals the obligations at
every depth become one type, one aux lemma, one kernel check — memoization and
literals compose, and only together.

---

## 4. Question 2: attribute names in the kernel

This is the largest single cost in the library, and it is invisible in the
heartbeat figures the ledger records.

`attrOk` (`Whatwg/Html/Content/Valid.lean:94`) resolves the attribute name
through `Attr.ofName?`, a 234-arm match on `String` literals
(`Whatwg/Html/Schema/Attributes.lean:4014`), and then `valueOk` (line 64 of
`Valid.lean`) calls `rowsFor` (line 59), which `filter`s the 271-row
`attributeRows` literal. Both are linear scans, and the kernel walks them.

| Probe | Kernel |
| --- | --- |
| `Attr.ofName? "abbr"` (arm 1) | 2.3 ms |
| `Attr.ofName? "id"` (arm 63) | 49.1 ms |
| `Attr.ofName? "onwheel"` (arm 234) | 231 ms |
| `Attr.ofName? "zzzz"` (no arm) | 199 ms |
| `Tag.ofName? "html"` (arm 1) / `"canvas"` (arm 113) | 2.0 / 52.5 ms |
| `rowsFor .id .li` | 32.2 ms |
| `valueOk .id .li "id" "b"` | 26.4 ms |
| `AttrSet.contains` on `li`'s set | 0.67 ms |
| `attrsOk .li` with 0 / 1 / 2 / 4 / 8 attributes | 0.4 / 55 / 109 / 233 / 386 ms |

The per-arm cost is one `String` equality. Measured separately: 100
comparisons against a fixed left operand cost 38 ms (0.38 ms each), 100
against varying operands 89.5 ms (0.9 ms each), and 100 `Nat` equalities
1.77 ms (0.018 ms each). **A `String` comparison in the kernel is 20 to 50
times a `Nat` comparison**, and `Attr.ofName?` does up to 234 of them.

End to end, in `html!`, a 25-item list where every `li` carries one attribute
(the cost is paid once per declaration, because the obligation expression is
shared across the items):

| attribute | position | kernel |
| --- | --- | --- |
| none | — | 5.3 ms |
| `accesskey` | ~4 | 49.8 ms |
| `class` | ~30 | 60.9 ms |
| `id` | 63 | 90.8 ms |
| `translate` | ~200 | 157 ms |
| `onwheel` | 234 | 284 ms |

Four routes, measured or costed:

1. **Dispatch on `String.length` first.** `match s.length with | 7 => match s with …`. Measured: `onwheel` falls from 231 ms to 29 ms (8×). Cheap to generate; the residual is the within-bucket `String` comparisons.
2. **Match on `List Char`.** A generated `ofChars? : List Char → Option Attr` whose 234 patterns are character lists; Lean's match compiler splits column-wise, which is a trie. Measured: 11 ms per lookup regardless of position (`abbr` 11.3, `onwheel` 12.5, a miss 10.2), of which **5 ms is `String.toList` of the literal alone**. That is a 20× improvement on late names and a 5× regression on the first few. The declaration itself costs 68.7 ms of kernel per module that defines it. This is the same reasoning `Valid.lean:38–41` already gives for spelling its string tests over `String.toList`.
3. **Do not look the name up at all.** `Tag` already has this: `ofName?_markupName` (`Whatwg/Html/Content/Lattice.lean:124`) is proved once over `Tag.all` by `decide +kernel`, and `validIn_element` (`Valid.lean:158`) uses it so the typed surface never re-runs `Tag.ofName?`. There is no `Attr` analogue, so every document re-runs `Attr.ofName?`. Building one costs **4.87 s of kernel time once at build**, and as stated over all of `Attr.all` it is **false** — the probe failed with a kernel application type mismatch, which is what a `data-`/`aria-` prefix constructor whose `markupName` is a prefix rather than a name would do. Restrict it to the index attributes and it should hold (INFERRED). Note for scale: the existing `Tag` bridge already costs **878 ms of kernel time on every build**.
4. **Generate `rowsFor` as a flat table.** `rowsFor` is a `filter` over 271 structure literals to find at most one row; H4.1 already did exactly this transformation for `Tag.content?` ("a flat match, proved equal to the `elements` lookup by `content?_eq_element?`"). Only `kind`, `keywords` and `allowEmpty` are read (`Valid.lean:64–72`), so the emitted table can be much smaller than `AttrRow`. Expected: 32 ms → constant. Unmeasured.

Routes 3 and 4 together take an attribute from 75–280 ms to roughly the cost
of `AttrSet.contains`, 0.7 ms. Routes 1 and 2 are strictly weaker but need no
new theorem.

### 4.1 H7.3's conditions add a second string cost

`Condition.lower` (`Whatwg/Html/Schema/Condition.lean:28`) is
`s.toList.map Char.toLower`, and `lookup` (line 31) applies it to both the
stored name and the sought name for every attribute. Measured:
`Condition.lower "href"` costs 3.2 ms of kernel, one
`Condition.holds (.hasAny ["href"]) [("href", "#")]` costs 5.3 ms, and a
25-element list of `<a href="#">` costs 70 ms of kernel against 6.6 ms for
`<a>` with no attribute (`<input type="text" />`: 136 ms). Comparing `Attr`
constructors instead of names inside `Condition` would remove the `toList`
entirely; the conditions are generated, and the names they mention are index
names.

---

## 5. Question 3: the derivative matcher

`Seq.deriv` (`Whatwg/Html/Content/Sequence.lean:38`) is textbook Brzozowski
with no simplification: `deriv (.seq a b) t` always builds an `.alt` of a
`.seq`, even when both sides are `.empty`. The terms therefore grow, and
`accepts` (line 50) folds `n` of them.

Measured term size of `ts.foldl (deriv base) s`, by `#eval`:

| children | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | --- | --- | --- | --- | --- | --- |
| `table`, *n* `tr` | 59 | 76 | 116 | 220 | 524 | 1516 |
| `dl`, *n*/2 `dt`/`dd` pairs | — | 35 | 91 | 275 | 931 | 3395 |
| `select`, *n* `option` | 27 | 46 | 90 | 202 | 522 | 1546 |

and the kernel cost of an `html!` document, which is the sum of those sizes:

| rows / groups | 10 | 25 | 50 | 100 |
| --- | --- | --- | --- | --- |
| `<table>` with *n* `<tr>` | 63.5 ms | 139 ms | 431 ms | **1.64 s** |
| `<dl>` with *n* `dt`/`dd` pairs | 95.1 ms | 506 ms | 2.14 s | **9.28 s** |
| `<p>` with *n* `<span>` (no sequence) | — | 5.6 ms | — | 8.1 ms at 100 |

`<dl>` multiplies its kernel cost by 4.2–4.3× for each doubling of *n*; the whole file
takes 11.9 s of wall time at 100 groups against a 1.1 s floor. The elaborator
suffers the same shape, because `html!` runs the compiled `seqProblem?` on the
children (`Elaborator.lean:296`): 1 s of elaboration at 100 groups. The
derivative size itself multiplies by 3.4–3.6× per doubling of *n*, and the
fold's cost is the sum of the sizes, which is where the near-cubic total
comes from.

**Smart constructors fix it completely.** I implemented `sq`/`al` that drop
`.empty` and `.eps` and collapse `alt a a`, and re-derived:

| *n* | 1 | 2 | 4 | 8 | 16 | 32 | 64 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `table`, *n* `tr`: derivative size | 5 | 5 | 5 | 5 | 5 | 5 | 5 |
| `dl`, *n* `dt`/`dd` pairs: derivative size | 9 | 9 | 9 | 9 | 9 | 9 | 9 |

and the smart matcher agrees with the shipped one on `table` for 0–39
`tr` and on `dl` for 0–19 `dt`/`dd` pairs (`#eval … .all …` returned `true`
for both). That is a finite probe, not a theorem.

Cost side. `seqOk` is inside `validIn` (`Valid.lean:128`), which ruling HP-13
makes *the definition* of the content model, so changing `deriv` changes the
definition and needs an agreement theorem — either `∀ base s ts, accepts' =
accepts` (not finitely decidable as stated, because `Seq` and `List Tag` are
infinite), or the honest route: give `Seq` a denotation
`Seq.Matches : Seq → List Tag → Prop`, prove `accepts` correct against it once,
and then any implementation is checked against the denotation rather than
against the old implementation. That is the only place in this report where I
am recommending real proof work; it is also the only place where the current
design has a scaling wall rather than a constant factor.

A generated DFA is the alternative (13 sequences, all tiny). It would make
matching a `Nat`-indexed table walk, and the agreement check per sequence is
finite, hence `decide +kernel`-able. Whether the state set is small enough to
enumerate is INFERRED; the derivative sizes above (constant under
simplification) say it is.

---

## 6. Question 4: where the combinator surface's 8-to-21 per node goes

Three obligations per node are discharged by the `admits` tactic
(`Whatwg/Html/Node/Admit.lean:158`): `attrsOk`, `seqOk` and, at `E.el`,
`admitsWith`. I built three copies of `E.div` differing only in how many of
them are auto-parameters, and measured both instruments.

| Variant | Obligations per node | Heartbeats, 17 nodes | Heartbeats, 32 nodes | elab (32) | tactic (32) | kernel (32) |
| --- | --- | --- | --- | --- | --- | --- |
| `mdivA`, as generated today | 3 | 328 | 712 | 18.1 ms | 9.14 ms | 31.2 ms |
| `mdivB`, `seqOk` given as `rfl` | 2 | 284 | — | 11.8 ms | 7.66 ms | 28.8 ms |
| `mdivC`, `attrsOk` and `seqOk` given | 1 | 256 | 521 | 10.6 ms | 6.37 ms | 29.2 ms |

Readings:

- **The tactic is about half the elaboration** and costs roughly 0.1 ms per invocation; three invocations per node is the dominant elaborator cost. Combining the three propositions into one `Element.ok` conjunction, discharged once, is worth **22–27% of the heartbeat budget**, measured. It changes 111 generated signatures and `Element.ofChildren` (`Typed.lean:91`), and it costs the diagnostics nothing as long as the tactic still decomposes the conjunction before blaming (the `admits` tactic already blames attributes one at a time, `Admit.lean:196–201`).
- **The kernel does not move**, because the same obligations are checked either way. At 32 nodes the kernel is 31.2 ms against 18.1 ms of elaboration: the deep combinator tree is kernel-bound, and §3 and §7 are where its cost is.
- Residual elaboration after the tactics is 0.13 ms per node (`mdivC`: 10.6 − 6.37 over 32 nodes). That is `elabApp` plus the unification of `Element .div (ctx.child .div)`. It is not where the money is.
- The wide case is the opposite: `cwch200`'s kernel is 3.3 ms for 401 nodes (all obligations identical, cache shared) against 103 ms of elaboration, 46 ms of it tactic. **Wide documents are elaborator-bound, deep documents are kernel-bound.**

`@[reducible]`/`abbrev` choices: `Ctx.child` is a plain `def`
(`Whatwg/Html/Content/Context.lean:87`). Making it `abbrev` would have the
elaborator's unifier unfold it speculatively at reducible transparency in
every `Child (ctx.child .tag)` position; the earlier research report's §6.2
argues against exactly that for the set functions, and nothing measured here
suggests unification is a cost centre (0.13 ms per node). Leave it.

---

## 7. Questions 5 and 7: the compiler, and memoization

**LCNF.** Measured on `html!` `ul`s: 25 items 1.3 ms, 100 items 2.9 ms, 400
items 11.4 ms of `compilation (LCNF base + mono + impure)` — linear, about
0.01 ms per emitted constructor. In heartbeats, `hwn400` (noncomputable) is
1394 and `hwc400` (computable) 2302 under `Elab.async false`, so compilation
is 908 thousand heartbeats for 1200 constructors: **0.76 of the option's units
per constructor**, which is 39% of that document's budget and 15% of its wall
time. That asymmetry is the whole story: the compiler is cheap in time and
expensive in budget.

I found no emitted shape that reduces it and stays honest. Binding the
literal once does not apply (the children differ); `List.replicate` is 6×
cheaper (`rawrep100` 0.5 ms against `rawc100` 2.9 ms) but only because the
children are identical, which a real document's are not; `@[inline]`
attributes act on functions, and the term here is data. The realistic advice
is the one `MarkupBenchmark.lean:35` already gives — a large document needs
`set_option maxHeartbeats` — plus: **a document used only for its proofs
should be `noncomputable`**, which is a 4.8× budget saving measured (143
against 681 on the 501-node document) and costs nothing.

**Memoization.** `whatwg.html.memo` (`Elaborator.lean:70`) mints one
`mkAuxLemma` per distinct obligation type per module. Measured:

| Shape | memo on | memo off |
| --- | --- | --- |
| 40 nested `div`, kernel | 117 ms | 41.7 ms |
| 40 nested `div`, heartbeats | 78 | 118 |
| 40 nested `div`, total heartbeats (async off) | 1889 | 661 |
| 200 `li`, kernel | 15.3 ms | 13.9 ms |
| 200 `li`, total heartbeats (async off) | 469 | 433 |
| six identical 25-`li` documents with `class="x"`, kernel | 531 ms (509 async, 357 sync) | 524 ms (490 async, 353 sync) |
| one such document | 70.6 ms | 61.9 ms |

Three findings. It **never dedupes across declarations**: six identical
documents cost 531 ms of kernel time against 70.6 ms for one, with
memoization on, with `Elab.async` both on and off. It **costs 2.8× the kernel time on a deep document**, for the cold-cache
reason of §3. It **does buy budget on a deep document** (78 against 118),
because the work moves into aux-lemma declarations whose kernel checks are
budgeted separately. On the wide shape it is a small loss on both axes, which
is consistent with `MarkupBenchmark.lean:13–14` recording no difference at
501 nodes.

So the option as it stands trades wall time for budget on deep documents and
loses on everything else. If R5 lands (reduced literals), obligations at
different depths coincide, memoization becomes a real deduplicator, and the
trade disappears. Until then, the honest default is off, and the row in
`MarkupBenchmark.lean` should gain the deep case, which is where the two modes
differ.

---

## 8. Question 6: structural alternatives

**`Ctx.excluded` is the per-obligation cost, and it is the cheapest thing to
fix.** `excluded` (`Whatwg/Html/Content/Context.lean:48`) builds
`x.flags` (a 15-element `List Bool`, `Exclusions.flags` at
`Whatwg/Html/Schema/Exclusions.lean:50`) and `hits t` (another 15, computing
four category functions and eleven tag comparisons,
`Context.lean:42`), zips them into fifteen pairs and folds. Measured, 40
distinct exclusion records against one tag, in one declaration:

| Definition | Kernel, 40 obligations | Per obligation |
| --- | --- | --- |
| `Ctx.excluded` as shipped | 29.4 ms | 0.73 ms |
| a short-circuiting `||` of fifteen `&&`, no lists | 5.43 ms | 0.13 ms |
| `Ctx.admits` as shipped, reduced literal contexts | 32.0 ms | 0.80 ms |
| the same with the short-circuit form | 6.28 ms | 0.16 ms |
| `Nat` bitmask: `b.contains t && (m &&& hitsMask t == 0)` | 1.88 ms (0.95 above the table's own cost) | **0.023 ms** |
| one `Ctx.hits .p` evaluated to a list | 0.876 ms | — |

The boolean rewrite is a 5× cut on every node of every document and needs one
bridge theorem, `∀ x t, Ctx.excluded x t = excluded' x t`, which is
`by cases x <;> cases t <;> rfl` if `excluded'` is written right-nested to
match `List.any`'s shape — 114 goals, the same class of one-time cost as
`Tag.mem_all`. `Ctx.excluded`'s consumers are `admits`, `admitsWith` and the
lemmas `excluded_mono`/`any_hit_mono`/`admits_antitone`
(`Context.lean:106–120`), which reason through `flags` and would keep working
against the bridged form.

The bitmask is a further 6× (32× against today) and is the one place in this
library where a `Nat` mask beats constructor dispatch, for exactly the reason
the earlier report gave in its §2.2: `Nat.land` is GMP-accelerated and a
15-element list walk is not. It costs a representation change —
`Exclusions` becomes a `Nat` (or keeps its fields and gains a generated
`mask`), `union` becomes `|||`, `le` becomes `land`, `names` needs the field
view back, and `hitsMask : Tag → Nat` becomes a generated 114-row table. The
prose function `Ctx.describe`/`Exclusions.names` (`Context.lean:93`,
`Exclusions.lean:62`) keeps the messages readable either way, which is the
condition the brief attaches.

**`Base.contains` is not a cost centre.** Measured at 0.176 ms for one lookup
including the declaration baseline, and inside the bitmask probe the whole
`admits` came to 0.023 ms with `Base.contains` still in it. It is a two-level
constructor dispatch (`Whatwg/Html/Schema/Families.lean:325`), already O(1) in
the kernel. **Do not replace it**; a `ctorIdx`-based or bitmask dispatch would
buy nothing measurable and would cost the readable per-base functions.

**Indexing by a pre-reduced `Ctx` value** is sound in the sense that matters —
`Ctx.child c t` and its reduct are definitionally equal, so `Element t ctx`
and `Element t ctx'` are the same type and no theorem changes — and it is
cheaper, by §3, but only inside an elaborator that can compute the reduction.
See R5.

---

## 9. Ranked recommendations

Each row: the saving, the evidence, what it costs in DX and in proof, and the
risk.

**R1. Smart constructors (or a DFA) for `Seq.deriv`.**
*Saving*: a `<dl>` of 100 groups from 9.28 s to linear; a `<table>` of 100
rows from 1.64 s; the heartbeat figures 3387 (50 groups) and 753 (50 rows)
fall with them (the linear figure is INFERRED — I measured term sizes and
agreement, not the rewritten checker's heartbeats).
*Evidence*: measured derivative sizes (1516 at 32 `tr`, 3395 at 32 alternating
`dt`/`dd` children, against a constant 5 and 9 with smart constructors),
measured kernel times, and a finite agreement probe over 0–39 `tr` and
0–19 `dt`/`dd` pairs.
*DX*: none; the error message (`seqProblem?`, `Sequence.lean:77`) is unchanged.
*Proof*: this is the one that costs. `seqOk` is part of `validIn`, the
definition (HP-13), so the change needs either an agreement theorem or —
better, and the shape I would freeze — a denotation `Seq.Matches` with
`accepts` proved correct against it, after which the implementation is free.
*Risk*: medium. It is the only super-linear cost inside the checker itself;
the other unbounded one, §2.1, is core's.

**R2. Kill the two linear scans behind an attribute.**
*Saving*: 45–280 ms of kernel per distinct attribute per declaration, down to
about 1 ms.
*Evidence*: measured, and measured to track the arm's position exactly
(§4). `Attr.ofName?` 49.1 ms at arm 63 and 231 ms at arm 234; `rowsFor`
32.2 ms; `AttrSet.contains` 0.67 ms.
*DX*: none.
*Proof*: the strong form needs an `Attr` analogue of `ofName?_markupName`
(`Lattice.lean:124`), which costs 4.87 s of kernel once per build and must
exclude the two prefix constructors (the unrestricted statement is false —
the probe failed in the kernel). The weak forms (length dispatch, 8×; a
`List Char` trie, 20× on late names) need no theorem at all, only a change to
the emitter, and the drift gate already covers the generated tables.
*Risk*: low for the weak forms; medium for the bridge, whose 4.9 s lands on
every build.

**R3. Rewrite `Ctx.excluded` without lists.**
*Saving*: 0.73 ms → 0.13 ms per distinct admission obligation, on every node
of every document; 0.023 ms with a `Nat` mask.
*Evidence*: measured over 40 distinct exclusion records (§8).
*DX*: none.
*Proof*: one bridge theorem by 114 `rfl`s for the boolean form; for the mask,
`Exclusions`'s representation changes and `flags`, `le`, `union`, `names`,
`any_hit_mono`, `all_le_zipWith_or`, `Exclusions.le_union_left`,
`excluded_mono` and `admits_antitone` are all restated
(`Context.lean:74–120`, `Exclusions.lean:41–70`).
*Risk*: low, then medium. Do the boolean form first; reach for the mask only
if R1 and R2 have landed and this is still the top line.

**R4. Document and route around the 33-child cliff.**
*Saving*: 2.02 s → 0.02 s of elaboration at 33 children; the cliff is
unbounded above (139 142 thousand heartbeats at 40).
*Evidence*: measured, with the core mechanism identified at
`Init/Data/List/Notation.lean:58`.
*DX*: this is a DX fix, not a cost fix. A user writing a 40-item menu through
the combinators today gets a multi-second hang and no explanation.
*Proof*: none.
*Risk*: none. Write the chunking form into
`Whatwg/Html/Node/Combinators.lean`'s docstring, add a `DecideBenchmark` row
at 32 and 33, and say plainly that wide content belongs in `html!`.

**R5. `html!` emits reduced `Ctx` literals for inner contexts.**
*Saving*: 37.2 ms → 1.1 ms of kernel on a 40-level spine; makes memoization
work.
*Evidence*: measured on the micro-benchmarks (§3) and on a hand-ascribed
30-deep combinator tree (kernel 31.2 → 7.84 ms). The elaborator-side cost is
argued from the code, not measured: `inner` is already a `Ctx` value at
`Elaborator.lean:232` and `ctxExpr` already exists.
*DX*: `#print` and type errors show a `Ctx.mk` literal instead of a
`Ctx.child` chain. The `admits` tactic reads both (`Admit.lean:77–94`), so
diagnostics are unaffected.
*Proof*: none — the two are definitionally equal.
*Risk*: low. Do it with R7.

**R6. One obligation per combinator instead of three.**
*Saving*: 22% at 17 nodes, 27% at 32 nodes, measured in heartbeats; nothing
in the kernel.
*Evidence*: §6, three hand-written variants of `E.div`.
*DX*: unchanged if the tactic decomposes the conjunction before blaming.
*Proof*: `Element` keeps its three fields; only the combinator signature and
`Element.ofChildren` change.
*Risk*: low, but it touches all 111 generated combinators and the
`CombinatorShape` drift gate.

**R7. Change the `whatwg.html.memo` default, or fix it.**
*Saving*: 2.8× kernel on deep documents if turned off today; nothing lost on
wide ones. If R5 lands first, turning it *on* becomes a real win.
*Evidence*: §7, six shapes measured on both axes.
*DX*: none.
*Proof*: none.
*Risk*: low. The benchmark row in `MarkupBenchmark.lean` should gain a deep
case, since the wide case cannot distinguish the two modes.

**R8. State the compiler's tax; do not try to remove it.**
*Saving*: none available. 0.76 of the option's units per emitted constructor, linear.
*Evidence*: §7.
*DX*: recommend `noncomputable` for proof-only documents (4.8× budget,
measured) and `set_option maxHeartbeats` otherwise.
*Risk*: none.

---

## Appendix A: exact commands

All from `/Users/pooks/Dev/lean4-whatwg`, toolchain v4.33.1, at commit
`e278982`. `$S` is the scratchpad
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-whatwg/5f31dd7e-b7b8-42ae-8ffa-6cdb9d83e245/scratchpad`.
Harness scripts written for this review, beside the pre-existing `probe.sh`
and `bisect.sh`:

- `$S/Count.lean` — a `count! <command>` elaborator reading `IO.getNumHeartbeats` around `elabCommand`.
- `$S/count.sh <body>` — `count!` with `Elab.async` at its default (elaboration only).
- `$S/count2.sh <body>` — `count!` with `set_option Elab.async false` (total).
- `$S/prof.sh <body>` — `set_option profiler true`, prints elaboration / tactic / type checking / LCNF.
- `$S/profs.sh <body>`, `$S/profk.sh <body>` — the same with `Elab.async false`.
- `$S/bisect2.sh <body>` — the pre-existing `probe.sh` driven by an auto-bracketing bisection, to within 5 units.
- `$S/probe2.sh <body> <n>`, `$S/bisect3.sh <body>` — bisection with `maxHeartbeats` at file scope, for bodies of more than one command.
- `$S/gen.py`, `$S/genk.py` — body generators.
- `$S/wall.sh <body>` — end-to-end `lake env lean` wall time.

Every probe file is `import Whatwg.Html.Syntax.Elaborator`,
`import Whatwg.Html.Node.Combinators`, the four `open`s, the options, then the
body; each is deleted after the run.

```
bash $S/bisect2.sh deep          -> deep: fails 350, passes 353
bash $S/bisect2.sh wide          -> wide: fails 487, passes 490
bash $S/bisect2.sh nc_memo       -> nc_memo: fails 140, passes 143
bash $S/bisect2.sh mk_memo       -> mk_memo: fails 678, passes 681
bash $S/bisect2.sh nc_attrs      -> nc_attrs: fails 246, passes 250
bash $S/bisect2.sh tb50          -> tb50: fails 750, passes 753
bash $S/bisect2.sh dl50          -> dl50: fails 3384, passes 3387
bash $S/bisect2.sh hd40          -> hd40: fails 75, passes 78
bash $S/bisect2.sh hdnm40        -> hdnm40: fails 115, passes 118
bash $S/bisect2.sh cwch200       -> cwch200: fails 3465, passes 3468
bash $S/bisect2.sh cond_a        -> cond_a: fails 140, passes 143
for b in mA15 mB15 mC15 mA30 mC30 lit15 lit30; do bash $S/bisect3.sh $b; done
      -> 328, 284, 256, 712, 521, 521, 1084 (smallest passing)
```

Instrument calibration (§1):

```
count! mk_memo, Elab.async true   -> HB 148
count! mk_memo, Elab.async false  -> HB 1225
bisect mk_memo                    -> 681
```

Elaboration heartbeats by depth and width, `count.sh` (async default):

```
cd1 24  cd5 68  cd10 133  cd15 208  cd20 292  cd25 387  cd30 491
cw10 148  cw20 288  cw30 427  cw31 441  cw32 455  cw33 53839  cw34 66044  cw40 139142
pt32 145  pt33 187        (33 text children under a p)
ce32 313  ce33 1533       (33 empty li under a ul)
hd1 10  hd5 14  hd10 20  hd15 27  hd20 35  hd25 44  hd30 54  hd40 77   (html!, noncomputable)
```

Profiles, `prof.sh` (milliseconds):

```
cd5    elab 2.74  tac 3.07  kernel 8.09   lcnf 2.3
cd10   elab 5.15  tac 4.77  kernel 14.0   lcnf 2.0
cd20   elab 9.88  tac 7.03  kernel 24.6   lcnf 3.3
cd30   elab 17.4  tac 10.0  kernel 36.3   lcnf 4.4     (a second run: elab 14.6, tac 8.0, kernel 31.2)
ce32   elab 7.86  tac 6.37  kernel 2.06
ce33   elab 47.9  tac 7.01  kernel 2.11
cw32   elab 11.7  tac 9.02  kernel 17.0
cw33   elab 2020  tac 16.3  kernel 4.6    (process pre-definitions 608 ms)
cwarr40 elab 4950 tac 13.1  kernel 3.56   (#[...].toList)
cwch40  elab 16.7 tac 10.5  kernel 3.44
cwch60  elab 23.8 tac 14.2  kernel 3.16
cwch100 elab 45.0 tac 24.6  kernel 4.13
cwch200 elab 103  tac 46.2  kernel 3.27
mA15 elab 9.16 tac 5.63 kernel 15.5 | mB15 6.66/4.88/15.9 | mC15 5.93/3.90/16.2
mA30 elab 18.1 tac 9.14 kernel 31.2 | mB30 11.8/7.66/28.8 | mC30 10.6/6.37/29.2
lit15 elab 14.5 tac 4.39 kernel 5.56 | lit30 elab 27.8 tac 6.90 kernel 7.84
hwn25 elab 5.17 kernel 5.73         | hwc25 5.02/5.20 lcnf 1.32
hwn100 elab 8.86 kernel 8.08        | hwc100 8.36/7.92 lcnf 3.1
hwn400 elab 21.5 kernel 43.1        | hwc400 21.9/43.2 lcnf 11.4
rawc100 elab 21.5 lcnf 2.9 | rawrep100 elab 0.94 lcnf 0.50 | rawc400 elab 83.3 lcnf 11.0
hd20 kernel 45.9 | hdnm20 kernel 21.5 | hd40 kernel 117 | hdnm40 kernel 41.7
hw200 elab 12.4 kernel 15.3 | hwnm200 elab 11.2 kernel 13.9
tb10 63.5 | tb25 139 | tb50 431 | tb100 1640      (kernel)
dl10 95.1 | dl25 506 | dl50 2140 | dl100 9280     (kernel)
fd25 5.55 | fd100 8.09 | fd200 15.2               (kernel; p with n spans)
cond_span 6.32 | cond_aplain 6.55 | cond_a 70.0 | cond_input 136   (kernel)
pa_acc 49.8 | pa_cls 60.9 | pa_id 90.8 | pa_tr 157 | pa_onw 284    (kernel)
mmB1_m 5.29 | mmA1_m 70.6 | mmA1_n 61.9 | mmA6_m 531 | mmA6_n 524 | mmB6_m 34.0 | mmB6_n 26.1
mmA6_m sync 357 | mmA6_n sync 353 | mmB6_m sync 27.3 | mmB6_n sync 22.5
```

Total heartbeats, `count2.sh` (`Elab.async false`):

```
hwn400 1394  hwc400 2302  cd15 585  cd30 1201  tb50 5744  dl50 25973
hd20 740  hdnm20 351  hd40 1889  hdnm40 661  hw200 469  hwnm200 433
```

Kernel micro-benchmarks, `profk.sh` (`Elab.async false`, milliseconds of
`type checking`; declaration baseline about 1.0 ms):

```
k1_1 1.41  k1_10 1.95  k1_40 3.85  k1_80 6.52          one admits at chain depth d
ksib10_1 1.44  ksib10_10 1.94  ksib10_20 2.62  ksib20_20 2.54  ksib40_20 2.64
klit10 1.11  klit20 1.16  klit40 1.10             n copies of one reduced literal
klitd20 16.5  klitd40 32.0                        n distinct reduced literals
ksp10 8.71  ksp20 17.4  ksp30 26.5  ksp40 37.2    a spine of depths 1..d
kbase1 0.176   khits1 0.876
kexcl40 29.4   kexcl2_40 5.43   altexcl40 6.28    excluded, hits2, admits2
mask1 0.947    mask40 1.88                        Nat bitmask
aname_early 2.3  aname_late 231  aname_none 199   Attr.ofName?
tname_early 1.99  tname_late 52.5                 Tag.ofName?
ofn_id 49.1  rf_id 32.2  vok_id 26.4  aset_id 0.67
aok0 0.401  aok1 55  aok2 109  aok4 233  aok8 386  attrsOk with k attributes
aok1x20 142  aok0x20 0.308
ochars_decl 68.7  ochars_early 80  ochars_late 81.2  ochars_none 78.9
olen_decl 3.66  olen_late 32.6
streq 2.04  streq10 4.48  streq100 38  streq100b 89.5  natcmp100 1.77
tolist1 5.0  lower1 3.2  cond1 5.29
bridge_tag 878          (Tag.all reflection of ofName?_markupName, decide +kernel)
bridge_attr 4870        (the Attr analogue; FAILS: kernel application type mismatch)
```

Derivative sizes, `#eval` (`$S/SeqSize.lean`, `$S/SeqSmart.lean`):

```
table, n tr        n=1,2,4,8,16,32  -> 59, 76, 116, 220, 524, 1516
dl, 2n dt          n=1,2,4,8,16,32  -> 35, 75, 203, 651, 2315, 8715
dl, n dt/dd pairs  n=1,2,4,8,16     -> 35, 91, 275, 931, 3395
select, n option   n=1,2,4,8,16,32  -> 27, 46, 90, 202, 522, 1546
smart table, n tr  n=1..64          -> 5 at every n
smart dl, n pairs  n=1..64          -> 9 at every n
agreement: table 0..39 tr -> true;  dl 0..19 dt/dd pairs -> true
```

Wall time, `wall.sh` (floor for import plus a trivial declaration: 1.12 s):

```
nul 1.12  mk_memo 1.23  tb100 2.86  cw33 3.16  dl100 11.86
bridge_tag 2.20  bridge_attr 8.45
```

Core source consulted, under
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`:
`Init/Data/List/Notation.lean:26–61` (the list-literal threshold and the
`%[…]` `let` desugaring).

## Appendix B: what I did not measure

- The heartbeat effect of any recommendation implemented inside the library. R1, R2, R3 and R5 are costed from micro-benchmarks and from a hand-ascribed prototype; none was landed.
- Whether a generated DFA's state set is small enough for a finite agreement check (§5). The constant derivative sizes under simplification say it is; that is inference, not measurement.
- Whether the restricted `Attr` bridge theorem is true. The unrestricted one is false, measured; the restriction to index attributes is INFERRED.
- The mechanism of the 33-child cliff beyond the desugaring that triggers it. The trigger is core source; the 170× factor is measured; the causal chain through the elaborator is INFERRED.
- `String.toList` reduction in the kernel below the level of its measured cost (5.0 ms on a 7-character literal; `Condition.lower` of the same literal, 3.2 ms). `String.length` was measured only inside the length-dispatch probe, never on its own. The C++ kernel is not in this toolchain's sources.
