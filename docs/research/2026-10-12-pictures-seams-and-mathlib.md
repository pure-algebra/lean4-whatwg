# Pictures: the seams, and what Mathlib can certify

2026-10-12. A research note of the SVG seat, after slice S11 of `docs/SVG-PACKAGE-PLAN.md`.

## 1. What was asked

The owner asked which parts of Mathlib could stand behind deep modules for pictures: graphs and
trees of lean4-effect4's programs, drawn with organic lines, with each picture a true account of
the program. Then two directions followed:

- motion as data is wanted;
- look at the seams where data crosses a boundary, since a consumer's proofs spend their effort
  on converting data, and that must be seamless or properly abstracted.

## 2. What was done

Three surveys, each by a seat that read and ran nothing:

- lean4-effect4's own view code, `tools/Tools/View/` at its checkout of this date: what it
  computes, what it proves, and what it wishes for;
- Mathlib at `v4.33.1` for curves, convexity, calculus, lengths, trigonometry, roots and
  intervals;
- Mathlib at `v4.33.1` for graphs, trees, orders, permutations, partitions and finite types.

Then the seat ran trials: small files of statements against the kit as it stands, each checked by
Lean. Section 7 lists them. A statement below that is marked *tried* was proved in a trial. A
statement that is not marked is a proposal.

## 3. The seams

A seam is a place where one kind of data becomes another. There are eight between the consumer
and the kit. For each: what crosses, what was found, and what the kit should do.

### 3.1 Axioms: the consumer's strict rule and exact numbers

The consumer holds its view code to `propext` and `Quot.sound`. The kit's geometry computes in
core `Rat`.

**Found (tried).** In Lean core at this toolchain the *definition* `Rat.add` reaches
`Classical.choice`, and so do `Rat.mul` and `Rat.div`. So does every theorem about them, down to
`Rat.add_comm`. It is not `grind` that brings the axiom in. So a module under the strict rule
cannot call a function of the kit's geometry, and cannot cite a law of it. No proof style
changes that.

**What follows.** The kit needs a layer with no number in it.

- **A structure layer** holds what a picture is made of and how its parts are named and moved:
  a thing with a key, a list of them, the join of two lists by key, a thing that moves by an
  amount, a stored result that stands for a computation. Its laws are about structure. *Tried:*
  a class `Moves` of things that move, with the law that a stored result of a computation that
  moves with its input is the result at the moved input. The law depends on no axiom, and its
  instance at whole pixels depends on `propext` and `Quot.sound` only.
- The consumer gives an instance for its own types. It converts no data. Its laws that are
  about structure (`lowerAll_move`, `cachedStroke_eq`, `join_new`, `join_old`, `sample_end`,
  the retained picture) become instances of the kit's, under its own rule.
- **The geometry layer** stays in `Rat` under the ordinary three axioms, and is one more
  instance of the structure layer. A consumer module that calls it takes the ordinary ceiling.
  That is the consumer's ruling to make, module by module. This repository made it for
  `Whatwg.Svg.Geometry` in ruling R-S25, for the same reason.

### 3.2 Whole pixels and exact numbers

The consumer's coordinates are `Int`. The kit's are `Rat`.

**Found (tried).** Three laws make the crossing exact where it can be.

- A whole count of a unit, as a number, comes back as itself when it is rounded:
  `toGrid s (ofGrid s k) = k`.
- **Rounding commutes with a move by a whole count:**
  `toGrid s (q + ofGrid s k) = toGrid s q + k`. So a law of the form "the figure of a moved
  input is the figure, moved" survives the rounding, for every move by whole pixels. Those are
  the moves the consumer makes.
- The consumer's own `lerp`, which divides whole numbers, is the exact `lerp` rounded down.

**What does not cross.** Two steps that each round down are not the rounding of the two exact
steps. The consumer rounds at every division, and the kit once, where it writes. So the
consumer's bytes change when it adopts the kit, and its 6,949 files of expected output with
them. The kit should let a caller say where a stage ends and its numbers are rounded, so that a
stage is `round ∘ exact` and its error is one unit.

**What the kit should do.** `Vec.ofGrid` and `Vec.toGrid` with these laws, the same for a
segment and a list, and one transfer theorem: a function that commutes with moves, rounded,
commutes with moves by whole counts.

### 3.3 Units

The consumer has three units in one type: logical pixels, device pixels, and thousandths of a
logical pixel for the points of a shape. Its `Call.move` multiplies by a thousand for one
constructor, and its move law carries `r * (1000 * dx)`. In `Rat` there is one unit, the
logical pixel, and a scaling at the device. `Cubic.scale_move` is that law already. No new
module: the port should use one unit.

### 3.4 Speed

Everything in the consumer's viewer is interpreted, and strokes are its hot path.

**Found (tried).** Interpreted, on the port of the consumer's stroke:

| What | Time |
| --- | --- |
| an organic stroke along 11 segments, 178 segments out | 12.5 ms |
| of that, the points of the two sides (noise, a root, a normal) | about 6.5 ms |
| of that, the two splines through the side points | about 2.8 ms |
| the same two splines through side points rounded to thousandths | about 1.2 ms |
| writing the outline as a path, 7,253 characters | 1.8 ms |
| a point of a segment, exact | 17 µs |
| a point of a segment, in whole numbers as the consumer has it | 3 µs |

The exact numbers of a stroke grow to 233 bits. With the side points rounded to thousandths
they stay under 32. Exact arithmetic costs about six times whole numbers for one point.

**What the kit should do.** Round at the stage boundaries of 3.2, which a stroke has: the side
points. The consumer's cache law (3.1) then pays for the rest: a stroke is computed once and
moved.

### 3.5 Three outputs

The consumer writes a row stream that C replays, SVG, and a live session. Its SVG is text built
by hand, and it does not import the kit. The value that every output reads is a list of
segments and boxes. The kit's geometry is already output-neutral in that sense: `List Cubic`,
`Box`. A writer for each output reads the same value. The kit has the SVG writer. A writer of
rows would be the consumer's, on `Vec.round`.

### 3.6 Real numbers

The kit computes in `Rat`, and a drawn curve has a point at every real parameter. The seam is a
cast, and the package `analysis/` holds what is true after it (ruling SV-58).

**Found (tried, and landed in `analysis/WhatwgAnalysis/Box.lean`).** The box of a segment holds
it at every real parameter. Four control values moved by `δ` at most move the curve by `δ` at
most, so a path written at three places is within half a thousandth of the exact segments
along each axis. Both were proved on the first run, in forty lines. A check takes eight seconds.

### 3.7 Motion

The consumer has motion as data already, in part: `Ease`, `Transition` (a delay, a duration,
an easing), `Choreography`, the join of two frames by key, and `sample`, which gives the page
at a moment of a step. It has the end law `sample_end`: the last moment of a step is the next
frame. What it writes is nineteen whole pictures for a step.

**Found.**

- `Transition.at` is the timing model of CSS: before the delay the start, after the end the
  end, and between them the easing of the share of the duration.
- The consumer's two spring easings are tables of twenty-one stops read by straight lines.
  That is the function `linear()` of CSS Easing Functions 2, stop for stop.
- *Tried:* `cubic-bezier(1/3, y1, 2/3, y2)` is the kit's segment from `(0, 0)` to `(1, 1)`
  with those controls, and its `x` at a progress is the progress itself. So its `y` is a
  polynomial of the progress, no equation is solved, and the consumer's cubic easings (`in_`,
  `out`, `outBack`) are such curves exactly.
- A reveal of a line is `stroke-dashoffset` under `pathLength`. An organic stroke is a filled
  outline, so its reveal is a mask: a plain stroke of the centre line, wide enough to cover the
  outline. The consumer's `halfWidth_band` gives that width as a theorem.

**What the kit should do.** A module of motion as data, in the structure layer:

- `Easing` with its meaning as a function of `Rat`, for `linear()` and for the cubic curves
  above, and the two end laws;
- `Transition` with `at`, as the consumer has it;
- `Track`: a key, a property, its two values and a transition; `Motion`: a list of tracks;
- `Motion.sample`, the scene at a moment, with the end law proved once for every scene whose
  parts have a start and an end (a class `Tween` with `at_start` and `at_end`);
- a writer of CSS: `@keyframes`, the `animation` shorthand, `linear()` and `cubic-bezier()`;
  and the same tracks as rows for the consumer's stream.

The law to state between the two readers: at every stop of an easing, the value that CSS
computes is the value of `sample`. One step is then one picture and its tracks.

### 3.8 Names

A key is a `String` in the consumer and a `data-key` attribute in SVG. The kit checks the name
of a data attribute (ruling SV-49). The open law is the consumer's own: the keys of a picture
are distinct, and each is one node of the program. It belongs to the structure layer (section
5, item 1).

## 4. What Mathlib has, in short

For curves and numbers:

- Bernstein polynomials with their sum, their sign and their derivative; convex hulls,
  segments, half spaces and thickenings; Taylor's bound and the mean value theorems; variation
  as the length of a curve; bounds on sine and cosine, on `π` to twenty places, on `exp` and
  `log`; `Nat.nthRoot` with its two bounds; rotations, isometries and dilations; quadratic
  roots; monotone functions glued at a point.
- Tactics that carry the proofs: `positivity`, `gcongr`, `nlinarith`, `linear_combination`,
  `field_simp`, `push_cast`, `fun_prop`.

For layout:

- Walks, paths, reachability, trees and their edge count for simple graphs; paths and
  arborescences for quivers; `Order.height` and chains and antichains; `Tuple.sort` and the
  sign of a permutation; partitions of a finite set and of a box, with the sum over a
  partition; disjoint intervals of a monotone sequence; actions of a group on a set.

What it does not have, so that nobody looks again: splines, Bézier curves beyond the Bernstein
basis, de Casteljau's recurrence; the length of a curve as an integral; remainders of sine and
cosine of any order; interval arithmetic with signs; a Lipschitz lemma for the arctangent;
curvature, offset curves and winding numbers; a type of acyclic directed graphs; a computable
topological sort; Dilworth's theorem; series-parallel orders; planarity and crossing numbers;
the count of inversions of a permutation; rose trees; any drawing of a tree or a graph;
L-systems.

So the pattern of SV-58 holds everywhere: core computes, and Mathlib says what the computation
means. No layout and no curve is taken from Mathlib.

## 5. Modules, in order

Each line: what the caller gets, the law that makes it worth having, and where the proof is.

1. **Structure layer.** Keyed things, `Moves`, the join by key, a stored result, a patch from
   one keyed list to the next. Laws: every key enters, updates or exits; a moved list is the
   list of moved things; a stored result is the result; keys are distinct and one to one with
   the program's nodes. Core, with no number, under the strict rule. *Tried in part.*
2. **Grid seam.** Section 3.2. Core. *Tried.*
3. **Motion as data.** Section 3.7. Core for the data, the meaning and the writer. *Tried in
   part.*
4. **A stroke of varying width.** One function from a centre line and a width at each point to
   a closed outline: both sides, the two ends, round or pointed, a collar where it meets a box,
   and a join where a branch leaves a trunk. Laws: the outline is closed; a moved line gives the
   moved outline; the outline lies within the centre line's box grown by the greatest
   half-width; with a wobble of amplitude `a`, two lines whose clearance is more than `2a` do
   not touch. Core computes. Mathlib certifies the band at every real parameter. The port
   wrote 106 lines of this by hand.
5. **Smooth joins.** *Tried:* a cardinal spline and a basis spline leave each joint with the
   velocity they arrive with, and a basis spline with the same bend. Core, two lines each.
   Mathlib would state it as `ContDiff`; the lemma that glues two pieces is not in Mathlib and
   is written once.
6. **Flattening with a tolerance.** *Tried:* a segment's distance from its chord at `t` is
   `t (1 - t)` times a mean of its two second differences. So `Cubic.flatten c tol` can choose
   its number of parts from a stated bound. This serves the row stream, hit tests and lengths.
7. **Arcs.** A circular arc as cubics from rational data, with the distance from the circle
   bounded at every parameter. It gives donuts, arcs between nodes, and the path chapter's
   elliptical arc. The same proof replaces the five sampled checks of `corner_near_circle`.
8. **Roots and angles.** `rootDown k q n`, the `k`-th root to `n` places, for d3's default
   Catmull-Rom spline and for power scales. Sine and cosine of an angle in degrees to a stated
   error, and `turnDeg`, an exact isometry within a stated angle of the one asked for, so that
   `rotate(θ)` has a reading for every angle.
9. **The monotone curve.** d3's `curveMonotoneX` with the law that it does not overshoot.
10. **Layout laws.** In the survey's order of value for effort: `pick` answers a key exactly
    when the point is in its box; `ranks` is the least layering, and with Mathlib equals
    `Order.height`; a stack of intervals tiles its range, which gives the icicle and the flame
    graph; boxes of one rank are pairwise apart after `spread`; a tidy tree with separation,
    centred parents and no crossing; a treemap as a partition with areas in proportion; Kahn's
    order exists for every acyclic graph; a sweep never adds a crossing.

Items 1 to 3 are the owner's stated order. Item 4 is the consumer's first wish and the port's
largest hand-written part.

## 6. Decisions that are the owner's

- Whether a consumer module that calls the geometry takes the ordinary three axioms (3.1).
- Whether the consumer's expected output files may change when a stage is rounded once (3.2).
- Whether `analysis/` becomes a package that another repository can require. That needs a
  path dependency on the library, which fetches three more of its dependencies.

## 7. The trials

Each was a file outside the tree, checked with `lake env lean`, and for the last two with
`lake -d analysis env lean`.

| Statement | Result |
| --- | --- |
| the axioms of `Rat.add`, `Rat.mul`, `Rat.div`, `Rat.add_comm`, and of twelve definitions and laws of the kit | all reach `Classical.choice`; `Rat.floor` and `Int.add_assoc` do not |
| `cached_eq`, a stored result of a computation that moves with its input | proved; no axiom |
| a list of whole-pixel points moved twice | proved; `propext`, `Quot.sound` |
| `toGrid_ofGrid`, `toGrid_add_ofGrid` | proved |
| the consumer's `lerp` is the exact one rounded down | proved |
| `cubic-bezier(1/3, y1, 2/3, y2)` as a segment | proved |
| a cardinal and a basis spline keep their velocity at a joint; a basis spline keeps its bend | proved |
| the distance of a segment from its chord | proved |
| four points each moved inside a box move the point of the segment inside that box | proved |
| the times of section 3.4 | measured |
| the box of a segment holds it at every real parameter | proved, in `analysis/` |
| a rounded segment stays near the exact one | proved, in `analysis/` |
