# Motion probes

2026-10-12. Eight pages that programs of the workshop write from the kit, with data like
lean4-effect4's. The first two show one step twice: animated by a browser from the CSS that the kit
wrote, and as five still pictures at the moments 0, 250, 500, 750 and 1000 that the kit's own
reading (`Track.at`) computes. The two must agree.

| Page | Written by | The data | What moves |
| --- | --- | --- | --- |
| `pfork.html` | `workshop/MotionProbe.lean` | one frame of lean4-effect4's viewer, the program `pFork`, read from its rendered picture; and that frame less the body of the fork | a kept row moves down three rows; three new rows appear one after another; a fiber grows on a spring; the fork between two fibers, an organic stroke, draws itself behind a mask; its collars appear |
| `tree.html` | `workshop/TreeProbe.lean` | the tree of `pFork` before and after the body of the fork is written, with its keys | a step in stages (`Motion.staged`): four kept nodes move and three kept edges change their shape and stay joined to their nodes, all at rest by the moment 300; then three new edges draw themselves and three new nodes grow, level by level, each level in a slot of its own; an edge's width is the root of its share of the leaves. A third row shows the five moments as the browser computes them, from the same tracks opened at the moment and paused |
| `between.html` | `workshop/BetweenProbe.lean` | a rank of four boxes with the widths and the gap of lean4-effect4's flow layout; one box leaves | the two boxes to its right close the room, timed three ways; under each way the least gap between two neighbours over the step, by the kit's reading |
| `branch.html` | `workshop/BranchProbe.lean` | a trunk that forks in two, each branch with half the share, at lean4-effect4's default wobble and at a lesser one | nothing moves: four panels at one scale, the exponent of the widths across and the wobble down; under each the narrowest place of the trunk and the widest place of a branch |
| `row.html` | `workshop/RowProbe.lean` | a rank of four boxes with the gap of lean4-effect4's flow layout; one box gets wider, as when its label grows, and its neighbour narrower by as much | the rank changes in four ways; under each the least and the greatest gap, and the least and the greatest length of the rank, over the step |
| `label.html` | `workshop/LabelProbe.lean` | eight qualified names such as a picture of a program holds, in lean4-effect4's grid of cells eight pixels wide | nothing moves: every name in rooms of six widths, fitted each by itself and then together; under each table the pairs of different names shown as one text |
| `cross.html` | `workshop/CrossProbe.lean` | two ranks of a graph of fibers and the straight links between them | the ends of the links move in three ways; under each the count of crossings at the start and each moment at which it changes |
| `resume.html` | `workshop/ResumeProbe.lean` | the rank of `between.html`: one box is leaving and two are closing the room when, at the moment 400, a second box is asked to leave | nothing moves on the page: for each of two ways, the last picture of the first step and the first picture of the second, each computed by the browser from tracks opened at the moment and paused; under them where each box stands in the two |

To write them again, from the repository root after `lake build`:

```bash
lake env lean workshop/MotionProbe.lean
```

```bash
lake env lean workshop/TreeProbe.lean
```

```bash
lake env lean workshop/BetweenProbe.lean
```

```bash
lake env lean workshop/BranchProbe.lean
```

```bash
lake env lean workshop/RowProbe.lean
```

```bash
lake env lean workshop/LabelProbe.lean
```

```bash
lake env lean workshop/CrossProbe.lean
```

```bash
lake env lean workshop/ResumeProbe.lean
```

## What a browser said

One profile: Chrome 152, the browser pane of the session that wrote the pages. A host
observation is evidence about that host, and no theorem.

- Every animation parsed: its name, its two keyframes, its duration, its delay, its easing and
  its fill. `translate`, `scale`, `opacity`, `stroke-dashoffset` and `d` were each read as a
  property.
- `cubic-bezier(0.333333, 1.567, 0.666667, 1)` at eleven moments gave 0, 0.408781, 0.705728,
  0.907047, 1.02894, 1.08762, 1.0993, 1.08016, 1.04643, 1.01431 and 1. The kit's reading
  `Easing.at` gave 0, 408, 705, 907, 1028, 1087, 1099, 1080, 1046, 1014 and 1000: each the
  browser's value in per mille, rounded down.
- `linear(…)` of twenty-one stops gave the stop's value at each stop.
- A reveal under `pathLength` of a thousand gave `stroke-dashoffset` of a thousand less the
  kit's reading at each of eleven moments.
- A mask whose line is revealed showed a filled outline from its start, as far as the line was
  drawn.
- A change of shape between two paths of the same commands was drawn point by point: at a
  tenth of a step the first point of an edge stood between its two ends, where the kit's
  `ICubic.mix` puts it.

## What the probes found

- The first reading of a transition rounded its progress to a thousandth before the easing. The
  browser showed a size of 0.419 where the kit read 0.416. `Transition.at` now reads its easing
  at the exact share of the duration (`Easing.of`), and the law `Transition.at_cubic` says that
  the reading is the browser's polynomial, rounded down once.
- An edge between two nodes that move differently must change its shape, or it leaves its
  nodes. `Change.morph` says so, and the same transition on the node and on the edge keeps
  them joined (`mix_shift`).
- A new thing needs its own entrance: a row appears, a box grows, a line draws itself. A plan
  takes the entrance from the thing (`Plan` of `Whatwg/Svg/Scene/Plan.lean`, which since slice
  S14 stands where `Motion.arriveWith` stood), and `Motion.delayed` starts each level after the
  one above it.
- Where two branches left one node their strokes lay over each other. They leave at the ports
  of a row of their widths now (`ports`), side by side. A true join of a branch and a trunk is
  not built yet.
- A gap that both pictures have is a gap of every moment only under two premises. With one
  timing and an easing in range the least gap of `between.html` is 16, the gap of both
  pictures. With the farther box started first it is -141. With an easing that passes its end
  it is -2. The browser measured -140.3 and -1.3 at those moments. `Kept.moment` of
  `Whatwg/Svg/Scene/Between.lean` is the law, and its controls are these two failures.
- A width means a share, so a branch must not look as wide as its trunk. At Leonardo's rule a
  trunk of 9 pixels has branches of 6.36, and `Branch.wobbleRoom` gives the two a room of 171
  per mille. At a wobble of 350, the noise of lean4-effect4's look `organic`, the narrowest
  place of the trunk in `branch.html` is 7.04 pixels and the widest place of a branch 7.55. At a
  wobble of 150 the trunk is the wider at every point, as `Branch.wobbleRoom_apart` says it must
  be. Since lean4-effect4's slice D2 its default look has a noise of 0, so the finding is of the
  look `organic` alone (the Effect4 coordinator's guidance 4), and lean4-effect4 refuses a look
  whose noise is over the room.
- The times of a sheet must be exact. `tree.html` shows five moments twice: as the kit reads
  them, and as Chrome 152 computes them from the same tracks, opened at the moment and paused,
  with no script. With each duration rounded to a whole millisecond the browser drew a line to
  953.06 of a thousand where the kit read 952: it read another share of the duration. With the
  times written exactly it draws the line to 952.145 and a size of 0.768857, and the kit reads
  952 and 768: each the browser's value, rounded down (`Transition.at_eq_floor`). The two rows
  agree to 0.05 of a unit.
- An edit moves a tree in rigid groups. The step of `tree.html` is one edit: the subtree at the
  fork is replaced (`Tree.replace`), and the page reads from the two spans of each node what the
  edit did to it. The root and `withFiber`, on the way to the address, are stretched: each keeps
  its first column, and its last moves by the leaf that the edit gains. `awaitFiber`, after the
  edit, is shifted by that leaf with its width as it was. The rest is the new subtree.
  `Tree.spans_replace` says that every kept node of every edit is in one of the three groups,
  and `Span.Shifted.moment` that the nodes after an edit keep the steps between them at every
  moment, so the edges among them need no change of shape.- A rank whose boxes change their widths keeps its gaps and its length only if its edges move,
  and not its boxes or its lengths one by one. In `row.html` both pictures have a gap of 16 and
  a rank of 664. With each box at its own time the gap runs from -42 to 17 over the step. With
  one timing and each length mixed by itself the gaps hold and the rank is 663 at some moments:
  the roundings of the lengths do not add up. With the edges mixed (`Row.between`) the gap is
  16 and the rank 664 at every moment, and also with an easing that passes its end, where the
  boxes go past their widths and the gaps do not move. Chrome 152 measured the same on the
  drawn boxes at a hundred and one times: a gap from -41.8 to 16 in the first way, and exactly
  16 and 664 in the last two. `Row.tiles_between`, `Row.between_conserves` and `Row.between_mem`
  are the laws.
- Two names that differ must not become one text when a room is small. In `label.html`, in a
  room of twelve cells, a cut that keeps the piece that matters most shows `Stream.mapEffect`
  and `Sink.mapEffect` both as `…mapEffect` where each label is fitted by itself. Fitted
  together (`Label.fitAll`) each of the two is a sign, a dot: the picture says that it does not
  tell them apart, and no pair of names has one text in any room. `Label.fitAll_distinct` is the
  law. In a room of sixteen cells both names are whole.
- A step that keeps the order of the ends of two links on both ranks keeps their crossings: in
  the first step of `cross.html` the one crossing is there at each of a hundred and one moments
  (`crosses_on_way`). A step that changes an order to take a crossing out loses it once, by the
  moment 290, and gains none. Two links that change places, with their lower ends passing
  before their upper ends, have no crossing before and none after, and one from the moment 260
  to the moment 290: a swap of two neighbours is seen as a crossing, and no timing of straight
  ends avoids it.
- The laws of a gap hold between the whole moments too. Chrome 152 was asked for the least gap
  of the three steps of `between.html` at 998 times that are no whole thousandths of the step.
  It gave 16.0000 for the first, where `Transition.exact_gap` of
  `Whatwg/Svg/Geometry/Moment.lean` says that no rational time has less, and -140.25 and -1.59
  for the two that break a premise.
- A step that starts from the still picture makes every moving thing jump when it interrupts
  another. In `resume.html` two boxes stand at 201 and 433 at the moment 400 of the first step,
  and the box that is leaving has 488 of a thousand of its opacity. A second step from the still
  picture starts the two at 160 and 392, a jump of 41 pixels, and the leaving box at full
  opacity. The step that resumes (`Plan.resume`) starts them at 201 and 433 and at 488, and ends
  on the third picture. Chrome 152 drew the four pictures with no script and measured 201.1
  and 433.1, then 160 and 392 in the first way and 201 and 433 in the second, with the opacity
  0.488 kept. `Motion.nothing_jumps` and `Motion.nothing_moves` are the laws.
