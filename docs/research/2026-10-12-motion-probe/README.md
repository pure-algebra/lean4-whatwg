# Motion probes

2026-10-12. Three pages that programs of the workshop write from the kit, with data like
lean4-effect4's. The first two show one step twice: animated by a browser from the CSS that the kit
wrote, and as five still pictures at the moments 0, 250, 500, 750 and 1000 that the kit's own
reading (`Track.at`) computes. The two must agree.

| Page | Written by | The data | What moves |
| --- | --- | --- | --- |
| `pfork.html` | `workshop/MotionProbe.lean` | one frame of lean4-effect4's viewer, the program `pFork`, read from its rendered picture; and that frame less the body of the fork | a kept row moves down three rows; three new rows appear one after another; a fiber grows on a spring; the fork between two fibers, an organic stroke, draws itself behind a mask; its collars appear |
| `tree.html` | `workshop/TreeProbe.lean` | the tree of `pFork` before and after the body of the fork is written, with its keys | four kept nodes move; three kept edges change their shape and stay joined to their nodes; three new edges draw themselves and three new nodes grow, level by level; an edge's width is the root of its share of the leaves |
| `between.html` | `workshop/BetweenProbe.lean` | a rank of four boxes with the widths and the gap of lean4-effect4's flow layout; one box leaves | the two boxes to its right close the room, timed three ways; under each way the least gap between two neighbours over the step, by the kit's reading |

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
- A new thing needs its own entrance: a row appears, a box grows, a line draws itself.
  `Motion.arriveWith` takes the entrance from the thing, and `Motion.delayed` starts each
  level after the one above it.
- Where two branches left one node their strokes lay over each other. They leave at the ports
  of a row of their widths now (`ports`), side by side. A true join of a branch and a trunk is
  not built yet.
- A gap that both pictures have is a gap of every moment only under two premises. With one
  timing and an easing in range the least gap of `between.html` is 16, the gap of both
  pictures. With the farther box started first it is -141. With an easing that passes its end
  it is -2. The browser measured -140.3 and -1.3 at those moments. `Kept.moment` of
  `Whatwg/Svg/Scene/Between.lean` is the law, and its controls are these two failures.
