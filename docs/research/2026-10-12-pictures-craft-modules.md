# Pictures: craft modules for graphs of programs

2026-10-12. A design note of a design seat, after
`docs/research/2026-10-12-pictures-seams-and-mathlib.md` (below: the seams note). The seat read
files and wrote this one. It ran no Lean, built nothing and fetched nothing. Every signature
below is a sketch, and every law is a statement that no checker has seen.

## 1. What was asked

The owner, verbatim:

> think through other deeply practical but powerful modules we would need for the subtle,
> gorgeous features of graph rendering, draw from the animation industry, deep typography, ed
> tufte, and natural organic design school and scientific handling to accord to our semantics..
> put a seat on this and land the suggestions as we go. create actual animations using data like
> mine to probe keep building with strong lean semantics and build practices

Earlier, on the same work: "gorgeous, detailed, organic, semantically perfectly accurate graph /
trees visuals for our effect4 lean eff reification project", "we definitely want the motion as
data stuff", and "look at seams where data boundaries are because that often becomes the hard
part for a consumer is having their proofs handle data conversion so that should be done
seemlesslpy or properly abstracted and considered".

This note gives three things:

- what each of five bodies of craft knows that a graph of a program needs (section 4);
- sixteen modules that section 5 of the seams note does not list, in order of value (section
  5). Fourteen are not in the kit. Two, M2 and M3, sharpen what another seat landed while this
  note was written; each says what exists and what it adds;
- the order to build them in, and the first three (section 6).

## 2. What was read

- The seams note, in full.
- The kit: `Whatwg/Svg/Scene/` (`Moves`, `Join`, `Join/Laws`, `Motion`, `Motion/Laws`, `Tree`);
  `Whatwg/Svg/Geometry/` (`Vec`, `Cubic`, `Box`, `Grid`, `Easing`, `Noise`, `Stroke`,
  `Stroke/Laws`, and the headers of `Shape`, `Smooth`, `Near`, `Root`, `Outline`, `Write`,
  `Affine/Map`); the four writers under `Whatwg/Html/Node/`; two files of
  `analysis/WhatwgAnalysis/`.
- The consumer, read only: `tools/Tools/View/` of lean4-effect4 (`Picture`, `Look`, `Organic`,
  `Motion`, `Graph`, `Flow`, `Page`, `Output`, `Grid`, and the headers of `Retained`, `Inc`,
  `Live`, `Tokens`, `Place`, `Run`, `FlowLaws`), and three of its research notes: the visual
  pipeline, the visual language and the organic strokes.

**The kit moved while the seat read.** Another seat was landing slice S12 and a motion probe in
the same worktree. A second reading, at the end, found these in the tree, and the note is
written against it:

- `Pose.shape`, `ICubic.mix` and `Change.morph` in `Scene/Motion.lean`: a change of shape from
  one list of segments to another. Two lists of different lengths have no shape between them,
  and the change is a jump at the middle;
- `Change.morphOf` in `Geometry/Grid.lean`, and the property `d` in the writer of CSS;
- `Motion.arriveWith` and `Motion.delayed`: an entrance for each thing, and a later start for
  each key;
- `Scene/Motion/Laws.lean`, with `Track.at_done`, and `Scene/Tree.lean`, a tree's spans;
- `docs/research/2026-10-12-motion-probe/README.md`: two pages, and what Chrome 152 said of
  them.

M2 and M3 below say what of them exists and what they add.

Seven facts from the reading carry the designs below.

1. The consumer's `lerp` and the kit's `mix` are one definition:
   `v + (u - v) * (1000 - e) / 1000`. A law of `mix` is a law of `lerp` with no conversion.
2. The consumer's `Grow.split n` is the whole square root of `10 ^ 12 / n`. Its only check is a
   finite evaluation at six counts.
3. An edge whose two ends move by two different steps must change its shape, or it leaves its
   boxes. `Change.morph` does that for two lists of one length. No law yet says what holds of
   the shape between, and an edge that gains a segment jumps.
4. `sampleLaid` of the consumer computes its stagger by hand: the levels, a slot for each, and
   two transitions made for each level. No law says that a box opens after its edge arrives.
5. The consumer measures a note in the label face, which is proportional, by its count of
   characters (`lineCells`). No part of the kit measures a text.
6. `Flow.unresolvedWaits` lists the waits that the reading cannot resolve. No drawing reads it.
   An unresolved wait and no wait are drawn alike: no edge.
7. The default look moves each edge of a line by up to 350 per mille of its half-width. A
   branch of a fork of two is 707 per mille as wide as its trunk. The two bands overlap.

## 3. The rule that ranks the modules

A picture of a program is a statement. Each channel of it says one thing: a place says an order,
a width says a share of work, a colour says a kind, a motion says a change. The consumer's own
rule is that every channel is the image of a fold, and that no channel holds a meaning twice.

A module is ranked first by how many false statements it stops, and then by its cost. There are
four kinds of false statement.

| Kind | Example |
| --- | --- |
| A relation that the data does not have | two boxes in a row where the data is a set; two lines that join drawn as if one passed under the other |
| A difference that the data has and the picture hides | two shares drawn at one width; two labels cut to one text |
| A moment between two pictures that neither program has | two boxes over each other half way through a step; an edge end off its box |
| A mark with no meaning that is read as one | a wobble wider than the difference between two widths |

Each module below names the invariant it guards, in those terms.

## 4. Five bodies of craft

For each: what it knows, what a graph of a program needs of it, and where that goes. "Exists"
means that the kit or the consumer has it. "Dropped" means that the idea makes a picture
prettier and less true. M1 to M16 are the modules of section 5.

The sources are recalled, not read for this note. No locator is given.

### 4.1 The animation industry

| What it knows | What a graph of a program needs | Where |
| --- | --- | --- |
| Timing and spacing: how long a move takes, and where the thing is at each moment | things that keep a relation take one timing, so the relation holds at each moment | M1 |
| Slow in and slow out | a thing that enters slows into its place; a thing that leaves speeds up | exists (`Easing`, the choreography) |
| Arcs: a living thing moves along an arc | an arc takes a box out of the line between its two places, and the order laws of M1 stop holding. Two things that change places are the one case where a straight move is false too | dropped for ordered things; M1 reports the pairs |
| Anticipation: a small move the other way first | it shows a place that the thing never had | dropped for places. The lit state before an edit is true anticipation, and it is data |
| Follow-through and overlapping action: parts arrive at different times, and pass their rest | an edge follows its boxes exactly, with no lag. A size may pass its rest by less than the gap to its neighbour | M1 (`grow_clear`), M2 |
| Staging: one idea at a time | what leaves, then what moves, then what enters; what does not change is drawn fainter | M3, M5, M13 |
| Secondary action | the collar that forms where a line arrives, and the tip that narrows while it grows, are functions of the reveal | exists (`Stroke`) |
| Squash and stretch | on a label it hurts reading. On a box it changes the width, and the width means the length of the text | dropped; a size grows evenly, and the text appears at rest, as the consumer does |
| Exaggeration | a picture of data must not exaggerate | dropped |
| Appeal: line with character | width that varies with meaning, ends that are finished | exists (`Stroke`), M4, M10 |
| Pose to pose against straight ahead | a step is two pictures and tracks, not a row of pictures | exists (`Motion`) |
| Choreography and stagger | order in time is order in the program: a thing appears after what it comes from | M3 |
| Duration against distance: a longer travel takes longer, and less than in proportion | one duration for a step, from its longest travel, so that M1's premise holds | M3 |
| Entering, leaving, a shared element | the join by key is the shared element. A region that closes into one node is a container that changes shape | exists (`Join`), M2 |
| Springs against curves | a spring has constants with a meaning and can be interrupted. A table of stops cannot be retargeted | M15, M3 (`retarget`) |
| Reduced motion | the change is still shown, with no travel. A row of still pictures is the other form | M3 (`reduced`), M13 |

### 4.2 Deep typography

| What it knows | What a graph of a program needs | Where |
| --- | --- | --- |
| Measure: a line of prose reads best at 45 to 75 characters | a note and a tip have a room in characters; code has 80 cells | M7 |
| Leading and a baseline grid | every face stands on the row's baseline; a row holds each face's ascent and descent | exists (the consumer's grid), M6 (`FitsRow`) |
| Optical sizes | a small face wants a larger x-height and more space. The host has the fonts | a request to the host, in M6 |
| Tabular against proportional figures | addresses and counts align in a column only where every digit has one advance | M6 (`tabular`) |
| Small capitals and letterspacing | a region's name can stand in small capitals with wider spacing. Both change the width | a request to the host, counted in M6's bounds |
| Hanging punctuation and optical margins | the bracket of an address can hang, so that digits align | a choice of the layout; no module |
| Kerning | it changes a width by a little, and the host does it | M6 states it as a bound |
| Widows and orphans | a label of two lines has no single short piece on its last line | M7 (balance) |
| Hyphenation and justification, Knuth and Plass | see below | M7 |
| Labels on a path | see below | M11 |
| Label placement without collision | an edge's label, a region's name and a note stand beside their marks and on nothing | M11 |
| Truncation with meaning kept | a cut label keeps the piece that names the thing, and two different labels stay different | M7 |
| Bidirectional text | the order of tokens that a reader sees is the order of the program's text | M14 |

Knuth and Plass break a paragraph by least total badness. Three things fail for a label in a
box. The method needs the width of every piece, and Lean has none. It justifies, and in a room
of twenty characters justified text has uneven spaces. It hyphenates, and a hyphen inside a name
shows a name that the program does not have. What to do instead: ragged right, the same total
fit with the widest line as the cost, at most three lines, and no break inside a name.

A label along a curve needs the advance of each character and turns each one. Turned text reads
slower, and the row stream has no call for it. It is dropped. A label stands level, beside the
straightest part of its edge.

What a layout can decide with no font metrics:

- the order of lines and rows, and the baseline of each;
- every width in a face with one advance: the data face, in cells;
- which face, size, weight and features to ask for;
- where a label may break and which pieces go first when it is cut.

What a layout must be given:

- for a proportional face, the advance of each character, as a least and a greatest value;
- the ascent, the descent, the cap height and the x-height of each face at its size;
- whether digits have one advance, and whether the host kerns or joins letters.

### 4.3 Edward Tufte

| What he says | What a graph of a program needs | Where |
| --- | --- | --- |
| Data-ink: ink that shows data | each channel has one row in a table of what the picture says. A mark with no row goes | M8 (`Encoding`) |
| Chartjunk | no texture, shadow or grain that says nothing | dropped (section 4.4) |
| Layering and separation | frames and rules are fainter than ink; depth takes weight and tone in steps | M5 (`ramp`), M8 (`steps`) |
| The smallest effective difference | a difference is large enough to see and no larger. A wobble is smaller than the least difference that has a meaning | M4 (`wobbleRoom`), M5, M8 (`ties`) |
| Small multiples | the frames of a build side by side, at one scale, each thing in one place | M13 |
| Sparklines | a fiber's states over a run, in the room of a word | M12 |
| Micro and macro readings | each cell is read alone; the shape of the whole says how parallel the run is | M12, M7 (the ladder) |
| 1 + 1 = 3: two strokes near each other make a third thing, the space between | a list of marks that are too near; a gap only where lines cross | M9 |
| Colour as quantity and as label | hue for a kind, at one lightness; lightness for a quantity. Never both in one channel | M5 |
| Annotation beside the mark | a label is within a stated step of what it names | M11 |
| Showing uncertainty | known, unknown and absent are three styles | M10, M8 (intervals) |
| The lie factor | twice the quantity is twice the length; a scale that does not start at nothing says so | M8, M4 |

### 4.4 The natural and organic school

| What it knows | What a graph of a program needs | Where |
| --- | --- | --- |
| Leonardo's rule: the squares of the branches' widths sum to the trunk's | a width that means a share of work, at every depth | M4 at `k = 2` |
| Murray's law: the cubes of the radii sum | the same, with another exponent | M4 at `k = 3` |
| Phyllotaxis: seeds at the golden angle | a set with no order, drawn with no first and no last | M16 |
| Growth by rule, L-systems | the fold of the program is the grammar. A second grammar would draw a structure that the program does not have | dropped. Growth by age exists (`tip`) |
| Reaction and diffusion | a texture with no meaning, at a high cost | dropped |
| Meanders | a bend that means nothing. The consumer's steer was to remove such bends | dropped |
| Tapering | a line that grows narrows to its tip | exists (`Stroke.organic`) |
| The wobble of a hand-drawn line | bounded, seeded by the key, and smaller than a difference that means work | exists (`Noise`), M4 |
| Line weight for depth: the near contour is heavier | a deeper region is never heavier than a shallower one | M8 (`steps`) |
| The near line breaks the far one | a gap in the line that passes under, at a crossing and nowhere else | M9 |
| Stipple and hatch for tone | a tone as a share of ink, in one colour | M10 |
| Ink on paper | a rough edge is the noise, and ink that pools is the collar. Paper grain is a filter of one output | exists; grain is dropped |
| Seeded irregularity | a thing looks the same each time it is drawn and in each panel; a texture belongs to its object and does not move inside it | exists (`Noise.seedOf`), M10 |

### 4.5 Scientific handling

| What it asks | What a graph of a program needs | Where |
| --- | --- | --- |
| Perceptually uniform colour | equal steps of a quantity are equal steps of lightness | M5 (OKLab) |
| Colour-vision deficiency | two kinds are told apart by a reader with one kind of cone missing, and without colour at all | M5, M10 |
| Contrast for legibility | ink on ground passes a stated ratio, by a test that Lean decides | M5 (WCAG 2). APCA is a draft; see M5 |
| Honest scales | zero, a logarithm and a broken axis are each named in the picture | M8 |
| Units | a length, a time and a count are not mixed | M8 for the scale's two ends. See section 8 for the rest |
| Error bars and bands | a band holds the mark of every value in the interval | M8, M6 |
| Rounding that is stated | exists at the grid. Two values that round to one mark are listed | exists (`Grid`), M8 (`ties`) |
| Reproducibility from a seed | the picture is a function of the data and the look, and not of the order in which a hash map gave its entries | exists (`seedOf`), M16 (`arrange_perm`) |
| No relation that the data does not have | every module names one | section 3 |

## 5. The modules, ranked

| Rank | Module | Layer | Effort | Value | Draws from |
| --- | --- | --- | --- | --- | --- |
| M1 | `Between`: what holds at every moment of a step | strict | small | large | animation, science |
| M2 | `Morph`: an edge between two pictures | strict, geometry, writer | medium | large | animation |
| M3 | `Score`: order in time | strict, writer | small | large | animation |
| M4 | `Branch`: widths that conserve | strict | small | large | organic, Tufte |
| M5 | `Colour`: kinds and quantities that can be told apart | strict, `analysis/` | medium | large | science, Tufte |
| M6 | `Metrics`: what a host says of a face | strict | small | large | typography |
| M7 | `Label`: a label in a room | strict | medium | large | typography, Tufte |
| M8 | `Scale`: a quantity as a length, and what the picture says | strict | small | medium | science, Tufte |
| M9 | `Cross`: crossings, gaps and marks that are too near | strict, geometry, `analysis/` | medium | medium | Tufte, organic |
| M10 | `Dash` and `Texture`: styles of state | geometry | medium | medium | organic, Tufte, science |
| M11 | `Place`: labels beside marks | strict | medium | medium | typography, Tufte |
| M12 | `Strip`: a sequence in the room of a word | strict | small | medium | Tufte |
| M13 | `Multiples`: panels at one scale | strict | small | medium | Tufte, animation |
| M14 | `TextOrder`: text that cannot reorder its line | writer | small | medium | typography, science |
| M15 | `Spring`: an easing from its constants | geometry, `analysis/` | large | small | animation |
| M16 | `Bag`: a set with no order | geometry | small | small | organic, science |

"Strict" is `Whatwg/Svg/Scene/`: no rational number, `propext` and `Quot.sound` only. "Geometry"
is `Whatwg/Svg/Geometry/`, in `Rat`. "Writer" is `Whatwg/Html/Node/`.

Four of these want a box of whole units in the strict layer, beside `IVec` and `ICubic`:

```lean
namespace Whatwg.Svg.Scene

/-- A box of whole units with sides along the axes. -/
structure IBox where
  x0 : Int
  y0 : Int
  x1 : Int
  y1 : Int

/-- The two boxes share no area. -/
def IBox.Disjoint (a b : IBox) : Prop := a.x1 ≤ b.x0 ∨ b.x1 ≤ a.x0 ∨ a.y1 ≤ b.y0 ∨ b.y1 ≤ a.y0

instance : Moves IVec IBox
```

It lands with the first module that needs it. The consumer's `Rect` has the same four fields.

### M1. `Between`: what holds at every moment of a step

- **Name and one line.** The caller gets the facts of two still pictures that are facts of
  every moment between them.
- **What it draws from.** Animation: timing and spacing, arcs, follow-through, squash and
  stretch. Science: no relation that the data does not have.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Between.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- The easing never leaves the range from its start to its end. -/
def Easing.bounded : Easing → Bool
  | .stops values => values.all fun v => 0 ≤ v && v ≤ 1000
  | .cubic y1 y2 => 0 ≤ y1 && y1 ≤ 1000 && 0 ≤ y2 && y2 ≤ 1000

/-- How far past its end the easing goes at most, per mille: a bound, not the least one. -/
def Easing.over : Easing → Nat
  | .stops values => (values.foldl max 1000 - 1000).toNat
  | .cubic y1 y2 => (max 1000 (max y1 y2) - 1000).toNat

/-- A relation of two places that every moment between two pictures keeps. -/
def Kept (R : IVec → IVec → Prop) : Prop :=
  ∀ {a a' b b' : IVec} {e : Int}, 0 ≤ e → e ≤ 1000 → R a b → R a' b' →
    R ⟨mix a.x a'.x e, mix a.y a'.y e⟩ ⟨mix b.x b'.x e, mix b.y b'.y e⟩

/-- The pairs of kept things that are apart in both pictures, and along no one axis in both.
A straight step may bring such a pair together. -/
def unsure {α κ : Type} (key : α → κ) (place size : α → IVec) (j : Join α) : List (κ × κ)

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A motion means a change. Each moment between two
  pictures is a picture, and a reader reads it. The invariant: *a relation along one axis that
  both pictures have is a relation of every moment between them.* It has two premises. The
  things related take one timing. The easing stays in range. The module must never show two
  boxes of one rank over each other, an edge end off its box, or a thing outside the two
  pictures' common box. Three rules of craft follow, each with its reason:
  - stagger the things that enter, and never the things that are kept;
  - an easing that passes its end is for a size, and never for a place;
  - a kept thing travels straight. An arc is dropped.
- **Laws worth proving.** Core proves all five, under the strict rule.
  - `mix_gap`: `0 ≤ e → e ≤ 1000 → u₁ + g ≤ u₂ → v₁ + g ≤ v₂ → mix u₁ v₁ e + g ≤ mix u₂ v₂ e`.
    A gap of both pictures is a gap of every moment. It holds with the rounding. With
    `w = 1000 - e` and `aᵢ = uᵢ - vᵢ`, the difference of the two values is
    `(v₂ - v₁) + ⌊a₂ w / 1000⌋ - ⌊a₁ w / 1000⌋`. The difference of two floors is no less than
    the floor of the difference. Where `a₂ ≥ a₁` that floor is not negative. Where `a₂ < a₁` it
    is no less than `a₂ - a₁`, since `w ≤ 1000`. Both cases give `g`.
  - `mix_add`: `mix (u + c) (v + c) e = mix u v e + c`, for every `e`. A thing that stands a
    fixed step from another in both pictures stands that step from it at every moment.
  - `mix_mem`: a value between `lo` and `hi` in both pictures is between them at every moment.
  - `bounded_at` and `at_le_over`: `e.bounded = true → p ≤ 1000 → 0 ≤ e.at p ∧ e.at p ≤ 1000`,
    and `e.at p ≤ 1000 + e.over`. These give the first three laws their premise from data.
  - `grow_clear`: two boxes of widths `w₁` and `w₂`, a gap `g` apart, each grown about its
    middle to at most `1000 + o` per mille, share no unit when `(w₁ + w₂) * o ≤ 2000 * (g - 1)`.
  From the first three: `Kept` holds of "left of by `g`", of "above by `g`", of "a fixed step
  from", and of a conjunction of kept relations. It does not hold of a disjunction: a pair
  that is side by side before and one above the other after can meet. `unsure` lists those
  pairs. Two controls go with the laws: a `shift` on `Easing.backOut` loses a gap, and two
  kept things with two delays lose one.
- **The seam.** The consumer's places are `Int`, and its `lerp` is `mix`. It converts nothing.
  Its `place_apart` gives the premise at each picture, as a disjunction of four, and its
  `sampleLaid` moves every kept thing by one `moved`. So it can state, for every moment of a
  step, what `Laid.boxesApart` tests on one layout. At the default look the premise of
  `grow_clear` holds in a flow: the widest box of a flow is 240 pixels, the gap is 16, the
  spring passes its end by 45 per mille, and `480 * 45 = 21600 ≤ 2000 * 15`. A box of the
  graph layout has no greatest width, so there the premise is a test on each pair.
- **A probe.** Take a program's graph before and after an edit that puts a node into the middle
  of a rank, so that its neighbours move apart. Write three animations of the step: one timing
  for all kept boxes; the kept boxes staggered from left to right; one timing with `backOut`
  on the shift. Print on each frame the least gap between two boxes of one rank. Look at that
  number: in the first it never falls below the lesser of the two pictures' gaps, and in the
  other two it does.
- **Effort and value.** Small, large. It depends on `Scene/Motion.lean` and on
  `Scene/Motion/Laws.lean`, which has `mix_start`, `mix_end` and `mix_self` and none of the
  laws above. The motion probe's note names a law `mix_shift` for a node and its edge under
  one transition; the seat did not find it in the tree. It is `mix_add` here.

### M2. `Morph`: an edge between two pictures

- **Name and one line.** The caller gets a change of shape for every two lines, with no jump,
  and the laws of the shape between: an edge stays on its two boxes while they move.
- **What it draws from.** Animation: follow-through, the shared element, the container that
  changes shape.
- **API sketch.** This module sharpens what landed during this seat's work. The tree has the
  pose (`Pose.shape`), the change (`Change.morph`), the mixing (`ICubic.mix`), the rounding of
  two exact lists (`Change.morphOf`) and the property `d` in the writer. It has no law of the
  shape between two pictures, and two lists of different lengths jump at the middle. M2 adds
  three things. The laws are strict (`Whatwg/Svg/Scene/Morph.lean`). The alignment is exact
  geometry (`Whatwg/Svg/Geometry/Align.lean`). A second writer is in
  `Whatwg/Html/Node/SvgMotion.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- A morph whose two lists have one length: it has a shape at every moment. -/
def Change.Aligned : Change → Prop
  | .morph a b => a.length = b.length
  | _ => True

end Whatwg.Svg.Scene

namespace Whatwg.Svg.Value

/-- The chain as `n` segments that draw the same line: its longest segment is halved, again
and again. The chain itself when it has `n` segments or more. -/
def Cubic.refine (cs : List Cubic) (n : Nat) : List Cubic

/-- Two chains as lists of one length, each drawing what it drew. -/
def Cubic.align (a b : List Cubic) : List Cubic × List Cubic

/-- The change from the line `a` to the line `b` on the grid of `1 / s`, aligned first:
`Change.morphOf` of the two aligned lists. -/
def Cubic.morph (s : Nat) (a b : List Cubic) : Whatwg.Svg.Scene.Change

end Whatwg.Svg.Value
```

  The writer has the two poses of a morph as the property `d`, with two `path()` values of one
  command structure. `align` gives that structure for every two lines. The second writer is
  for a host that does not read `d` as a property: the path at each stop of the easing. Today
  such a host shows the shape at the end throughout, by the writer's own header.
- **The semantics it must accord with.** An edge says that one thing runs before another, or
  waits for it. It joins two boxes. The invariant: *at every moment the edge starts on its
  source and ends on its target, and it has the form that both pictures give it.* The module
  must never show an edge that ends in the air, an edge with a part that rises between two
  pictures in which it descends, or a line that is not one line. A jump at the middle of a
  step is a change with no cause: an edge that gains one segment because a rank was added
  must still go over smoothly.
- **Laws worth proving.**
  - `refine_draws` (core, `Rat`): each segment of `refine cs n` is `c.between a b` of a segment
    `c` of `cs`, and in order the parts run through each segment from `0` to `1`. With
    `Cubic.between_pointAt`, the refined chain has the points of the chain and no others. And
    `align_aligned`: the two lists of `align` have one length, so `Cubic.morph` never jumps.
  - `mix_chained` (core, strict): where both lists are chains, the list at every moment is a
    chain.
  - `mix_descends` and `mix_upright` (core, strict, from `mix_gap`): a segment with
    `p0.y ≤ p1.y ≤ p2.y ≤ p3.y` in both pictures has it at every moment, and one with
    `p0.x = p1.x` in both has it at every moment. So "every edge descends" and "a step is
    vertical at both ends" are facts of the whole step.
  - `morph_attached` (core, strict, from `mix_add`): where the chain starts a fixed step from
    its box's place in both pictures, and the box's shift takes the morph's timing, the chain
    starts that step from the box at every moment.
  - `mixed_normSq` (core, `Rat`, by `grind`): `normSq (lerp a b t)` is
    `(1 - t)² |a|² + t² |b|² + 2 t (1 - t) (a · b)`. An outline that is morphed point by point
    is narrower between two pictures where the line turns, and this says by how much.
- **The seam.** The consumer's routes are lists of its own `Cubic`, in whole pixels. That type
  has the four fields of `ICubic`, with a pair where `ICubic` has an `IVec`. The consumer takes
  `ICubic` for its routes, or maps once. From there `Cubic.ofGrid` reads a route into the exact
  geometry, `align` works on it, and `Cubic.toGrid` reads it back: one rounding, at a stage
  boundary of the seams note's section 3.2. An organic stroke is an outline. Two ways are
  open, and the caller chooses. It can stroke the morphed centre line at each moment: the
  width is true, and the stroke cache does not help. It can morph the two outlines point by
  point: no stroke is computed, and the width is short by the factor of `mixed_normSq`.
- **A probe.** The motion probe's page `tree.html` already shows three kept edges that change
  shape and stay on their nodes, each with one count of segments in both pictures. The probe
  for M2 is the case it does not have. Take the graph of fibers of a run of a race of three,
  at the step where the winner exits. Exit edges appear, a rank is added, and a long edge
  gains a point, so its count of segments changes. Write the step as one SVG file with CSS
  tracks, as the motion probe does: animated, and as five still pictures from `Track.at`. Look
  at three things. Print the greatest distance from an edge end to its box over the stills: it
  is zero. Look at the long edge at the middle of the step: it does not jump. Look for an edge
  with a part that rises: there is none.
- **Effort and value.** Medium, large. The pose and the first writer are in the tree. What is
  left is the alignment, the laws and the second writer. Without the alignment an edge of a
  graph that gains a rank jumps; without the laws no caller can say that an edge stays on its
  boxes. It depends on M1 and on `Geometry/Grid.lean`. One host was observed to read `d` as a
  property; the others were not tested (section 8).

### M3. `Score`: order in time

- **Name and one line.** The caller gets a few operations that put tracks in order, and a law
  that the order in time follows an order of the program.
- **What it draws from.** Animation: staging, choreography and stagger, duration against
  distance, interruption, reduced motion.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Score.lean`. The writer gains one rule. The
  tree has two of the operations since this seat's first reading: `Motion.delayed m later`
  starts each track later by what `later` gives its key, and `Motion.arriveWith` gives each
  thing its own entrance. A stagger by rank is `m.delayed fun k => gap * rank k`. Neither has
  a law about order. M3 adds the predicate, its laws and the rest.

```lean
namespace Whatwg.Svg.Scene

namespace Motion

variable {κ : Type}

/-- The moment the last track ends. -/
def finish (m : Motion κ) : Nat

/-- `b`, each track started when `a` has ended, less `overlap`. -/
def andThen (a b : Motion κ) (overlap : Nat := 0) : Motion κ

/-- Every delay and duration scaled by one factor, so that the motion ends by `budget`. -/
def fit (m : Motion κ) (budget : Nat := 1000) : Motion κ

/-- A step in three parts: what leaves, then what moves, then what enters. -/
def staged (leave move enter : Motion κ) (overlap : Nat := 0) : Motion κ

/-- A track of a key ends before a track of each key that `before` puts after it starts. -/
def Respects (before : κ → κ → Prop) (m : Motion κ) : Prop :=
  ∀ a ∈ m, ∀ b ∈ m, before a.key b.key →
    a.timing.delay + a.timing.duration ≤ b.timing.delay

/-- The same step with no travel: each thing changes by its opacity alone, at the same
times. -/
def reduced (m : Motion κ) : Motion κ

/-- The motion `next`, started from the poses that `m` has at the moment `t`. -/
def retarget (m : Motion κ) (t : Nat) (next : Motion κ) : Motion κ

end Motion

/-- The first stop after which the easing stays within `slack` of its end. -/
def Easing.settledBy (e : Easing) (slack : Nat) : Nat

/-- A duration for a travel: `least` for none, more for more, never above `greatest`. -/
def Transition.forTravel (least greatest rate travel : Nat) : Nat :=
  min greatest (least + rate * Nat.sqrt travel)

end Whatwg.Svg.Scene
```

  `Motion.sheet` writes the tracks of `reduced` inside
  `@media (prefers-reduced-motion: reduce)`.
- **The semantics it must accord with.** Order in time says order in the program. The
  invariant: *a thing does not appear before what it comes from.* In a build, a child appears
  after its parent. In a graph, an edge reaches a box before the box opens. The module must
  never show an effect before its cause, a jump when a step is interrupted, or less
  information to a reader who asked for less motion.
- **Laws worth proving.** Core proves all five, under the strict rule.
  - `delayed_respects`: where `before a b` gives `rank a < rank b`, the tracks of `m` start
    together and each lasts `gap` at most, `m.delayed fun k => gap * rank k` respects `before`.
  - `fit_respects` and `fit_finish`: `fit` keeps `Respects`, and `(m.fit b).finish ≤ b`. Two
    floors of two parts are no more than the floor of their sum, so a rounding breaks no
    order. With `Track.at_done`, the last moment of a fitted step is the next picture.
  - `reduced_settles`: `reduced` keeps each track's key and timing, and a track that settles
    still settles. The reader who asked for less motion sees the same last picture and the
    same order.
  - `retarget_start`: for each key and each kind of pose, the pose of `retarget m t next` at
    its first moment is the pose of `m` at `t`. An interrupted step does not jump.
  - `settledBy_holds`: from the stop `e.settledBy slack` on, `e.at` is within `slack` of
    `1000`. So the things that enter may start before the move ends, at a moment that is
    computed: every kept thing is then within the gap of its place.
- **The seam.** The consumer passes two functions: `rank`, which is its `ranks` or a level's
  height, and its own relation of edges for `before`. Its `ranks_forward` gives the premise of
  `delayed_respects`. Times are per mille of a step, as in its `Choreography.norm`. The levels,
  the slots, `drawAt` and `expandAt` of `sampleLaid` become `delayed` and `andThen`, and
  `enterFrom` becomes `settledBy` of the move's easing. One duration for the kept things, from
  the step's longest travel (`forTravel`), keeps M1's premise.
- **A probe.** The motion probe's two pages already start new things level by level, with
  `delayed`. The probe for M3 is the law and the two forms those pages do not have. Take the
  build of a corpus program at the fill that puts a fork of three branches: a bar, three edges
  and three boxes enter. Write the step twice: delayed by rank, and delayed by the order of
  the keys. Look at each box and its edge: in the first the edge reaches the box before the
  box opens, and `Respects` is closed by evaluation; in the second some box opens over an
  edge that is not there yet. Then turn on reduced motion in the browser and look at the same
  file: nothing travels, and the same things appear in the same order. Then send a second
  edit at the middle of the step, with `retarget`: no box jumps.
- **Effort and value.** Small, large. It replaces arithmetic that the consumer wrote by hand
  and holds by no law. It depends on `Scene/Motion.lean`.

### M4. `Branch`: widths that conserve

- **Name and one line.** The caller gets the width of each branch of a fork, with a law that
  the branches together carry what the trunk carries, at every depth.
- **What it draws from.** The organic school: Leonardo's rule and Murray's law. Tufte: the lie
  factor and the smallest effective difference.
- **API sketch.** Strict layer, in `Nat`: `Whatwg/Svg/Scene/Branch.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- The greatest `r` with `r ^ k ≤ n`, for `k > 0`. -/
def rootDown (k n : Nat) : Nat

/-- A share of the work: `num` parts of `den`. A share of a share multiplies both, exactly. -/
structure Share where
  num : Nat
  den : Nat

/-- The shares of the branches of a line with the share `s`, the branches carrying
`weights`. -/
def Share.split (s : Share) (weights : List Nat) : List Share :=
  weights.map fun w => ⟨s.num * w, s.den * weights.sum⟩

/-- The width of a line with the share `s`, where the trunk is `trunk` wide and the `k`-th
powers of widths add. `k = 1`: widths add, as in a flow diagram. `k = 2`: Leonardo's rule.
`k = 3`: Murray's law. One rounding, down. -/
def Share.width (k trunk : Nat) (s : Share) : Nat := rootDown k (trunk ^ k * s.num / s.den)

/-- The greatest wobble, per mille of a width, at which a line `narrow` wide is narrower than
a line `wide` wide at every point. -/
def Branch.wobbleRoom (narrow wide : Nat) : Nat := 1000 * (wide - narrow) / (wide + narrow)

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A width means a share of the work. The invariant:
  *at every fork the `k`-th powers of the branches' widths sum to the trunk's, and a wider
  line never carries less.* The module must never show a branch that looks as wide as its
  trunk, a line whose width depends on how deep it is nested, or two shares at one width with
  no report. Three things are the owner's to rule, and the module takes each as a parameter:
  - the exponent. At `k = 2` the branches of a fork of two are 41 per cent wider together than
    their trunk. A reader who reads width as quantity over-reads them. The legend must say
    that areas add, or `k` is 1;
  - the weights. The consumer gives each branch an equal share. A branch of ten nodes and a
    branch of one could have ten parts and one;
  - the least width. The consumer never draws a line finer than `fine`. Below it, different
    shares are drawn alike, and M8's `ties` lists them.
- **Laws worth proving.** Core proves all, in `Nat`, under the strict rule.
  - `rootDown_pow_le` and `lt_rootDown_succ_pow`: `(rootDown k n) ^ k ≤ n < (rootDown k n + 1) ^ k`.
  - `width_conserves`: for the widths `cᵢ` of the shares of `s.split weights`, with `q` the
    exact quantity `trunk ^ k * s.num / s.den`: `Σ cᵢ ^ k ≤ q < Σ (cᵢ + 1) ^ k`. The consumer
    checks this at six counts. The port of its stroke in this repository's tests proves it
    for every count of equal parts at `k = 2`, by the seat's note to the consumer. This is the
    same law in the library, for every exponent and for unequal weights.
  - `split_exact`: a split of a split has the products of the parts, with no rounding. So a
    width is rounded once, at any depth. The consumer multiplies rounded shares
    (`Box.reshare`), and its error grows with depth.
  - `width_mono`: a greater share is never drawn narrower.
  - `wobbleRoom_apart`: `amp ≤ wobbleRoom n w → n * (1000 + amp) ≤ w * (1000 - amp)`. With
    `Stroke.organic_band`, two lines whose wobble is within that room cannot be taken for each
    other at any point. For a trunk and a branch of a fork of two at `k = 2` the room is 171
    per mille. The default look has 350.
- **The seam.** The consumer's `Edge.share` is a count of millionths. It becomes a `Share`, two
  counts, or stays a count through `⟨share, 1000000⟩`. Its `Grow.split n` is
  `Share.width 2 1000000 ⟨1, n⟩`, number for number, so its pictures do not change at one
  level of forks. They change by a rounding where forks nest. The module is in `Nat`, so
  `Flow.lean` uses it under its own axiom rule. The motion probe's tree already draws an edge
  at the root of its share of the leaves (`edgeWidth` of `workshop/TreeProbe.lean`), in `Rat`
  with a least width: that is `Share.width 2` with the leaves as weights, and M4 is its
  library form with the laws.
- **A probe.** Take a program with a fork of two inside a fork of three, drawn with organic
  strokes. Draw it four times as small panels: `k` at 1 and at 2, the wobble at 350 and at
  150. Look at the trunk against a branch near the fork: at 350 a branch is in places wider
  than its trunk; at 150 it never is. Look at the six innermost lines: their widths are one
  number in every panel, whatever the nesting.
- **Effort and value.** Small, large: this is the owner's first example of a meaning. It
  depends on nothing. It sharpens item 8 of the seams note, which plans the `k`-th root in
  `Rat`: the root is wanted on `Nat` first, in the strict layer, and the `Rat` form follows
  from it, as `sqrtDown` follows from `Nat.sqrt`.

### M5. `Colour`: kinds and quantities that can be told apart

- **Name and one line.** The caller gets tests on colours that Lean decides: this ink is
  legible on this ground, these kinds differ for every kind of vision, this ramp is in order.
- **What it draws from.** Science: perceptually uniform colour, colour-vision deficiency,
  contrast. Tufte: layering, colour as quantity and as label.
- **API sketch.** Strict layer, in whole numbers: `Whatwg/Svg/Scene/Colour.lean`. The meaning
  over the real numbers is `analysis/WhatwgAnalysis/Colour.lean`. The record `Rgb` is in
  `Whatwg/Html/Node/SvgPaint.lean` today, which is not strict; it moves down, and `SvgPaint`
  keeps its reader and its writer. No second type of colour is made.

```lean
namespace Whatwg.Svg.Scene

namespace Colour

/-- The linear light of a byte of sRGB, in millionths, rounded down: a table of 256. -/
def linear (b : UInt8) : Nat

/-- The relative luminance of a colour, in millionths. -/
def luminance (c : Rgb) : Nat

/-- The contrast of the two colours, as WCAG 2 defines it, is `num / den` at least. The test
rounds against itself: the lighter down, the darker up. -/
def contrastAtLeast (num den : Nat) (a b : Rgb) : Bool

/-- The colour that a paint at `value` per mille shows over a ground: what `fill-opacity`
draws. -/
def over (value : Nat) (paint ground : Rgb) : Rgb

/-- The colour in OKLab, in millionths. -/
structure Lab where
  l : Int
  a : Int
  b : Int

def oklab (c : Rgb) : Lab

/-- The square of the distance of two colours in OKLab. -/
def distSq (a b : Rgb) : Nat

/-- A kind of vision: all three cones, or one missing. -/
inductive Vision where
  | full | protan | deutan | tritan

/-- The colour as a reader with that vision sees it, by a stated model. -/
def seen (v : Vision) (c : Rgb) : Rgb

/-- Every two of the colours are `d` apart at least, for every kind of vision. -/
def distinct (d : Nat) (cs : List Rgb) : Bool

/-- `n` colours from the ground to the ink, at even steps of lightness. -/
def ramp (ground ink : Rgb) (n : Nat) : List Rgb

end Colour

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A colour says a kind: the host, a failure, a
  resource. A tone says a quantity: depth, or a band behind a lit row. The invariant: *two
  kinds are never drawn in colours that a reader cannot tell apart, a text is never drawn in
  an ink that cannot be read on its ground, and more of a quantity is never lighter.* Hue is
  for kinds, at one lightness. Lightness is for quantities. A palette whose kinds differ in
  lightness says a quantity that the data does not have.
- **Laws worth proving.**
  - `linear_brackets` (core, by evaluation): each entry `e` of the table is the floor of the
    exact value. Above the linear part that is
    `(e / 10⁶) ^ 5 ≤ ((b / 255 + 0.055) / 1.055) ^ 12 < ((e + 1) / 10⁶) ^ 5`, an inequality of
    whole numbers. The exponent 2.4 is twelve fifths, so no real power is computed.
  - `linear_real` (Mathlib certifies): each entry is within one millionth below the transfer
    function of sRGB at its byte. It needs one lemma, that `x ^ 5 ≤ y ^ 12` gives
    `x ≤ y ^ (12 / 5)` for numbers that are not negative.
  - `contrast_real` (Mathlib certifies): `contrastAtLeast n d a b = true` gives
    `n / d ≤ (L₁ + 0.05) / (L₂ + 0.05)` for the real luminances, `L₁` the greater.
  - `over_luminance_mono` (core): for a paint that is lighter than its ground in each channel,
    the luminance of `over value paint ground` does not fall as `value` rises. So a tone by
    opacity is in order.
  - `ramp_ordered` (core): the lightness of `ramp ground ink n` rises or falls strictly along
    the list, and its ends are the ground and the ink.
  One small fact is worth a line of evaluation: WCAG 2 writes the end of the linear part as
  0.03928, and sRGB as 0.04045. No byte falls between them, so the table is the same for both.
- **The seam.** The consumer's `Rgb` is a number `0xRRGGBB`; `Rgb.ofNat` reads it. A look can
  carry its own proof, in a strict module:
  `Colour.contrastAtLeast 9 2 ink ground = true`, closed by evaluation. That replaces the
  palette validator that the consumer runs outside Lean. Where the kernel is too slow for it
  (section 8), the same test runs where a look file is read, and refuses the file.
- **A probe.** Take the three looks of the consumer. Draw a matrix of six roles by six roles,
  each cell one role's colour on another's, with the contrast written in the cell. Draw it four
  times as small panels, one for each kind of vision. Look for a cell below its ratio, and at
  the failure red against the resource green in the deutan panel. Then take a run in which a
  fiber fails, with the hue on, and write its animation twice: as it is, and as `seen .deutan`
  draws it. Look at the failed node as it enters: it must differ from a resource in both.
- **Effort and value.** Medium, large: every picture and every look. It depends on a whole
  cube root (`rootDown 3` of M4) and on constants that need a sealed source: the two matrices
  of OKLab and the matrices of the vision model. APCA is left out. It is a draft, its
  constants have changed, and its exponents are not ratios of small numbers. It can come as
  data when a version is sealed.

### M6. `Metrics`: what a host says of a face

- **Name and one line.** The caller gets the width of a text as a least and a greatest value,
  from numbers that the host supplied once.
- **What it draws from.** Typography: the baseline grid, tabular figures, kerning, and the
  line between what a layout decides and what it is given.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Metrics.lean`. It reads code points and no
  string: the consumer found that `String.length` of core reaches `Classical.choice` at this
  toolchain.

```lean
namespace Whatwg.Svg.Scene

/-- What a host says of a face at one size. Every length is in thousandths of the picture's
unit. -/
structure Metrics where
  ascent : Nat
  descent : Nat
  capHeight : Nat
  xHeight : Nat
  /-- ranges of code points: first, last, and the least and the greatest advance of a
  character of the range, with whatever kerning and joining the host does -/
  ranges : List (Nat × Nat × Nat × Nat)
  /-- the least and the greatest advance of a character in no range -/
  other : Nat × Nat
  /-- every digit has one advance -/
  tabular : Bool

namespace Metrics

/-- A face in which every character has the advance `cell`: the data face. -/
def mono (cell ascent descent : Nat) : Metrics

/-- The least and the greatest width of a run of characters. -/
def width (m : Metrics) (codes : List Nat) : Nat × Nat

/-- The run fits the room, whatever the host draws within the metrics. -/
def Fits (m : Metrics) (codes : List Nat) (room : Nat) : Prop := (m.width codes).2 ≤ room

/-- A row holds the face: its ascent above the baseline, its descent below. -/
def FitsRow (m : Metrics) (base rowHeight : Nat) : Prop :=
  m.ascent ≤ base ∧ m.descent ≤ rowHeight - base

/-- The metrics of several faces as one: the bounds of each are within its bounds. -/
def any (ms : List Metrics) : Metrics

end Metrics

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A box's width says the length of its text, and a
  text's room says where it ends. The invariant: *a text that Lean says fits does fit, for
  every host that the metrics describe.* The width is an interval and not a number, because
  Lean does not know the kerning. The module must never give a width that it does not have: a
  proportional text measured in cells is such a width.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `width_append`: the bounds of two runs in a row are the sums of their bounds. A room is
    computed part by part.
  - `mono_width`: for `Metrics.mono cell`, both bounds are `cell` times the count. The data
    face needs no host, and the consumer's grid is this instance.
  - `fits_any`: `Fits (Metrics.any ms) codes room` gives `Fits m codes room` for each `m` of
    `ms`. A room computed for a list of fallback families holds for the one the host picks.
  - `tabular_aligns`: with `tabular`, two runs of digits of one count have one width, the
    least equal to the greatest. Counts and addresses align on the right.
- **The seam.** The numbers cross once, from the host to Lean. They are a fact of a look's
  faces, so they belong in the look: an extension of its token file, written once by a tool of
  the host that asks pango for the advances. The consumer supplies data and converts nothing.
  Toward a browser, where the font is not known, the kit's typed `textLength` can state the
  width that the layout assumed. The browser then spaces the text to that width, so a box is
  never overrun, at the cost of spacing that is off by the error of the estimate. Requests to
  the host go the other way, as data beside the face: tabular figures, small capitals, no
  joined letters in the data face.
- **A probe.** Take one page of a build, with its notes in the label face. Draw each note twice
  over itself: a box at the least width and a box at the greatest, under the text that the
  host drew. Look at each text's end: it lies between the two box ends. Then swap the look's
  first family for its second and look again.
- **Effort and value.** Small for Lean, large: M7 and M11 cannot start without it, and the
  consumer's `lineCells` is wrong without it. `Metrics.mono` needs no host and can land first.
  The tool that measures is the consumer's, on its C side.

### M7. `Label`: a label in a room

- **Name and one line.** The caller gets a label fitted to a room: whole, or broken at a
  permitted place, or cut with a mark, in an order of forms that never shows more in less
  room.
- **What it draws from.** Typography: measure, widows, breaking without Knuth and Plass,
  truncation. Tufte: micro and macro readings.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Label.lean`. The fitting reads no character:
  a piece carries its two widths, which the caller takes from M6.

```lean
namespace Whatwg.Svg.Scene

/-- A piece of a label that is never broken: a name, a number, a mark of punctuation. -/
structure Piece (π : Type) where
  id : π
  /-- its least and its greatest width -/
  least : Nat
  greatest : Nat
  /-- how much the piece matters: the piece that names the thing has the most -/
  keep : Nat
  /-- a line may end after this piece -/
  breakAfter : Bool

/-- How a label is shown. Each form says less than the one before it. -/
inductive Shown (π : Type) where
  /-- every piece, on these lines -/
  | whole (lines : List (List π))
  /-- some pieces, with a mark where others were left out -/
  | cut (lines : List (List (Option π)))
  /-- a sign of one or two characters: the thing is there, and its name is not shown -/
  | sign
  /-- nothing -/
  | none

/-- The label in a room of `room` by `rows` lines. `mark` is the width of the mark of a cut. -/
def Label.fit {π : Type} (room rows mark : Nat) (label : List (Piece π)) : Shown π

/-- The labels of one picture, fitted together. -/
def Label.fitAll {π : Type} [DecidableEq π] (room rows mark : Nat)
    (labels : List (List (Piece π))) : List (Shown π)

end Whatwg.Svg.Scene
```

  The breaking is a total fit with the widest line as its cost, over three lines at most. The
  cutting leaves out the piece of least `keep` first, the later one on a tie.
- **The semantics it must accord with.** A label names a thing. The invariant: *a label with
  no mark of a cut is the whole label; a name is shown whole or not at all; and two labels
  that differ are not shown as one text.* The module must never show a name with a break or a
  hyphen inside it, a cut text that reads as a whole one, or two different nodes with one
  label.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `fit_fits`: each line of the result is within the room at its greatest width, and there
    are `rows` lines at most.
  - `fit_whole`: a `whole` result holds every piece of the label, in order. A label that fits
    on one line is shown `whole` on one line.
  - `fit_subsequence`: the pieces of a `cut` result are pieces of the label, in its order, and
    a mark stands at each place where pieces were left out.
  - `fit_mono`: with more room, the result shows every piece that it showed with less. So a
    picture drawn larger never says less.
  - `fitAll_distinct`: two labels that differ, both shown as text, are shown as two texts.
- **The seam.** The consumer makes the pieces from its own structure, and not from a lexer: the
  name of a constructor has the most `keep`, a prefix of a module less, an argument of a type
  the least. Its widths in the data face are counts of cells times eight, with the least equal
  to the greatest. It gets back identities of pieces and writes their texts itself, so the kit
  never holds a text. Its writer of SVG today cuts a text at its end and adds an ellipsis
  (`Dev.svg`), and two long names with one prefix are then one text.
- **A probe.** Take the graph of a program whose nodes have long names with one prefix, such
  as operations of one module. Draw it at four widths of a box: thirty cells, twenty, twelve
  and six. Look at each box: no two boxes have one text, the last name stays when the prefix
  goes, and at six cells the sign stands with the pointer box still answering the key. Then
  write the four as frames of one animation, with the join by key, and look for a label that
  shows less in a wider box: there is none.
- **Effort and value.** Medium, large: every node of every picture has a label. It depends on
  M6 for widths, and on nothing for the data face.

### M8. `Scale`: a quantity as a length, and what the picture says

- **Name and one line.** The caller gets a scale as data, with its laws, and a table of what
  each channel of the picture means, from which a legend is drawn.
- **What it draws from.** Science: honest scales, bands, stated rounding. Tufte: data-ink, the
  lie factor, the smallest effective difference.
- **API sketch.** Strict layer, in `Int`: `Whatwg/Svg/Scene/Scale.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- How a quantity becomes a length. A value outside the range of the data is drawn at the
nearer end. -/
inductive Scale where
  /-- equal steps of the quantity are equal steps of the length -/
  | linear (dataLo dataHi lo hi : Int)
  /-- the `k`-th root: the `k`-th powers of lengths are in proportion -/
  | root (k : Nat) (dataLo dataHi lo hi : Int)
  /-- one step of length for each doubling -/
  | log2 (dataLo dataHi : Nat) (lo hi : Int)
  /-- levels: a value is drawn at the level of the last threshold that it reaches -/
  | steps (thresholds levels : List Int)

/-- The length of a value. -/
def Scale.at : Scale → Int → Int

/-- The pairs of the values that the scale draws alike: an end of the range, a level, or a
rounding. -/
def Scale.ties (s : Scale) (values : List Int) : List (Int × Int)

/-- No quantity is no length. -/
def Scale.fromZero : Scale → Bool

/-- A channel of a picture. -/
inductive Channel where
  | across | down | width | height | tone | hue | dash | texture | orderInTime

/-- One line of what a picture says: a channel, what it means, and how it is drawn. -/
structure Encoding where
  channel : Channel
  meaning : String
  scale : Option Scale

/-- The marks of a legend: sample values with the lengths that the picture draws them at. -/
def Encoding.samples (e : Encoding) (values : List Int) : List (Int × Int)

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A length says a quantity. The invariant: *more is
  never drawn as less, and where two different values are drawn alike the picture says so.*
  The table of encodings is the picture's statement. A channel has one row at most, which is
  the consumer's rule that no channel holds a meaning twice. The legend's marks come from
  `Scale.at`, the function that draws the picture, so the two cannot differ. The module must
  never show a bar that does not start at nothing with no word of it, or a doubling drawn as
  a tripling.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `at_mono`: `a ≤ b → s.at a ≤ s.at b`, for every scale whose `lo` is no more than its `hi`.
  - `linear_strict`: a `linear` scale with one unit of length at least for each unit of the
    quantity gives `a < b → s.at a < s.at b` in its range. Where a scale is shorter than that,
    `ties` lists the pairs.
  - `linear_ratio`: for a `linear` scale from nothing, `s.at (n * a)` is within `n` units of
    `n * s.at a`. Twice the quantity is twice the length, to a rounding.
  - `at_between`: `a ≤ v → v ≤ b → s.at a ≤ s.at v ∧ s.at v ≤ s.at b`. A band drawn from
    `s.at a` to `s.at b` holds the mark of every value of the interval.
- **The seam.** The consumer passes whole numbers: a share in millionths, a depth, a count, a
  step. It gets whole numbers in its own unit. Its edge width is `max fine (trunk * share)`,
  which is a `linear` scale drawn at the nearer end below `fine`; `ties` says which shares
  that end hides. Depth as weight and as tone, which its visual language note proposes, is
  `steps`, and `at_mono` is that note's law "a deeper item is never heavier". A row of the
  table can be written into the picture as a data attribute, so a file says what it claims.
- **A probe.** Take a program with regions nested four deep. Draw it with weight by depth on a
  `steps` scale of three levels, and put the legend beside it, made by `Encoding.samples`.
  Look at the fourth level: it is drawn as the third, and the legend says "3 and deeper",
  because `ties` is not empty. Then change the scale to four levels and look again.
- **Effort and value.** Small, medium. M4, M12 and the depth channel use it. It depends on
  `rootDown` of M4.

### M9. `Cross`: crossings, gaps and marks that are too near

- **Name and one line.** The caller gets the crossings of the lines of a picture as data, the
  line that passes under with a gap at each, and the pairs of marks that are too near.
- **What it draws from.** Tufte: 1 + 1 = 3. The organic school: the near line breaks the far
  one. Graph drawing: crossings cost a reader most.
- **API sketch.** The test is strict and reads whole points
  (`Whatwg/Svg/Scene/Cross.lean`). The cut is exact geometry
  (`Whatwg/Svg/Geometry/Gap.lean`). One law is in `analysis/`.

```lean
namespace Whatwg.Svg.Scene

/-- The two straight segments meet at one point that is inside both: by the signs of four
cross products. -/
def IVec.crosses (a b c d : IVec) : Bool

/-- A crossing of two lines: their keys, and which piece of each. -/
structure Crossing (κ : Type) where
  over : κ
  under : κ
  overAt : Nat
  underAt : Nat

/-- The crossings of the lines, each a row of points. `above` says which of two lines is
drawn over the other. -/
def crossings {κ : Type} (above : κ → κ → Bool) (lines : List (κ × List IVec)) :
    List (Crossing κ)

/-- The pairs of marks nearer than `d` that do not meet. -/
def tooNear {κ : Type} (d : Int) (marks : List (κ × IBox)) : List (κ × κ)

end Whatwg.Svg.Scene

namespace Whatwg.Svg.Value

/-- The chain with a gap about each of the places given: a segment's number and two
parameters. What is left of the line that passes under. -/
def Cubic.gapped (cs : List Cubic) (gaps : List (Nat × Rat × Rat)) : List (List Cubic)

end Whatwg.Svg.Value
```

- **The semantics it must accord with.** Two lines that cross have nothing to do with each
  other there. Two lines that join do. The invariant: *a gap stands at a crossing and nowhere
  else, and which line is over follows one order of the data.* The order is depth, by the
  consumer's note: a deeper line is never in front of a shallower one. The count of crossings
  is then a fact of a layout, which two layouts can be compared by.
  The known shortcut fails here. Mapmakers draw a wide stroke in the ground's colour under each
  line, and need no test. That stroke also cuts the frames it passes and the lines that leave
  one port together, so lines that join look as if one passed under the other. So the
  crossings are computed, and a gap is cut only there.
- **Laws worth proving.**
  - `crosses_iff` (core, `Rat`): `crosses a b c d = true` exactly when a point is on both
    segments at parameters strictly between `0` and `1`, for segments not on one line.
  - `crossings_move` (core, strict): the crossings of moved lines are the crossings. So they
    are stored with a retained picture.
  - `gapped_parts` (core, `Rat`): the pieces of `gapped` are `between` parts of the chain's
    segments, in order, and what lies between two pieces is one of the gaps asked for.
  - `bump_crosses` (core for the sign, Mathlib for the real parameter): two `bumpY` links
    between the same two heights meet at a parameter strictly inside exactly when their ends
    stand in opposite orders. Both links have one ordinate at each parameter, and the
    difference of their abscissae runs from one difference of ends to the other. So for a
    layered graph the drawn crossings are the inversions of the order, and a law about the
    order (item 10 of the seams note) is a law about the picture.
- **The seam.** The consumer passes its routes as rows of whole points, after it has flattened
  them, and a function for `above` from its depth. Detection needs no rational number, so it
  can stand in a strict module. The cut is in `Rat` and is rounded once.
- **A probe.** Take the graph of fibers of a run in which three fibers wait on one another's
  exits, so that back edges cross forward ones. Draw it twice: with no gaps, and with gaps
  from `crossings` and depth. Print the count of crossings on each. Look at the port where
  three edges leave one box: no gap is there. Look at a crossing: the line that passes under
  is whole on both sides of a gap of a pixel or two. Then animate one step with M2 and look at
  whether a gap opens and closes only where two lines pass.
- **Effort and value.** Medium, medium. The consumer's flows are series-parallel and cross
  only through waits and back edges; its graphs of fibers cross more. It depends on the
  flattening of item 6 of the seams note.

### M10. `Dash` and `Texture`: styles of state

- **Name and one line.** The caller gets dashes that end on a dash, hatching with a stated
  share of ink, and dots that stay with their object, each as plain segments and points.
- **What it draws from.** The organic school: stipple and hatch for tone, ink on paper. Tufte:
  showing uncertainty. Science: a second code for a reader without colour.
- **API sketch.** Exact geometry: `Whatwg/Svg/Geometry/Dash.lean` and `Texture.lean`.

```lean
namespace Whatwg.Svg.Value

/-- The chain cut into dashes: the pieces drawn, in order. The dash and the gap are scaled by
one factor so that the chain starts with a whole dash and ends with one. -/
def Cubic.dashes (cs : List Cubic) (dash gap : Rat) (n : Nat := 8) (places : Nat := 3) :
    List (List Cubic)

/-- The direction of the lines of a hatching. -/
inductive Slope where
  | level | upright | rising | falling

/-- Straight lines `pitch` apart, cut to a box: the middle line of each. -/
def Hatch.lines (b : Box) (pitch : Rat) (slope : Slope) : List Cubic

/-- The pitch at which lines `weight` wide cover `tone` per mille of an area. -/
def Hatch.pitchFor (weight : Rat) (tone : Nat) : Rat := weight * 1000 / tone

/-- Dots in a box: one in each cell of a lattice that starts at the box's least corner, moved
inside its cell by the noise of a seed. -/
def Stipple.dots (seed : Nat) (b : Box) (pitch : Rat) : List Vec

end Whatwg.Svg.Value
```

- **The semantics it must accord with.** A style of a line or of a fill says a state of
  knowledge: resolved, not resolved, not yet built, not reached, refused. The invariant: *known,
  unknown and absent are drawn in three ways, in one ink.* A second invariant is of the dash
  itself: *a dashed edge still touches both its boxes.* A dash pattern that ends in a gap
  shows a line that stops short. A tone drawn as hatching says a share, and the share of ink
  is that share. The module must never show a texture that moves inside its object from frame
  to frame: that is a change with no cause.
- **Laws worth proving.** Core proves all, in `Rat`.
  - `dashes_ends`: the first dash starts where the chain starts, and the last ends where it
    ends.
  - `dashes_parts`: each dash is a run of `between` parts of the chain, in order, and no two
    dashes share a part.
  - `hatch_inside` and `hatch_cover`: each line of a hatching is in its box. For level lines of
    weight `w` at pitch `p` in a box `h` high, the share of ink differs from `w / p` by `w / h`
    at most: one line.
  - `stipple_grows`: a box grown at its far sides keeps every dot that it had. With
    `Commutes`, a moved box has the moved dots. So dots do not move inside an object when it
    moves or widens.
- **The seam.** The consumer gets segments and points, which its three outputs draw already as
  curves and shapes. Nothing is added to the row stream or to the C painter. SVG has
  `stroke-dasharray`, and the kit writes it, but it does not fit a pattern to a line's ends,
  and it does nothing for a filled outline. The consumer's first use is its own data:
  `Flow.unresolvedWaits`, a hole of a program under construction, a part that cannot end. A
  map from its states to styles is a row of M8's table, with no two states at one style.
- **A probe.** Take a program in which an await names a fiber that was passed in, so the wait
  is not resolved, beside one that is. Draw the first wait dashed, to a small open ring where
  the target is not known, and the second solid. Look at both ends of the dashed line: a dash
  touches each. Then build the program step by step, with its holes stippled, and animate the
  steps. Look at a hole while its box moves and widens: its dots stay where they were on it.
- **Effort and value.** Medium, medium. Not resolved, not built and not reached are central to
  the consumer's semantics, and today they are text or nothing. It depends on `Stroke.samples`
  for lengths along a line, and on `Noise`.

### M11. `Place`: labels beside marks

- **Name and one line.** The caller gets a place for each label, at one of the places offered
  for it, on no mark and on no other label; or the answer that it has none.
- **What it draws from.** Typography: label placement. Tufte: annotation beside the mark.
- **API sketch.** Strict layer, in whole units: `Whatwg/Svg/Scene/Place.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- A label to place: its key, its size, the point it belongs to, and the places it may take
as steps from that point, the best first. -/
structure Wanted (κ : Type) where
  key : κ
  size : IVec
  anchor : IVec
  offers : List IVec

/-- Where the labels stand. They are placed in the order given, each at its first offer that
is free. A later label never moves an earlier one. -/
def place {κ : Type} (fixed : List IBox) (wanted : List (Wanted κ)) : List (κ × Option IBox)

/-- Eight places around a point, a gap away. -/
def Offers.around (size : IVec) (gap : Int) : List IVec

/-- Places beside a run of points, level, by the longest straight part first. -/
def Offers.along (run : List IVec) (size : IVec) (gap : Int) : List IVec

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A label says something of the mark beside it. The
  invariant: *each placed label is within a stated step of its own mark and covers nothing.* A
  label that has no free place is not drawn over something; it is reported, and the host can
  show it on demand. The module must never show a label nearer to another mark than to its
  own by an overlap, and never move a label because a label of less weight came.
  Two known methods fail here. The best placement is a hard search. A placement by forces
  gives a different answer for a small change, so labels move between frames for no cause.
  This module is greedy, in a fixed order, and it claims no best.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `place_apart`: the placed boxes are pairwise `Disjoint`, and each is `Disjoint` from every
    fixed box.
  - `place_at_offer`: a placed box stands at its anchor plus one of its offers.
  - `place_prefix`: the places of `wanted ++ [w]` are the places of `wanted`, and one more. A
    new label of less weight moves no label.
  - `place_first`: a label whose first offer is free stands there.
  - `place_move`: everything moved by one step gives the places, moved (`Commutes`).
- **The seam.** The consumer passes boxes of whole pixels and a size for each label, from M6
  and M7. The order of the list is its own: by address, so an edit deep in a program changes
  only the labels after it. It gets boxes back. A label that changes its offer between two
  frames is a kept thing of the join, and takes a `shift`.
- **A probe.** Take a flow with a fork whose branches wait on one another, and label each wait
  edge with the fork it waits for. Draw it, and print the count of labels with no place. Look
  at each label: it is level, beside a straight part of its own edge, on nothing. Then apply an
  edit that adds a node below, and animate the step. Look at the labels above the edit: none
  moves.
- **Effort and value.** Medium, medium. It depends on M6 and M7 for sizes, and on `IBox`.

### M12. `Strip`: a sequence in the room of a word

- **Name and one line.** The caller gets a sequence as a row of cells or as a small line, with
  the law that left means earlier and that each step is drawn once.
- **What it draws from.** Tufte: sparklines, micro and macro readings.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Strip.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- A sequence of quantities as points, one column for each. -/
def Strip.line (scale : Scale) (column : Int) (values : List Int) : List IVec

/-- A sequence of states as boxes: each run of one state is one box, as wide as its count of
steps. -/
def Strip.runs {σ : Type} [BEq σ] (column height : Int) (states : List σ) : List (σ × IBox)

/-- Lanes: a row for each key and a column for each step. A key with no state at a step has no
box there. -/
def Strip.lanes {κ σ : Type} [BEq σ] (cell : IVec) (rows : List (κ × List (Option σ))) :
    List (κ × σ × IBox)

/-- The columns of the least value, the greatest and the last: the three marks of a small
line. -/
def Strip.marks (values : List Int) : Option (Nat × Nat × Nat)

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** Across means the order of steps. A column is one step
  of control, and not a length of time. The invariant: *left of means before, every step is in
  exactly one box of its lane, and a box is as wide as its count of steps.* A run that
  advances a clock has two axes, steps and milliseconds; a strip takes one and names it, and
  a break in an axis is drawn as a break. A key that is not yet forked, or has exited, has no
  box: absent is not a state.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `line_across`: the point of the `i`-th value is at `i * column`. With `Scale.at_mono`, a
    greater value is never lower, and equal values are level.
  - `runs_tile`: the boxes of `runs` stand in order, each starts where the one before ends, and
    together they run from `0` to the count of steps times `column`. This is the first
    instance of the interval law that item 10 of the seams note plans.
  - `runs_width`: the width of a box is `column` times the length of its run.
  - `lanes_absent`: a key with `none` at a step has no box whose columns hold that step.
- **The seam.** The consumer passes a list for each fiber: its state at each step, from
  `Run.states`, or nothing. The states are its own type; it supplies an equality test. It gets
  boxes in whole pixels, and draws each with the tone or the texture that M8's table gives the
  state.
- **A probe.** Take the run of a race of three. Draw four lanes, one for each fiber, a column
  for each step, under the graph of fibers. Look at the whole: the two losers' lanes end one
  step after the winner's exit, so the race is a shape. Look at one cell: its state is the
  state on that fiber's box at that step. Then animate the run: at each step one column
  enters at the right, and no earlier box changes.
- **Effort and value.** Small, medium. It depends on M8 and on `IBox`.

### M13. `Multiples`: panels at one scale

- **Name and one line.** The caller gets the frames of a sequence as panels of one size at one
  scale, with each thing at the same place in every panel that holds it unmoved.
- **What it draws from.** Tufte: small multiples. Animation: staging, and the still form of a
  motion.
- **API sketch.** Strict layer, `Whatwg/Svg/Scene/Multiples.lean`.

```lean
namespace Whatwg.Svg.Scene

/-- Panels of one size, in rows of `columns`. -/
structure Multiples where
  columns : Nat
  panel : IVec
  gap : IVec

/-- The panels for some frames: each as large as the box that holds every frame. -/
def Multiples.of (columns : Nat) (gap : IVec) (frames : List IBox) : Multiples

/-- The corner of the `i`-th panel. -/
def Multiples.origin (m : Multiples) (i : Nat) : IVec

/-- Every frame in its panel: moved, and never scaled. -/
def Multiples.lay {α : Type} [Moves IVec α] (m : Multiples) (frames : List (List α)) :
    List (List α)

/-- For each frame after the first, the keys that entered or changed since the frame before,
by the join. -/
def Multiples.changed {α κ : Type} [BEq κ] (key : α → κ) (same : α → α → Bool)
    (frames : List (List α)) : List (List κ)

end Whatwg.Svg.Scene
```

- **The semantics it must accord with.** A place in a panel means what it means in every
  panel, and a size means what it means in every panel. The invariant: *one scale for all
  panels, and a thing that did not move is at one place in each.* The order of the panels,
  along each row and then down, is the order of the steps. The module must never scale a
  panel to fit its own content: two panels would then show one size as two.
- **Laws worth proving.** Core proves all, under the strict rule.
  - `origin_apart`: the boxes of two different panels are `Disjoint`.
  - `lay_place`: a thing of the `i`-th frame is drawn at itself moved by `m.origin i`. So the
    step between one key's two drawings in two panels is the step between the panels plus
    the key's own move.
  - `lay_holds`: each frame's box, moved, is inside its panel.
  - `changed_join`: a key of `changed` is in the `enter` of the join of the two frames, or in
    its `update` with a difference.
- **The seam.** The consumer's `Keyed Call` moves by whole pixels, with the two laws that
  `Moves` asks for (`Call.move_move`, `Call.move_zero`), so it gives an instance and converts
  nothing. It draws the keys of `changed` in full ink and the rest at a lower tone of M5. At a
  small scale the labels come from M7's order of forms.
- **A probe.** Take the build of a corpus program of twelve fills. Draw it as four panels by
  three, with what changed in ink and the rest faint. Look across a row at one node that no
  fill touches: it is at one place in each panel. Look at the whole: the place of each edit
  walks through the program. This picture is also what a reader gets who asked for no motion,
  and what a printed page gets.
- **Effort and value.** Small, medium. It depends on `IBox`, `Join` and, for small panels,
  M7.

### M14. `TextOrder`: text that cannot reorder its line

- **Name and one line.** The caller gets a text of a program that is safe to put in a line: it
  holds no hidden character that changes the direction of what stands beside it.
- **What it draws from.** Typography: bidirectional text. Science: no relation that the data
  does not have.
- **API sketch.** Writer layer, with strings: `Whatwg/Html/Node/SvgText.lean`.

```lean
namespace Whatwg.Html

/-- One of the twelve characters that change the direction of text and are not seen: U+061C,
U+200E, U+200F, U+202A to U+202E, U+2066 to U+2069. -/
def Text.isDirectionControl (c : Char) : Bool

/-- The text with each such character written as its code in visible characters. -/
def Text.visible (s : String) : String

/-- The visible text between a first strong isolate and its end. -/
def Text.isolated (s : String) : String

/-- `unicode-bidi: isolate`, for an element that holds a text of the program. -/
def SvgAttr.isolate {t : Whatwg.Svg.Schema.Tag} : SvgAttr t

end Whatwg.Html
```

- **The semantics it must accord with.** A line of code is drawn from left to right in the
  order of its tokens. The invariant: *the order that a reader sees is the order of the
  program's text.* A string literal that holds a right-to-left override can make a host draw
  the tokens after it in another order, so that a comment reads as code. A viewer of programs
  must not show that.
- **Laws worth proving.** Core proves both.
  - `visible_clean`: no character of `Text.visible s` is a direction control. A text with none
    is returned as it is.
  - `isolated_balanced`: `Text.isolated s` holds one opening isolate, at its start, and one
    end, at its end.
  What the module does not claim: what a host draws. That an isolate keeps its content from
  the line around it is a rule of the Unicode bidirectional algorithm, and a fact of a host
  profile.
- **The seam.** The consumer passes each text that comes from a user's program through
  `Text.visible` before it writes it, in every output. Text that the consumer itself makes
  needs none of it.
- **A probe.** Take a program with a string literal that holds U+202E between two words. Draw
  its line twice: as it is, and through `Text.visible`. Look at the first in a browser: the
  characters after the literal run backwards. Look at the second: the code of the character
  stands in the literal, and the line reads in order.
- **Effort and value.** Small, medium. The input is rare, and the fault is a false picture of
  the program's text. It depends on nothing. Cutting a text inside a cluster of characters is
  a second fault of the same kind; M7 avoids it, because it never cuts inside a piece.

### M15. `Spring`: an easing from its constants

- **Name and one line.** The caller gets the stops of a damped spring from its two constants,
  with a bound on how far it passes its end and on what is left when the step ends.
- **What it draws from.** Animation: springs against curves, weight.
- **API sketch.** Exact geometry: `Whatwg/Svg/Geometry/Spring.lean`. The meaning is in
  `analysis/`.

```lean
namespace Whatwg.Svg.Value

/-- `e ^ (-x)` for `x ≥ 0`, from below and from above, `10 ^ -places` apart at most. -/
def expNegBounds (x : Rat) (places : Nat) : Rat × Rat

/-- The place at the progress `s` of a mass on a spring released at rest toward `1`. `ratio`
is the damping ratio, `1` for critical. `turns` is the natural frequency times the step. To
`places` places. -/
def Spring.at (ratio turns s : Rat) (places : Nat := 4) : Rat

/-- What is left to go at the end of the step, before the stops are scaled to end at the
whole. -/
def Spring.residue (ratio turns : Rat) (places : Nat := 4) : Rat

/-- The spring as stops of `linear()`, scaled to end at the whole. -/
def Spring.easing (ratio turns : Rat) (pieces : Nat := 20) : Whatwg.Svg.Scene.Easing

end Whatwg.Svg.Value
```

- **The semantics it must accord with.** A motion with weight says that the thing has arrived:
  it slows into its rest. The invariant: *the stops are those of the named spring to a stated
  error, the last stop is the whole, and what the scaling hides is stated.* A spring has not
  arrived when a step ends; the consumer scales its two tables so that they end at one. That
  hides the residue, which is about half of one per cent for its `settle`. The module must
  never claim an easing in range that is not: M1 reads `Easing.bounded` and `Easing.over`
  from the stops.
- **Laws worth proving.**
  - `easing_proper` (core): `Spring.easing` starts at `0` and ends at `1000`.
  - `stops_near` (Mathlib certifies): each stop is within the stated places of the closed form
    over the real numbers, scaled.
  - `critical_bounded` (Mathlib certifies): for a damping ratio of one or more the closed form
    rises from `0` toward `1` and never passes it. So `settle` is an easing for a place.
  - `under_over` (Mathlib certifies): for a damping ratio `ζ` below one, the closed form passes
    its end by `exp (-π ζ / √(1 - ζ²))` at most.
  A check by evaluation stands beside them: the consumer's two tables should be
  `Spring.easing 1 7.4` and `Spring.easing 0.7 7.5` to a unit. Those are the reference's own
  numbers. The seat worked one stop of the first by hand, the second of twenty-one, and got
  the table's 54.
- **The seam.** The result is a `Scene.Easing`, which the strict layer and the writer of CSS
  read already. A look can then name a spring by two numbers in its token file, where it
  holds a table of twenty-one today.
- **A probe.** Take one box that enters. Write its animation four times in one file: damping
  ratios of 1, 0.7, 0.5 and 0.3. Print on each the bound of `under_over` and the greatest stop.
  Look at each box against a neighbour a gap away: with M1's `grow_clear`, the first two pass
  the test and never touch; the last fails it and does touch.
- **Effort and value.** Large, small. The tables exist as data, and `Easing.over` of M1 reads
  a bound from any table. The gain is where the numbers come from. It depends on `exp`, sine
  and cosine to a stated error; item 8 of the seams note plans the last two, and this adds the
  first.

### M16. `Bag`: a set with no order

- **Name and one line.** The caller gets places for the things of a set that show no first and
  no last, and that do not depend on the order in which the things came.
- **What it draws from.** The organic school: phyllotaxis. Science: reproducibility.
- **API sketch.** Exact geometry: `Whatwg/Svg/Geometry/Bag.lean`.

```lean
namespace Whatwg.Svg.Value

/-- The place of the `i`-th seed of a sunflower head: `i` turns by a fixed exact rotation near
the golden angle, at the distance `c √i`, the root to `places` places. -/
def Bag.seed (c : Rat) (i : Nat) (places : Nat := 3) : Vec

/-- The places of a count of things with no identity: the first `n` seeds. -/
def Bag.count (c : Rat) (n : Nat) : List Vec

/-- The places of the things of a set: by the order of their keys, and not by the order they
came in. -/
def Bag.arrange {α κ : Type} [Ord κ] (key : α → κ) (c : Rat) (things : List α) : List (α × Vec)

/-- The first `n` seeds are `d` apart at least: a test, for the caller's own `n`. -/
def Bag.apart (c d : Rat) (n : Nat) : Bool

end Whatwg.Svg.Value
```

- **The semantics it must accord with.** A row says first and last. Where the data is a set,
  the permits of a semaphore, the services of a context, the entries of a map, a row shows an
  order that the data does not have. The invariant: *the picture of a set is the same for
  every order in which its things are given.* Two wishes conflict, and the module has a
  function for each. Things with no identity take the next seed, and adding one moves no
  other. Things with keys are placed by key, so the picture does not depend on arrival, and a
  new key moves the keys after it.
- **Laws worth proving.**
  - `arrange_perm` (core): two lists with distinct keys that are permutations of each other
    have one arrangement.
  - `count_prefix` (core): `Bag.count c (n + 1)` is `Bag.count c n` and one more place.
  - `seed_within` (core): the `i`-th seed is within `c` times the root of `i`, plus one unit of
    the last place, of the middle.
  - `turn_near` (Mathlib certifies, with `analysis/WhatwgAnalysis/Turn.lean`): the rotation is
    within a stated angle of the golden angle.
  No law says that seeds are apart for every count. That rests on a theorem about the golden
  angle which this note does not attempt. `Bag.apart` is a test at a count.
- **The seam.** The consumer passes a count, or its things with a key and an order on keys. It
  gets exact points and rounds them once.
- **A probe.** Take a semaphore of eight permits in a run where three are taken and then
  returned. Draw the permits as a bag of dots and animate the steps with the join. Look at the
  five that stay: none moves when three leave or return. Then give the same set of services in
  two orders to `Bag.arrange`, and compare the two files byte for byte.
- **Effort and value.** Small, small, until the consumer draws the state of a module, which
  its visual language note tracks and has not built. It depends on `Affine.turn` and
  `sqrtDown`.

## 6. The order of building

| Step | Modules | Why then |
| --- | --- | --- |
| 1 | M1 `Between` | It is small, it has no dependency, and it turns three choices that the consumer made by taste into theorems. M2 and M3 cite it |
| 2 | M3 `Score` | It is small. With it a seat can write the probes of every later module as real animations, with the stagger by a law |
| 3 | M2 `Morph` | The pose and the first writer are in the tree. With the alignment and the laws, a step of a graph whose edges gain or lose a segment is one picture and its tracks, and a caller can state that every edge stays on its boxes. That is the owner's "motion as data" at the size of a graph |
| 4 | M4 `Branch`, then M8 `Scale` | Whole numbers, strict, no file of motion. A second seat can build them beside steps 1 to 3 |
| 5 | M5 `Colour` | It is independent. It waits on a sealed source for its constants, which is the owner's to grant |
| 6 | M6 `Metrics`, M7 `Label`, M11 `Place` | In that order. `Metrics.mono` needs no host, so M7 can start on the data face before the consumer's tool measures a proportional one |
| 7 | M9 `Cross`, M10 `Dash` and `Texture` | After the flattening of item 6 of the seams note, and after `Stroke` has landed |
| 8 | M12 `Strip`, M13 `Multiples` | After M8, `IBox` and M7 |
| 9 | M14 `TextOrder` | It is small and can land at any time. It should land before a picture shows a text of a user's program to someone else |
| 10 | M15 `Spring` | After `exp`, sine and cosine |
| 11 | M16 `Bag` | When the consumer draws the state of a module |

**The three to build first: M1 `Between`, M3 `Score`, M2 `Morph`**, in that order. Together
they are one line of work for one seat. Each one's probe is an animation of the consumer's own
data, and each probe reuses the one before. They also carry section 3.7 of the seams note, one
step as one picture and its tracks, from a list of boxes to a whole graph.

M4 `Branch` is the cheapest fourth. It is the owner's own example of a meaning, it changes no
file of motion, and its `wobbleRoom` law bears on a default of the consumer's look today.

## 7. What was looked for and not found

In the kit:

- A law of `mix` between its two ends. `Scene/Motion/Laws.lean` has the start, the end and a
  value mixed with itself. `mix_shift`, which the motion probe's note names, is not in the
  tree.
- A law of a `Change.morph` between its two ends, and a morph of two lists of different
  lengths that does not jump.
- A law that ties the order of tracks in time to an order of keys.
- A box of whole units in the strict layer. `IVec` and `ICubic` are there.
- Any measure of a colour. `Rgb` has its hexadecimal text and its reader, and `Paint` its five
  forms. No luminance, no contrast and no distance.
- Any measure of a text. `Svg.label` places a text and does not size it.
- A test that two segments cross, and the flattening that it needs. The second is planned.
- A dash as geometry. `SvgAttr.strokeDasharray` writes the attribute.
- A root other than the square root, on `Nat` or on `Rat`. The `Rat` form is planned.
- `exp`, sine or cosine. The last two are planned.
- A table of the bidirectional classes of Unicode. M14 needs only twelve code points.
- A writer of any animation element of SVG. Whether the sealed schema has `animate` was not
  checked.

In the consumer:

- A law that boxes stay apart at a moment of a step. `place_apart` is of a still layout, and
  `Laid.boxesApart` is a test that a driver runs on frames.
- A drawing that reads `Flow.unresolvedWaits`.
- A label on an edge, and a legend.
- A measure of a proportional text. `lineCells` counts characters.
- A test of a palette in Lean. `Look.lean` says that the hues passed a validator on their
  ground; that validator is outside the view's modules.
- A form of a step for a reader who asked for less motion.
- A weight of a branch other than an equal share.

## 8. What the seat is unsure of

- **Whether the kernel can run the colour tests.** A proof by evaluation walks a table of 256
  and takes whole roots. The roots must recurse on fuel to reduce. If it is slow, the test
  runs where a look file is read, and no theorem about a look is stated.
- **Which core lemmas the strict rule admits.** The consumer's notes list traps: `omega` on a
  conjunction or over a division, `String.length`, two lemmas of `List`. The laws above were
  checked by hand against none of them. `Nat.sqrt` and its two bounds, and `Nat.log2`, were
  not checked.
- **Whether each host animates the property `d` from CSS.** The motion probe saw Chrome 152
  read it and go from one path to the other point by point. That is one host profile. The
  seat recalls that one family of browsers did not read `d` as a property, and tested nothing.
  M2 has a second writer for that reason.
- **The constants of M5.** The matrices of OKLab and the models of colour-vision deficiency
  are recalled by their authors' names (Ottosson; Viénot, Brettel and Mollon; Machado,
  Oliveira and Fernandes), not read. Which model of deficiency to seal is open. The tritan
  model is the weakest of the three.
- **What a width means.** The exponent and the weights of M4 are a ruling. The consumer's
  organic strokes note asks the owner the same question and records no answer that this seat
  found. The claim that a reader reads width as a quantity in proportion is recalled from the
  literature on graphical perception and was not read.
- **Two boxes that change places.** M1 proves nothing for them, and `unsure` reports them.
  What to draw is open: two phases, or one of the two lifted in the order of painting. This is
  the one case where an arc may be the true motion.
- **Units as types.** The consumer has three units in one type, and the seams note rules "one
  unit" for the port. A length with its unit in its type would stop a class of faults in the
  strict layer, where no rational number can absorb a factor of a thousand. It would also add
  a conversion at every call. The seat did not make it a module and does not know which
  weighs more.
- **`Scale` as an inductive type.** The repository's rule is that stored content is
  first-order data, so a scale is four constructors and not a function. A fifth scale then
  needs a change of the type and of every law.
- **New carriers.** `Whatwg/AGENTS.md` asks for an ownership record for each public type and
  warns against a carrier made for convenience. This note names about twenty types and writes
  no record. `IBox` beside `Box`, and `Share` beside the consumer's count of millionths, each
  need their stated reason: the first is the strict layer's box, as `IVec` is its point; the
  second is exact where a count of millionths rounds.
- **The cost of M2's second way.** Morphing two outlines point by point needs the two strokes
  to have one count of segments. That holds when their centre lines are aligned and are read
  at one count of steps. It was reasoned, not tried.
- **Whether sixteen is right.** M12 and M13 could be one module. M15 could wait for a need.
  M9's `tooNear` is a small thing beside the crossings and may belong to a lint of pictures
  that no one has asked for.

## 9. What this note does not establish

- Nothing here was built, run or measured. The numbers in M1 and M4 are arithmetic on the
  consumer's defaults as read on this date.
- No comprehension was measured. That a staged step is followed better than an unstaged one,
  and a gap at a crossing better than none, is the literature's claim, recalled.
- The probes of this note are described, not made. Each is small, and each uses data that the
  consumer's drivers write today: a build of a corpus program, a run with a race, the flow
  specimen and the graph specimen. Two probes of another seat exist, under
  `docs/research/2026-10-12-motion-probe/`; this seat read their note and not their pages or
  their programs, beyond one definition of `workshop/TreeProbe.lean`.
- The kit was being changed while the seat read it. What section 2 lists was in the tree at
  the second reading. A thing that landed after it is not in this note.
- The laws are statements. The argument for `mix_gap` is written out in M1 because the rounding
  makes it less than plain; no other law has an argument here.
