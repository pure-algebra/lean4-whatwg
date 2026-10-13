import Whatwg.Svg.Scene.Network.Fit

/-!
# WhatwgTest.Svg.UseNetwork

The totals of the queue of lean4-effect4's sketch as a flow network on
`Whatwg/Svg/Scene/Network.lean`, and d3-sankey's example against d3's own expected files
(slice S22; ask W18). The sketch is `docs/research/2026-10-13-living-quantities/sketch.html`,
whose fourth picture draws where the four messages of the run went, by hand. The consumer is
read at its checkout `6ad8f7b8d`, which has no fold of a journal into totals yet: the note asks
for one, and `legs` below is it. This module imports nothing of that package.

**What is here, in the note's words.**

| The note's | Here |
| --- | --- |
| totals as channels: the run's flows summed | `totals`, a `Network` of the journal's `legs` |
| the branches of a split sum to the trunk | `Network.outs_stacked` read at `offered` (`split_tiles`), `Network.conserved_fills` read at `held` (`held_fills`) |
| conservation: a unit enters by an offer and leaves by a take | `Network.Conserved`, decided at each inner node (`inner_conserve`) |
| links do not cross a node | `no_link_meets_a_node`, from `Network.channel_misses_neighbours` |
| a channel's width is what it carries | `Network.channel_times`, with nine pixels for one message as the sketch has |

**d3-sankey.** `test/energy.json` of d3-sankey at `bb7233ea0004` has 48 nodes and 68 links, and
`test/energy-nodes.json` and `test/energy-links.json` the expected place of each. d3 marks that
test `tape.skip`, so the files are its expected output and not a result of its test run. Every
number in them is floating point, rounded to a tenth of a pixel. The kit counts in whole
hundredths of a pixel and rounds down, so a number of d3's file is compared within half a
tenth. What is compared: the value of each node and the scale `ky` together, through the
length of each of the 48 nodes; the columns; the width of each of the 68 links; and where each
link leaves its source and enters its target, below the top of the node. What is taken from
the file and not computed: the order of the links at a side, which d3 sorts by where its
relaxation has put the node at the other end. What is not compared: where a node stands down
its column, which is the relaxation's.

The lines are of four kinds: the consumer's fold; readers, which are laws of the kit applied
to its network and to d3's; finite evaluations; and controls.
-/

namespace WhatwgTest.Svg.UseNetwork

open Whatwg.Svg.Scene

/-! ## The journal of the scene, and its totals -/

/-- What became of an offer, and of a take. -/
inductive Outcome where
  /-- An offer whose message entered the buffer at once. -/
  | enteredAtOnce
  /-- An offer that found the buffer full and waited at the inlet. -/
  | waitedAtInlet
  /-- A take that found a message. -/
  | takenAtOnce
  /-- A take that found the buffer empty, and whose taker waited at the outlet. -/
  | takenAfterWait
  deriving DecidableEq, Repr

/-- **The journal of the scene**: its eight requests in their order, each with what became of
it. The scene has nine steps, and the ninth is the request 7 taking 40 after its wait. The
offers of 10, 20 and 40 entered at once and the offer of 30 waited; the takes of the requests
4, 5 and 6 found a message, and the take of the request 7 waited. -/
def journal : List Outcome :=
  [.enteredAtOnce, .enteredAtOnce, .waitedAtInlet, .takenAtOnce, .takenAtOnce, .takenAtOnce,
    .takenAfterWait, .enteredAtOnce]

/-- Where a message is on its way through the queue: the nodes of the sketch's fourth
picture. -/
inductive Stage where
  | offered
  | atOnce
  | waited
  | held
  | taken
  | takenLate
  deriving DecidableEq, Repr

/-- One leg of the totals: so many messages went from one stage to another. -/
structure Leg where
  fr : Stage
  to : Stage
  units : Nat
  deriving DecidableEq, Repr

/-- How many commands of the journal had an outcome. -/
def count (o : Outcome) : Nat := (journal.filter (· == o)).length

/-- **The totals of the run**: a fold of the journal. A message is offered and enters at once
or waits at the inlet; it is held; and it is taken at once or by a taker that waited. -/
def legs : List Leg :=
  [⟨.offered, .atOnce, count .enteredAtOnce⟩, ⟨.offered, .waited, count .waitedAtInlet⟩,
    ⟨.atOnce, .held, count .enteredAtOnce⟩, ⟨.waited, .held, count .waitedAtInlet⟩,
    ⟨.held, .taken, count .takenAtOnce⟩, ⟨.held, .takenLate, count .takenAfterWait⟩]

/-- The six stages, in the order in which those of one column stand down it. -/
def stages : List Stage := [.offered, .atOnce, .waited, .held, .taken, .takenLate]

/-- **The totals as a network**: the consumer's legs, read by three functions. -/
def totals : Network Leg Stage where
  nodes := stages
  links := legs
  src := (·.fr)
  dst := (·.to)
  carry := (·.units)

/-- The column of a stage, as the sketch has them. -/
def col : Stage → Nat
  | .offered => 0
  | .atOnce => 1
  | .waited => 1
  | .held => 2
  | .taken => 3
  | .takenLate => 3

/-- The numbers of the picture: a node 12 pixels thick, columns 96 apart, 16 between two nodes
of a column, and 9 pixels for one message, which is the sketch's width of a channel. -/
def measure : Network.Measure := ⟨12, 96, 16, Network.times 9⟩

/-! ## Readers -/

/-- The stages in their order serve the legs: each leg goes from an earlier stage to a later
one. -/
theorem stages_serve : Layers.Serves totals.steps totals.links stages :=
  (Layers.serves_iff totals.steps totals.links stages).mp (by decide)

/-- **Every leg goes to a later column.** -/
theorem legs_forward (e : Leg) (he : e ∈ legs) :
    totals.depth stages e.fr < totals.depth stages e.to :=
  Network.depth_lt stages_serve he

/-- **A unit enters by an offer and leaves by a take**: each inner stage conserves. -/
theorem inner_conserve : ∀ v ∈ [Stage.atOnce, Stage.waited, Stage.held], totals.Conserved v := by
  decide

/-- **At the buffer, the bands that enter and the bands that leave fill its two sides**: the
four messages that were held are the three and the one that entered, and the three and the one
that were taken. -/
theorem held_fills :
    ((totals.ins measure col .held).map IBox.height).sum = (totals.box measure col .held).height ∧
      ((totals.outs measure col .held).map IBox.height).sum =
        (totals.box measure col .held).height :=
  Network.conserved_fills col (inner_conserve .held (by decide)) rfl

/-- **The branches of the split at the inlet tile**: the band of what entered at once and the
band of what waited lie one below the other on the side of `offered`, with no gap. -/
theorem split_tiles : Network.Stacked (totals.outs measure col .offered) :=
  Network.outs_stacked totals measure col .offered

/-- No two stages share a pixel, and each is inside the room. -/
theorem totals_clear : (totals.layout measure col).Clear :=
  Network.layout_clear totals col (by decide) (by decide)

theorem totals_fits : (totals.layout measure col).Fits := Network.layout_fits totals measure col

/-- Every leg is between two neighbouring columns. -/
theorem legs_neighbours : ∀ e ∈ legs, col e.to = col e.fr + 1 := by decide

/-- **No link meets a node**: the room of each placed leg shares nothing with the box of any
stage. A ribbon that stays in the room of its two ends crosses no node. -/
theorem no_link_meets_a_node : ∀ c ∈ totals.channels measure col, ∀ w : Stage,
    (totals.box measure col w).Disjoint (Boxed.box c) := fun c hc w =>
  Network.channel_misses_neighbours totals col (by decide) hc
    (legs_neighbours c.link (Network.channel_spec totals measure col hc).1) w

/-- **A channel is nine pixels wide for each message that it carries**, at both ends. -/
theorem channel_width : ∀ c ∈ totals.channels measure col,
    c.out.height = (c.link.units * 9 : Nat) ∧ c.into.height = (c.link.units * 9 : Nat) :=
  fun _ hc => Network.channel_times totals col rfl hc

/-! ## Finite evaluations against the sketch -/

-- The fold gives the totals that the sketch's fourth picture says in words: four offered,
-- three entered at once and one waited; four held; three taken at once and one after its
-- taker waited.
#guard legs.map (·.units) == [3, 1, 3, 1, 3, 1]
#guard stages.map totals.value == [4, 3, 1, 4, 3, 1]

-- The columns of the sketch are the layers of the legs.
#guard stages.map (totals.depth stages) == stages.map col

-- Where each stage stands: across at its column, and down below the stage before it in its
-- column by that stage's length and the gap. `offered` is 4 * 9 = 36 long.
#guard stages.map (totals.box measure col) ==
  [⟨0, 0, 12, 36⟩, ⟨96, 0, 108, 27⟩, ⟨96, 43, 108, 52⟩, ⟨192, 0, 204, 36⟩, ⟨288, 0, 300, 27⟩,
    ⟨288, 43, 300, 52⟩]
#guard ((totals.layout measure col).w, (totals.layout measure col).h) == (300, 52)

-- **Each leg as data for a ribbon**: where its band leaves its source and where it enters its
-- target, each from `y0` to `y1` on the side of the node. At `offered` the trunk of 36 splits
-- into 27 and 9; at `held` they join again in the same order, and split again.
#guard (totals.channels measure col).map (fun c =>
    (c.link.fr, c.link.to, c.out.x0, c.out.y0, c.out.y1, c.into.x0, c.into.y0, c.into.y1)) ==
  [(.offered, .atOnce, 12, 0, 27, 96, 0, 27), (.offered, .waited, 12, 27, 36, 96, 43, 52),
    (.atOnce, .held, 108, 0, 27, 192, 0, 27), (.waited, .held, 108, 43, 52, 192, 27, 36),
    (.held, .taken, 204, 0, 27, 288, 0, 27), (.held, .takenLate, 204, 27, 36, 288, 43, 52)]

-- The two edges of a ribbon, for the leg of the message that waited.
#guard (totals.channels measure col)[1]?.map (·.upper) == some (⟨12, 27⟩, ⟨96, 43⟩)
#guard (totals.channels measure col)[1]?.map (·.lower) == some (⟨12, 36⟩, ⟨96, 52⟩)

/-! ## Controls -/

-- The two ends of the run do not conserve: nothing enters `offered` and nothing leaves
-- `taken`. The value of a node is the greater of the two, so an end is as long as its links.
#guard !decide (totals.Conserved .offered)
#guard !decide (totals.Conserved .taken)
#guard (totals.enters .offered, totals.leaves .offered, totals.value .offered) == (0, 4, 4)

/-- The same totals with no stage for what entered at once: its three messages go from
`offered` to `held` in one link, over the column of `waited`. -/
def short : Network Leg Stage where
  nodes := [.offered, .waited, .held, .taken, .takenLate]
  links := [⟨.offered, .held, 3⟩, ⟨.offered, .waited, 1⟩, ⟨.waited, .held, 1⟩, ⟨.held, .taken, 3⟩,
    ⟨.held, .takenLate, 1⟩]
  src := (·.fr)
  dst := (·.to)
  carry := (·.units)

-- The long link's room holds the box of `waited`, which stands at the top of the column
-- between: a ribbon drawn there crosses a node. `Network.channel_misses` leaves out the nodes
-- of the columns strictly between a link's two, and this is why. A stage in each column that
-- a link passes, as `atOnce` in `totals`, is the remedy.
#guard (short.channels measure col).map (fun c =>
    decide ((short.box measure col .waited).Disjoint (Boxed.box c))) ==
  [false, true, true, true, true]

/-- The scale of ten pixels for three messages: it rounds. -/
def thirds : Network.Measure := ⟨12, 96, 16, Network.ratio 10 3⟩

/-- Three sources of one message each, into one node. -/
def three : Network (Nat × Nat) Nat where
  nodes := [0, 1, 2, 3]
  links := [(0, 3), (1, 3), (2, 3)]
  src := (·.1)
  dst := (·.2)
  carry := fun _ => 1

-- On a scale that rounds, the bands still tile and are together as high as the scale of the
-- sum, 10 for 3. The third link is 3 wide where it leaves and 4 where it enters: the edges
-- are rounded and not the widths. `Network.channel_times` asks for a scale of whole units, and
-- this is why.
#guard (three.ins thirds (fun k => if k == 3 then 1 else 0) 3).map (fun b => (b.y0, b.y1)) ==
  [(0, 3), (3, 6), (6, 10)]
#guard (three.channels thirds (fun k => if k == 3 then 1 else 0)).map
    (fun c => (c.out.height, c.into.height)) == [(3, 3), (3, 3), (3, 4)]

/-! ## d3-sankey's example -/

/-- A link of d3's example: its place in the file, its two nodes by their index, and its value
in thousandths. -/
structure Link where
  index : Nat
  source : Nat
  target : Nat
  value : Nat
  deriving DecidableEq, Repr

/-- The 68 links of `test/energy.json`, in the order of the file. Each value is the file's
number times one thousand: the file has three decimals at most. -/
def file : List Link :=
  ([(0, 1, 124729), (1, 2, 597), (1, 3, 26862), (1, 4, 280322), (1, 5, 81144), (6, 2, 35000),
    (7, 4, 35000), (8, 9, 11606), (10, 9, 63965), (9, 4, 75571), (11, 12, 10639),
    (11, 13, 22505), (11, 14, 46184), (15, 16, 104453), (15, 14, 113726), (15, 17, 27140),
    (15, 12, 342165), (15, 18, 37797), (15, 19, 4412), (15, 13, 40858), (15, 3, 56691),
    (15, 20, 7863), (15, 21, 90008), (15, 22, 93494), (23, 24, 40719), (25, 24, 82233),
    (5, 13, 129), (5, 3, 1401), (5, 26, 151891), (5, 19, 2096), (5, 12, 48580), (27, 15, 7013),
    (17, 28, 20897), (17, 3, 6242), (28, 18, 20897), (29, 15, 6995), (2, 12, 121066),
    (2, 30, 128690), (2, 18, 135835), (2, 31, 14458), (2, 32, 206267), (2, 19, 3640),
    (2, 33, 33218), (2, 20, 4413), (34, 1, 4375), (24, 5, 122952), (35, 26, 839978),
    (36, 37, 504287), (38, 37, 107703), (37, 2, 611990), (39, 4, 56587), (39, 1, 77810),
    (40, 14, 193026), (40, 13, 70672), (41, 15, 59901), (42, 14, 19263), (43, 42, 19263),
    (43, 41, 59901), (4, 19, 882), (4, 26, 400120), (4, 12, 46477), (26, 15, 525531),
    (26, 3, 787129), (26, 11, 79329), (44, 15, 9452), (45, 1, 182010), (46, 15, 19013),
    (47, 15, 289366)] : List (Nat × Nat × Nat)).zipIdx.map fun p => ⟨p.2, p.1.1, p.1.2.1, p.1.2.2⟩

/-- `x` of each node in `test/energy-nodes.json`, in tenths of a pixel. -/
def theirX : List Nat :=
  [10, 1357, 2704, 9440, 2704, 2704, 10, 10, 10, 1357, 10, 5399, 9440, 9440, 9440, 5399, 9440,
    6746, 9440, 9440, 9440, 9440, 9440, 10, 1357, 10, 4051, 10, 8093, 10, 9440, 9440, 9440, 9440,
    10, 10, 10, 1357, 10, 10, 10, 1357, 1357, 10, 10, 10, 10, 10]

/-- `y` of each node in that file, in tenths. -/
def theirY : List Nat :=
  [1300, 1158, 3942, 609, 1326, 1903, 4903, 1881, 2187, 1986, 2018, 2586, 2253, 3568, 2959, 1506,
    1645, 2207, 3924, 3456, 3811, 1857, 2053, 2487, 2252, 2299, 354, 3159, 2599, 3267, 4552, 4925,
    4232, 4789, 1776, 10, 4050, 4004, 4688, 1533, 3669, 3238, 3437, 3484, 3374, 1006, 3039, 2630]

/-- `dy` of each node in that file, in tenths: how long the node is. -/
def theirDy : List Nat :=
  [133, 415, 691, 937, 477, 218, 37, 37, 12, 81, 68, 85, 607, 143, 397, 980, 111, 29, 207, 12, 13,
    96, 100, 43, 131, 88, 1485, 7, 22, 7, 137, 15, 220, 35, 5, 896, 538, 653, 115, 143, 281, 64, 21,
    84, 10, 194, 20, 309]

/-- `dy`, `sy` and `ty` of each link in `test/energy-links.json`, in tenths: how wide the link
is, and how far below the top of its source and of its target it starts. -/
def theirLinks : List (Nat × Nat × Nat) :=
  [(133, 0, 194), (1, 414, 0), (29, 0, 840), (299, 29, 0), (87, 328, 0), (37, 0, 653),
    (37, 0, 359), (12, 0, 68), (68, 0, 0), (81, 0, 397), (11, 0, 466), (24, 61, 44),
    (49, 11, 121), (111, 60, 0), (121, 762, 0), (29, 368, 0), (365, 397, 50), (40, 940, 0),
    (5, 883, 1), (44, 888, 0), (60, 0, 868), (8, 931, 0), (96, 172, 0), (100, 268, 0),
    (43, 0, 88), (88, 0, 0), (0, 218, 44), (1, 162, 929), (162, 0, 1323), (2, 215, 6),
    (52, 164, 415), (7, 0, 889), (22, 7, 0), (7, 0, 930), (22, 0, 40), (7, 0, 961),
    (129, 0, 478), (137, 503, 0), (145, 138, 63), (15, 675, 0), (220, 283, 0), (4, 129, 8),
    (35, 640, 0), (5, 133, 8), (5, 0, 410), (131, 0, 87), (896, 0, 0), (538, 0, 0),
    (115, 0, 538), (653, 0, 1), (60, 83, 299), (83, 0, 327), (206, 0, 191), (75, 206, 68),
    (64, 0, 897), (21, 0, 171), (21, 64, 0), (64, 0, 0), (1, 476, 0), (427, 0, 896),
    (50, 427, 0), (561, 840, 0), (840, 0, 0), (85, 1400, 0), (10, 0, 968), (194, 0, 0),
    (20, 0, 869), (309, 0, 561)]

/-- The column of a node in d3's file: its `x`, which is 134.7 pixels for each column from 1. -/
def column (k : Nat) : Nat := (theirX.getD k 0 - 10) / 1347

/-- Where d3's file has a node, down. -/
def placed (k : Nat) : Nat := theirY.getD k 0

/-- The links in the order in which d3 has them at a side: by where the node at the source
stands, and then by where the node at the target stands. Among the links that leave one node
this is the order of their targets, and among those that enter one node the order of their
sources, which are d3's two sorts (`reorderLinks`). -/
def sorted : List Link :=
  file.mergeSort fun a b =>
    placed a.source < placed b.source ||
      (placed a.source == placed b.source && placed a.target ≤ placed b.target)

/-- **d3's example as a network**, its links in d3's order. -/
def energy : Network Link Nat where
  nodes := List.range 48
  links := sorted
  src := (·.source)
  dst := (·.target)
  carry := (·.value)

/-- An order of the 48 nodes that serves the links: by column, and within a column by index. -/
def byColumn : List Nat :=
  (List.range 8).flatMap fun c => (List.range 48).filter fun k => column k == c

/-- d3's call: `extent([[1, 1], [959, 494]])`, `nodePadding(10)`, `nodeWidth(15)`. In hundredths
of a pixel the room is 49300 high, the gap 1000, a node 1500 thick, and the columns 13470
apart. -/
def ROOM : Nat := 49300
def PAD : Nat := 1000

/-- d3's scale for this call: the 20 nodes of the first column leave 493 - 19 * 10 = 303
pixels for values that sum to 2840.703. -/
def energyMeasure : Network.Measure := ⟨1500, 13470, PAD, Network.ratio 30300 2840703⟩

/-- Whether a length of the kit, in hundredths of a pixel and rounded down, is a number of d3's
file, in tenths and rounded to the nearest: the two are within half a tenth. -/
def near (mine : Int) (theirs : Nat) : Bool :=
  decide (10 * (theirs : Int) ≤ mine + 5) && decide (mine ≤ 10 * (theirs : Int) + 5)

-- The order serves, and `justify` gives the 48 columns of d3's file.
#guard Layers.serves energy.steps energy.links byColumn
#guard (List.range 48).map (energy.justify byColumn) == (List.range 48).map column

-- **`fit` is d3's `ky`**: the first column, with the most nodes, is the one that bounds it.
#guard energy.fit column PAD ROOM == (30300, 2840703)

-- **The 48 lengths of d3's file.** The length of a node is its value on the scale, so this
-- compares `value`, which is `computeNodeValues`, and the scale together.
#guard (List.range 48).all fun v => near (energy.length energyMeasure v) (theirDy.getD v 0)

-- **The 68 widths and the 136 places of d3's file**: each link is as wide as d3 has it, and
-- starts as far below the top of its source and of its target as d3 has it.
#guard (energy.channels energyMeasure column).all fun c =>
  let theirs := theirLinks.getD c.link.index (0, 0, 0)
  near c.out.height theirs.1 && near c.into.height theirs.1 &&
    near (c.out.y0 - (energy.top energyMeasure column c.link.source : Nat)) theirs.2.1 &&
    near (c.into.y0 - (energy.top energyMeasure column c.link.target : Nat)) theirs.2.2

-- Every column is inside d3's room, and the first column fills it to the rounding.
#guard (energy.layout energyMeasure column).h ≤ ROOM
#guard ROOM - 20 ≤ (energy.layout energyMeasure column).h

/-- **Both bands of each of the 68 links stay inside its two nodes**: a reader, with no
evaluation of a place. -/
theorem energy_inside : ∀ c ∈ energy.channels energyMeasure column,
    c.out.Inside (energy.box energyMeasure column c.link.source) ∧
      c.into.Inside (energy.box energyMeasure column c.link.target) := fun _ hc =>
  Network.channel_inside energy column (Network.rising_ratio 30300 2840703) hc

/-- The measure with the scale that `fit` gives for d3's room, not written out. The guard
above says that it is `energyMeasure`. -/
def fitted : Network.Measure :=
  ⟨1500, 13470, PAD,
    Network.ratio (energy.fit column PAD ROOM).1 (energy.fit column PAD ROOM).2⟩

/-- **Each of the 48 nodes ends inside d3's room**: a reader of `Network.fit_fits`, with no
evaluation of a place. A column has 48 nodes at most, so its gaps alone are 470 pixels at
most, and the room has 493. -/
theorem energy_fits : ∀ v ∈ energy.nodes,
    energy.top fitted column v + energy.length fitted v ≤ ROOM := fun v hv =>
  Network.fit_fits energy column rfl (fun u _ => by
    have h : (energy.nodes.filter fun w => decide (column w = column u)).length ≤ 48 :=
      Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq List.length_range)
    show ((energy.nodes.filter fun w => decide (column w = column u)).length - 1) * 1000 ≤ 49300
    omega) hv

-- A control: in the order of the file, and not in d3's, the links are as wide but most start
-- elsewhere. The order of the links at a side is the caller's.
#guard (({ energy with links := file }).channels energyMeasure column).all fun c =>
  near c.out.height (theirLinks.getD c.link.index (0, 0, 0)).1
#guard !(({ energy with links := file }).channels energyMeasure column).all fun c =>
  near (c.out.y0 - (energy.top energyMeasure column c.link.source : Nat))
    (theirLinks.getD c.link.index (0, 0, 0)).2.1

-- A control: the two ends of a link differ by a hundredth of a pixel for some links, since the
-- scale rounds, and never by more.
#guard (energy.channels energyMeasure column).any fun c => c.out.height != c.into.height
#guard (energy.channels energyMeasure column).all fun c =>
  decide (c.out.height ≤ c.into.height + 1) && decide (c.into.height ≤ c.out.height + 1)

end WhatwgTest.Svg.UseNetwork
