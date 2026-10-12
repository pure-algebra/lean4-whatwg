import Whatwg.Svg.Value.Number

/-!
# Whatwg.Svg.Value.Path

Owner: path data, the value of the attribute `d` (slice S4b of `docs/SVG-PACKAGE-PLAN.md`,
section 5.3). The authority is `vendor/w3c-svgwg-47e645ef/master/paths.html`: the grammar under
the heading `PathDataBNF`, from `svg_path` to `flag`, the paragraphs after it, and the
definition of the property `d` under the heading `TheDProperty`, whose value is
`none | <string>`. The numbers and the separators are those of `Whatwg/Svg/Value/Number.lean`.

Four typed values:

- `Arc` is one `elliptical_arc_argument`.
- `Command` is one `drawto_command`: the case of its letter, as `relative`, and its argument
  groups. Where the grammar asks for one group or more, the value holds the first group and
  the list of the ones after it.
- `Path` is `svg_path`: no command, or a moveto and the commands after it.
- `PathData` is the value of `d`: the keyword `none`, or a path.

Every term of these types is a value of the grammar. A path whose first command is no moveto,
and a lineto with no coordinate pair, are not terms.

`Path.grammar` and `PathData.grammar` are values of `Grammar`, so their laws are those of
`Whatwg/Svg/Value/Grammar.lean`. The printer writes one spelling of a value:

- a command letter and then its arguments, with nothing between two commands:
  `M100,100L300,100 200,300z`;
- a comma inside a coordinate pair, and one space between two pairs or two coordinates;
- an arc as `rx,ry rotation large,sweep x,y`, as the chapter writes one under
  `PathDataEllipticalArcCommands`: `a100,50 0 0,1 100,50`.

Nothing is printed after a command's arguments because the premise `Syn.ok` asks for it: white
space there could open one more argument group. The value keeps the commands the text states:
`L1,2 3,4` and `L1,2L3,4` are two values with two spellings.

The reader takes every spelling the grammar has under its processing rule (below): white space
between commands and after a letter, and any `comma_wsp` or none between two arguments.

The grammar is followed production by production. Three kinds of production are described
with one reading each, and the language is the same:

- Each sequence production is right-recursive. `coordinate_pair_sequence` is
  `coordinate_pair | (coordinate_pair comma_wsp? coordinate_pair_sequence)`, and
  `coordinate_sequence`, `curveto_coordinate_sequence`, `smooth_curveto_coordinate_sequence`,
  `quadratic_bezier_curveto_coordinate_sequence` and `elliptical_arc_argument_sequence` have
  that shape. The description is `x (comma_wsp? x)*` (`Syn.sepBy1`). Unfolding the recursion
  gives one `x` and then any number of `comma_wsp? x`, which is that expression.
- A command letter, such as `("M" | "m")`, is one character of a set of two, read as a truth
  value. `flag`, `"0" | "1"`, is described the same way.
- `drawto_command` keeps the order of its ten alternatives. Each opens with a letter of its
  own, so no alternative is factored. `svg_path` is described as it is written.

Readings of the sealed text:

- The three leading arguments of `elliptical_arc_argument` are the production `number`, which
  has no sign. So the radii and the rotation are each a `Magnitude`, and an arc with a negative
  rotation is no path data. The grammar of SVG 1.1 gave the rotation a sign. The prose under
  `ArcOutOfRangeParameters` speaks of radii with negative signs; the grammar has none, and
  this module follows the grammar.
- The paragraph after the grammar says that a production consumes as much as it can. The
  reader is that rule: it takes the longest match. The grammar read as a bare expression has
  more texts. In `M10` it can take `1` and `0` as two coordinates, because `comma_wsp?` may be
  empty. Under the rule the first coordinate is `10`, no second one follows, and the text is
  refused.
- `d` takes the keyword as the sealed text writes it: `none`, in lower case, with no white
  space around it. The paragraph `presentation-attribute-css-value` of `master/types.html`
  sends a presentation attribute to the parser of CSS, which this package does not hold
  (ruling SV-26). The text of the attribute is here the path data string itself, not a quoted
  string of CSS.
- A number with a point and no digit after it, `23.`, is refused. The advisement under
  `PathDataBNF` lets a user agent accept one and forbids an author to write one.

What this module does not claim: that the reader accepts every text of the description's
expression. The description is not deterministic (`Syn.deterministic` of
`Whatwg/Svg/Value/Deterministic.lean`, node V3c of the plan), the sealed rule above is the
reader's, and `WhatwgTest/Svg/Path.lean` holds `M10`. Nor does it claim the error handling of
`PathDataErrorHandling`, which renders a path up to its first error, where this reader refuses
the whole text; or any meaning of a command. There is no current point
here, no implicit lineto after a moveto, no absolute reading of a first `m`, and no adjustment
of a radius. `PathData.none` and the empty path are two values, though the chapter gives them
one rendering.

Copyright (c) 2026 World Wide Web Consortium. This file includes material derived from
Scalable Vector Graphics (SVG) 2, https://w3c.github.io/svgwg/svg2-draft/, under the W3C
Document License, https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Svg.Value

/-! ## Flags and command letters -/

/-- The two characters of `flag`. -/
def flagSet : CharSet := .ofList ['0', '1']

/-- `flag`: `"0" | "1"`, as a truth value. -/
def flag : Syn Bool :=
  .map (fun c => c == '1') (fun b => if b then '1' else '0') (by decide) (.one flagSet)

/-- Both flags print. -/
theorem flag_total : flag.Total := fun b => by
  revert b
  decide

/-- Two characters can be the two cases of one command letter: both are ASCII, and they
differ. -/
def letterPair (upper lower : Char) : Bool :=
  decide (upper.toNat < 128) && decide (lower.toNat < 128) && !(upper == lower)

/-- The case of a letter is read back from the character that writes it. -/
theorem letter_law {upper lower : Char} (h : letterPair upper lower = true) (b : Bool) :
    ((if b then lower else upper) == lower) = b := by
  cases b with
  | true => exact decide_eq_true rfl
  | false =>
    simp only [letterPair, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.2

/-- A command letter in either case, such as `("M" | "m")`, as `relative`: the lower case is
`true`. -/
def letter (upper lower : Char) (h : letterPair upper lower = true) : Syn Bool :=
  .map (fun c => c == lower) (fun b => if b then lower else upper) (letter_law h)
    (.one ((CharSet.single upper).union (.single lower)))

/-- Both cases of a command letter print. -/
theorem letter_total {upper lower : Char} {h : letterPair upper lower = true} :
    (letter upper lower h).Total := fun b => by
  have h' := h
  simp only [letterPair, Bool.and_eq_true, decide_eq_true_eq] at h'
  cases b with
  | true =>
    show ((CharSet.single upper).union (.single lower)).mem lower = true
    rw [CharSet.mem_union, CharSet.mem_single_self h'.1.2, Bool.or_true]
  | false =>
    show ((CharSet.single upper).union (.single lower)).mem upper = true
    rw [CharSet.mem_union, CharSet.mem_single_self h'.1.1, Bool.true_or]

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] flag_total letter_total

/-! ## Argument groups -/

/-- `coordinate_pair_double`: `coordinate_pair comma_wsp? coordinate_pair`, printed with a
space between the pairs. -/
abbrev coordinatePairDouble : Syn (Point × Point) := .seq Point.syn (.right spaceSep Point.syn)

/-- `coordinate_pair_triplet`: three pairs, each `comma_wsp?` apart, printed with a space
between two pairs. -/
abbrev coordinatePairTriplet : Syn (Point × Point × Point) :=
  .seq Point.syn (.seq (.right spaceSep Point.syn) (.right spaceSep Point.syn))

/-- One `elliptical_arc_argument`: the typed value of the parameters
`rx ry x-axis-rotation large-arc-flag sweep-flag x y` of `PathDataEllipticalArcCommands`. The
radii and the rotation have no sign, as the production `number` has none. -/
structure Arc where
  /-- The radius along the x-axis of the ellipse. -/
  rx : Magnitude
  /-- The radius along its y-axis. -/
  ry : Magnitude
  /-- `x-axis-rotation`, in degrees. -/
  rotation : Magnitude
  /-- `large-arc-flag`. -/
  largeArc : Bool
  /-- `sweep-flag`. -/
  sweep : Bool
  /-- The end point of the arc. -/
  to : Point
  deriving DecidableEq, Repr, Inhabited

namespace Arc

/-- The description of `elliptical_arc_argument`:
`number comma_wsp? number comma_wsp? number comma_wsp flag comma_wsp? flag comma_wsp?
coordinate_pair`. The separator after the rotation is not optional. It is printed as
`rx,ry rotation large,sweep x,y`. -/
def syn : Syn Arc :=
  .map (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2⟩)
    (fun a => (a.rx, a.ry, a.rotation, a.largeArc, a.sweep, a.to)) (fun _ => rfl)
    (.seq Magnitude.syn (.seq (.right commaSep Magnitude.syn) (.seq (.right spaceSep Magnitude.syn)
      (.seq (.right commaWsp flag) (.seq (.right commaSep flag) (.right spaceSep Point.syn))))))

/-- Every arc prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

end Arc

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Arc.syn_total

/-! ## The ten commands

One description for each alternative of `drawto_command`, under the production's name. Each
is a letter in either case, `wsp*`, and one argument group or more. The value is the case of
the letter and the groups.

A part with no type of its own is an `abbrev`: the search that proves a grammar total
(`Whatwg.Syn`) reads through it, so a part states no totality lemma of its own. -/

namespace Drawto

/-- `moveto`: `("M" | "m") wsp* coordinate_pair_sequence`. -/
abbrev moveto : Syn (Bool × (Point × List Point)) :=
  .seq (letter 'M' 'm' (by decide)) (.right wsps (Point.syn.sepBy1 spaceSep))

/-- `closepath`: `"Z" | "z"`. -/
abbrev closepath : Syn Bool := letter 'Z' 'z' (by decide)

/-- `lineto`: `("L" | "l") wsp* coordinate_pair_sequence`. -/
abbrev lineto : Syn (Bool × (Point × List Point)) :=
  .seq (letter 'L' 'l' (by decide)) (.right wsps (Point.syn.sepBy1 spaceSep))

/-- `horizontal_lineto`: `("H" | "h") wsp* coordinate_sequence`. -/
abbrev horizontalLineto : Syn (Bool × (Decimal × List Decimal)) :=
  .seq (letter 'H' 'h' (by decide)) (.right wsps (Decimal.syn.sepBy1 spaceSep))

/-- `vertical_lineto`: `("V" | "v") wsp* coordinate_sequence`. -/
abbrev verticalLineto : Syn (Bool × (Decimal × List Decimal)) :=
  .seq (letter 'V' 'v' (by decide)) (.right wsps (Decimal.syn.sepBy1 spaceSep))

/-- `curveto`: `("C" | "c") wsp* curveto_coordinate_sequence`. -/
abbrev curveto : Syn (Bool × ((Point × Point × Point) × List (Point × Point × Point))) :=
  .seq (letter 'C' 'c' (by decide)) (.right wsps (coordinatePairTriplet.sepBy1 spaceSep))

/-- `smooth_curveto`: `("S" | "s") wsp* smooth_curveto_coordinate_sequence`. -/
abbrev smoothCurveto : Syn (Bool × ((Point × Point) × List (Point × Point))) :=
  .seq (letter 'S' 's' (by decide)) (.right wsps (coordinatePairDouble.sepBy1 spaceSep))

/-- `quadratic_bezier_curveto`:
`("Q" | "q") wsp* quadratic_bezier_curveto_coordinate_sequence`. -/
abbrev quadraticBezierCurveto : Syn (Bool × ((Point × Point) × List (Point × Point))) :=
  .seq (letter 'Q' 'q' (by decide)) (.right wsps (coordinatePairDouble.sepBy1 spaceSep))

/-- `smooth_quadratic_bezier_curveto`: `("T" | "t") wsp* coordinate_pair_sequence`. -/
abbrev smoothQuadraticBezierCurveto : Syn (Bool × (Point × List Point)) :=
  .seq (letter 'T' 't' (by decide)) (.right wsps (Point.syn.sepBy1 spaceSep))

/-- `elliptical_arc`: `("A" | "a") wsp* elliptical_arc_argument_sequence`. -/
abbrev ellipticalArc : Syn (Bool × (Arc × List Arc)) :=
  .seq (letter 'A' 'a' (by decide)) (.right wsps (Arc.syn.sepBy1 spaceSep))

end Drawto

/-! ## A command -/

/-- One `drawto_command`: the typed value of a command letter and its arguments. `relative`
is the case of the letter, and the lower case is `true`. A command that takes arguments holds
its first group and the groups after it, which the chapter reads as the same command again. -/
inductive Command where
  /-- `M` or `m`: `(x y)+`. -/
  | moveto (relative : Bool) (first : Point) (rest : List Point)
  /-- `Z` or `z`. The two have one effect; the value keeps the letter the text has. -/
  | closepath (relative : Bool)
  /-- `L` or `l`: `(x y)+`. -/
  | lineto (relative : Bool) (first : Point) (rest : List Point)
  /-- `H` or `h`: `x+`. -/
  | horizontalLineto (relative : Bool) (first : Decimal) (rest : List Decimal)
  /-- `V` or `v`: `y+`. -/
  | verticalLineto (relative : Bool) (first : Decimal) (rest : List Decimal)
  /-- `C` or `c`: `(x1 y1 x2 y2 x y)+`, the two control points and the end point. -/
  | curveto (relative : Bool) (first : Point × Point × Point)
      (rest : List (Point × Point × Point))
  /-- `S` or `s`: `(x2 y2 x y)+`, the second control point and the end point. -/
  | smoothCurveto (relative : Bool) (first : Point × Point) (rest : List (Point × Point))
  /-- `Q` or `q`: `(x1 y1 x y)+`, the control point and the end point. -/
  | quadraticBezierCurveto (relative : Bool) (first : Point × Point)
      (rest : List (Point × Point))
  /-- `T` or `t`: `(x y)+`. -/
  | smoothQuadraticBezierCurveto (relative : Bool) (first : Point) (rest : List Point)
  /-- `A` or `a`: one arc or more. -/
  | ellipticalArc (relative : Bool) (first : Arc) (rest : List Arc)
  deriving DecidableEq, Repr, Inhabited

namespace Command

/-- The command of a reading: the alternative says which command it is. -/
def ofReading :
    (Bool × (Point × List Point)) ⊕ Bool ⊕ (Bool × (Point × List Point)) ⊕
      (Bool × (Decimal × List Decimal)) ⊕ (Bool × (Decimal × List Decimal)) ⊕
      (Bool × ((Point × Point × Point) × List (Point × Point × Point))) ⊕
      (Bool × ((Point × Point) × List (Point × Point))) ⊕
      (Bool × ((Point × Point) × List (Point × Point))) ⊕
      (Bool × (Point × List Point)) ⊕ (Bool × (Arc × List Arc)) → Command
  | .inl (r, a) => .moveto r a.1 a.2
  | .inr (.inl r) => .closepath r
  | .inr (.inr (.inl (r, a))) => .lineto r a.1 a.2
  | .inr (.inr (.inr (.inl (r, a)))) => .horizontalLineto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inl (r, a))))) => .verticalLineto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inr (.inl (r, a)))))) => .curveto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (r, a))))))) => .smoothCurveto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (r, a)))))))) =>
    .quadraticBezierCurveto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (r, a))))))))) =>
    .smoothQuadraticBezierCurveto r a.1 a.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (r, a))))))))) =>
    .ellipticalArc r a.1 a.2

/-- The reading of a command: its alternative of `drawto_command`. -/
def toReading :
    Command → (Bool × (Point × List Point)) ⊕ Bool ⊕ (Bool × (Point × List Point)) ⊕
      (Bool × (Decimal × List Decimal)) ⊕ (Bool × (Decimal × List Decimal)) ⊕
      (Bool × ((Point × Point × Point) × List (Point × Point × Point))) ⊕
      (Bool × ((Point × Point) × List (Point × Point))) ⊕
      (Bool × ((Point × Point) × List (Point × Point))) ⊕
      (Bool × (Point × List Point)) ⊕ (Bool × (Arc × List Arc))
  | .moveto r p ps => .inl (r, (p, ps))
  | .closepath r => .inr (.inl r)
  | .lineto r p ps => .inr (.inr (.inl (r, (p, ps))))
  | .horizontalLineto r x xs => .inr (.inr (.inr (.inl (r, (x, xs)))))
  | .verticalLineto r y ys => .inr (.inr (.inr (.inr (.inl (r, (y, ys))))))
  | .curveto r t ts => .inr (.inr (.inr (.inr (.inr (.inl (r, (t, ts)))))))
  | .smoothCurveto r d ds => .inr (.inr (.inr (.inr (.inr (.inr (.inl (r, (d, ds))))))))
  | .quadraticBezierCurveto r d ds =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (r, (d, ds)))))))))
  | .smoothQuadraticBezierCurveto r p ps =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (r, (p, ps))))))))))
  | .ellipticalArc r a as =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (r, (a, as))))))))))

/-- A command's reading is read as the command. -/
theorem ofReading_toReading (c : Command) : ofReading (toReading c) = c := by
  cases c <;> rfl

/-- The description of `drawto_command`: its ten alternatives in the grammar's order. Each
opens with a letter of its own, so the letter decides. -/
def syn : Syn Command :=
  .map ofReading toReading ofReading_toReading
    (.alt Drawto.moveto (.alt Drawto.closepath (.alt Drawto.lineto (.alt Drawto.horizontalLineto
      (.alt Drawto.verticalLineto (.alt Drawto.curveto (.alt Drawto.smoothCurveto
        (.alt Drawto.quadraticBezierCurveto
          (.alt Drawto.smoothQuadraticBezierCurveto Drawto.ellipticalArc)))))))))

/-- Every command prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

end Command

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Command.syn_total

/-! ## The path -/

/-- The typed value of the production `svg_path`: no command, or a moveto and the commands
after it. The moveto is in the constructor, so a path that opens with another command is no
term. -/
inductive Path where
  /-- No command: the empty text, or white space alone. -/
  | empty
  /-- The first command, a moveto with its case and its pairs, and the commands after it. -/
  | moveto (relative : Bool) (first : Point) (rest : List Point) (commands : List Command)
  deriving DecidableEq, Repr, Inhabited

namespace Path

/-- The path of a reading. -/
def ofReading : Option ((Bool × (Point × List Point)) × List Command) → Path
  | none => .empty
  | some (m, cs) => .moveto m.1 m.2.1 m.2.2 cs

/-- The reading of a path. -/
def toReading : Path → Option ((Bool × (Point × List Point)) × List Command)
  | .empty => none
  | .moveto r p ps cs => some ((r, (p, ps)), cs)

/-- A path's reading is read as the path. -/
theorem ofReading_toReading (p : Path) : ofReading (toReading p) = p := by
  cases p <;> rfl

/-- The description of `svg_path`: `wsp* (moveto (wsp* drawto_command)*)? wsp*`. The white
space is read in any amount and printed as nothing. -/
def syn : Syn Path :=
  .map ofReading toReading ofReading_toReading
    (.right wsps (.left (Syn.opt (.seq Drawto.moveto (.many (.right wsps Command.syn)))) wsps))

/-- Every path prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of `svg_path`. -/
def grammar : Grammar Path := ⟨syn, by decide +kernel, syn_total⟩

/-- A path of several subpaths: each is an absolute moveto to its start and the commands after
it. The first moveto is the path's own and each later one is a command, so a program that
draws several closed shapes in one `d` builds the list and not the two forms. -/
def ofSubpaths : List (Point × List Command) → Path
  | [] => .empty
  | first :: rest =>
    .moveto false first.1 []
      (first.2 ++ rest.flatMap fun subpath => Command.moveto false subpath.1 [] :: subpath.2)

theorem ofSubpaths_nil : ofSubpaths [] = .empty := rfl

/-- One subpath is a moveto and its commands. -/
theorem ofSubpaths_singleton (start : Point) (commands : List Command) :
    ofSubpaths [(start, commands)] = .moveto false start [] commands := by
  rw [ofSubpaths, List.flatMap_nil, List.append_nil]

end Path

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Path.syn_total

/-! ## The value of `d` -/

/-- The keyword `none` of the property `d`, as the sealed text writes it. -/
def noneKeyword : Syn Unit := .lit ['n', 'o', 'n', 'e']

/-- The keyword prints. -/
theorem noneKeyword_total : noneKeyword.Total := lit_total _ (by decide)

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] noneKeyword_total

/-- The typed value of the attribute `d`, whose property has the value `none | <string>`
(`TheDProperty`): the keyword, or a path data string. -/
inductive PathData where
  /-- The keyword `none`: no path data. -/
  | none
  /-- A path data string, the empty one included. -/
  | path (data : Path)
  deriving DecidableEq, Repr, Inhabited

namespace PathData

/-- The value of a reading. -/
def ofReading : Unit ⊕ Path → PathData
  | .inl _ => .none
  | .inr p => .path p

/-- The reading of a value. -/
def toReading : PathData → Unit ⊕ Path
  | .none => .inl ()
  | .path p => .inr p

/-- A value's reading is read as the value. -/
theorem ofReading_toReading (d : PathData) : ofReading (toReading d) = d := by
  cases d <;> rfl

/-- The description of the value of `d`: the keyword `none`, or else `svg_path`. No path
opens with `n`, so the first character decides. -/
def syn : Syn PathData := .map ofReading toReading ofReading_toReading (.alt noneKeyword Path.syn)

/-- Every value of `d` prints. -/
theorem syn_total : syn.Total := by
  unfold syn
  aesop (rule_sets := [Whatwg.Syn])

/-- The grammar of the value of `d`. -/
def grammar : Grammar PathData := ⟨syn, by decide +kernel, syn_total⟩

end PathData

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] PathData.syn_total

end Whatwg.Svg.Value
