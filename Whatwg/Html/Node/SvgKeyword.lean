import Whatwg.Html.Node.SvgPaint

/-!
# Whatwg.Html.Node.SvgKeyword

Owner: the keywords of a picture's attributes, as types (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`). The table of kinds gives these attributes no grammar, so the node
holds their value as text, and a program wrote the text: `.attr .stroke_linecap "round"`,
`.attr .maskUnits "userSpaceOnUse"`, `.fillRule true`. A word with a letter wrong is still a
text, and the checker passes it.

This module gives each closed set of keywords a type, and each attribute a helper that takes
the type and writes the text:

```
Svg.path d [.strokeLinecap .round, .strokeLinejoin .round, .vectorEffect .nonScalingStroke]
Svg.loops outlines [.fillRule .evenodd]
Svg.rect 0 0 40 20 [.fill .none, .pointerEvents .all]
```

So a keyword that is no keyword is no term. `Keyword` is the class of these types: every
keyword once, and the text of each. `Keyword.read?` reads a text back, for a program that reads
a look from a file, and each type states that the text of a keyword reads back as the keyword
(`LineCap.read?_css` and its like): so two keywords have two texts.

Where each set is taken from:

| Type | Attribute | Read from |
| --- | --- | --- |
| `VectorEffect` | `vector-effect` | the value line of the property, `master/coords.html` |
| `Units` | `gradientUnits`, `maskUnits` and their like | `SVGUnitTypes`, `master/types.html` |
| `Orient` | `orient` of `marker` | memory; `auto-start-reverse` stands in a figure of `master/struct.html` |
| `LineCap`, `LineJoin`, `FillRule`, `PaintLayer` | painting properties | memory: the chapter Painting is not sealed |
| `FontStyle`, `DominantBaseline`, `Visibility` | properties of CSS | memory: no CSS text is sealed for them |
| `PointerEvents` | `pointer-events` | memory: the chapter Scripting and Interactivity is not sealed |
| `SpreadMethod`, `MarkerUnits`, `MaskType` | paint servers, markers, masks | memory: not sealed |

Three helpers took the place of a helper of `Whatwg/Html/Node/SvgPaint.lean` that took a flag
or a text: `fillRule`, `fontStyle` and `pointerEvents`. A caller that holds a flag for italic
writes `.fontStyle (.ofItalic flag)`.

What this module does not claim: that a set is the whole set of its property in SVG or CSS, or
that a text it writes is valid there. For a row marked memory no sealed text of this repository
was read. Nor that an element takes the attribute: `SvgAttr.allOk` judges that.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Value (Decimal)

/-- A closed set of keywords: every keyword once, and the text of each. -/
class Keyword (κ : Type) where
  /-- Every keyword, once. -/
  all : List κ
  /-- The text of a keyword. -/
  css : κ → String

/-- Read a text as a keyword of a set: the keyword that writes it. -/
def Keyword.read? {κ : Type} [Keyword κ] (text : String) : Option κ :=
  (Keyword.all (κ := κ)).find? fun k => Keyword.css k == text

/-! ## Strokes and fills -/

/-- The shape of the end of an open subpath: `stroke-linecap`. -/
inductive LineCap where
  | butt | round | square
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a cap. -/
def LineCap.css : LineCap → String
  | .butt => "butt"
  | .round => "round"
  | .square => "square"

instance : Keyword LineCap := ⟨[.butt, .round, .square], LineCap.css⟩

/-- The text of a cap reads back as the cap. -/
theorem LineCap.read?_css (k : LineCap) : Keyword.read? k.css = some k := by cases k <;> rfl

/-- The shape of a corner of a stroke: `stroke-linejoin`. -/
inductive LineJoin where
  | miter | miterClip | round | bevel | arcs
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a join. -/
def LineJoin.css : LineJoin → String
  | .miter => "miter"
  | .miterClip => "miter-clip"
  | .round => "round"
  | .bevel => "bevel"
  | .arcs => "arcs"

instance : Keyword LineJoin := ⟨[.miter, .miterClip, .round, .bevel, .arcs], LineJoin.css⟩

/-- The text of a join reads back as the join. -/
theorem LineJoin.read?_css (k : LineJoin) : Keyword.read? k.css = some k := by cases k <;> rfl

/-- Which points are inside a shape that crosses itself: `fill-rule` and `clip-rule`. -/
inductive FillRule where
  | nonzero | evenodd
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a rule. -/
def FillRule.css : FillRule → String
  | .nonzero => "nonzero"
  | .evenodd => "evenodd"

instance : Keyword FillRule := ⟨[.nonzero, .evenodd], FillRule.css⟩

/-- The text of a rule reads back as the rule. -/
theorem FillRule.read?_css (k : FillRule) : Keyword.read? k.css = some k := by cases k <;> rfl

/-- One of the three layers that a shape is painted in: a word of `paint-order`. -/
inductive PaintLayer where
  | fill | stroke | markers
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a layer. -/
def PaintLayer.css : PaintLayer → String
  | .fill => "fill"
  | .stroke => "stroke"
  | .markers => "markers"

instance : Keyword PaintLayer := ⟨[.fill, .stroke, .markers], PaintLayer.css⟩

/-- The text of a layer reads back as the layer. -/
theorem PaintLayer.read?_css (k : PaintLayer) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-- What a transform leaves alone: `vector-effect`. -/
inductive VectorEffect where
  | none | nonScalingStroke | nonScalingSize | nonRotation | fixedPosition
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of an effect. -/
def VectorEffect.css : VectorEffect → String
  | .none => "none"
  | .nonScalingStroke => "non-scaling-stroke"
  | .nonScalingSize => "non-scaling-size"
  | .nonRotation => "non-rotation"
  | .fixedPosition => "fixed-position"

instance : Keyword VectorEffect :=
  ⟨[.none, .nonScalingStroke, .nonScalingSize, .nonRotation, .fixedPosition], VectorEffect.css⟩

/-- The text of an effect reads back as the effect. -/
theorem VectorEffect.read?_css (k : VectorEffect) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-! ## Text and the pointer -/

/-- The slant of a face: `font-style`. -/
inductive FontStyle where
  | normal | italic | oblique
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a slant. -/
def FontStyle.css : FontStyle → String
  | .normal => "normal"
  | .italic => "italic"
  | .oblique => "oblique"

instance : Keyword FontStyle := ⟨[.normal, .italic, .oblique], FontStyle.css⟩

/-- The text of a slant reads back as the slant. -/
theorem FontStyle.read?_css (k : FontStyle) : Keyword.read? k.css = some k := by cases k <;> rfl

/-- The slant of a face that is italic or not: what a look holds as a flag. -/
def FontStyle.ofItalic (italic : Bool) : FontStyle := if italic then .italic else .normal

/-- The line of a face that a text is placed by: `dominant-baseline`. -/
inductive DominantBaseline where
  | auto | textBottom | alphabetic | ideographic | middle | central | mathematical | hanging
  | textTop
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a baseline. -/
def DominantBaseline.css : DominantBaseline → String
  | .auto => "auto"
  | .textBottom => "text-bottom"
  | .alphabetic => "alphabetic"
  | .ideographic => "ideographic"
  | .middle => "middle"
  | .central => "central"
  | .mathematical => "mathematical"
  | .hanging => "hanging"
  | .textTop => "text-top"

instance : Keyword DominantBaseline :=
  ⟨[.auto, .textBottom, .alphabetic, .ideographic, .middle, .central, .mathematical, .hanging,
      .textTop], DominantBaseline.css⟩

/-- The text of a baseline reads back as the baseline. -/
theorem DominantBaseline.read?_css (k : DominantBaseline) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-- Which part of an element takes the pointer: `pointer-events`. -/
inductive PointerEvents where
  | boundingBox | visiblePainted | visibleFill | visibleStroke | visible | painted | fill
  | stroke | all | none
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a choice. -/
def PointerEvents.css : PointerEvents → String
  | .boundingBox => "bounding-box"
  | .visiblePainted => "visiblePainted"
  | .visibleFill => "visibleFill"
  | .visibleStroke => "visibleStroke"
  | .visible => "visible"
  | .painted => "painted"
  | .fill => "fill"
  | .stroke => "stroke"
  | .all => "all"
  | .none => "none"

instance : Keyword PointerEvents :=
  ⟨[.boundingBox, .visiblePainted, .visibleFill, .visibleStroke, .visible, .painted, .fill,
      .stroke, .all, .none], PointerEvents.css⟩

/-- The text of a choice reads back as the choice. -/
theorem PointerEvents.read?_css (k : PointerEvents) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-- Whether an element is drawn: `visibility`. -/
inductive Visibility where
  | visible | hidden | collapse
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a visibility. -/
def Visibility.css : Visibility → String
  | .visible => "visible"
  | .hidden => "hidden"
  | .collapse => "collapse"

instance : Keyword Visibility := ⟨[.visible, .hidden, .collapse], Visibility.css⟩

/-- The text of a visibility reads back as the visibility. -/
theorem Visibility.read?_css (k : Visibility) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-! ## Definitions that are referenced -/

/-- The coordinate system of a definition's own numbers: user space where it is referenced, or
fractions of the box of the element that refers to it. -/
inductive Units where
  | userSpaceOnUse | objectBoundingBox
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a coordinate system. -/
def Units.css : Units → String
  | .userSpaceOnUse => "userSpaceOnUse"
  | .objectBoundingBox => "objectBoundingBox"

instance : Keyword Units := ⟨[.userSpaceOnUse, .objectBoundingBox], Units.css⟩

/-- The text of a coordinate system reads back as it. -/
theorem Units.read?_css (k : Units) : Keyword.read? k.css = some k := by cases k <;> rfl

/-- What a gradient paints outside its two ends: `spreadMethod`. -/
inductive SpreadMethod where
  | pad | reflect | «repeat»
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a method. -/
def SpreadMethod.css : SpreadMethod → String
  | .pad => "pad"
  | .reflect => "reflect"
  | .«repeat» => "repeat"

instance : Keyword SpreadMethod := ⟨[.pad, .reflect, .«repeat»], SpreadMethod.css⟩

/-- The text of a method reads back as the method. -/
theorem SpreadMethod.read?_css (k : SpreadMethod) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-- What a marker's own numbers count: widths of the stroke it stands on, or user units. -/
inductive MarkerUnits where
  | strokeWidth | userSpaceOnUse
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a marker's units. -/
def MarkerUnits.css : MarkerUnits → String
  | .strokeWidth => "strokeWidth"
  | .userSpaceOnUse => "userSpaceOnUse"

instance : Keyword MarkerUnits := ⟨[.strokeWidth, .userSpaceOnUse], MarkerUnits.css⟩

/-- The text of a marker's units reads back as them. -/
theorem MarkerUnits.read?_css (k : MarkerUnits) : Keyword.read? k.css = some k := by
  cases k <;> rfl

/-- How a marker is turned: along the path, along the path and reversed at its start, or by a
fixed angle in degrees. It is no closed set, so it has a text and no `Keyword`. -/
inductive Orient where
  | auto
  | autoStartReverse
  | angle (degrees : Decimal)
  deriving DecidableEq, Repr, Inhabited

/-- What a mask reads of its content: its luminance, or its alpha. -/
inductive MaskType where
  | luminance | alpha
  deriving DecidableEq, Repr, Inhabited

/-- The keyword of a mask's reading. -/
def MaskType.css : MaskType → String
  | .luminance => "luminance"
  | .alpha => "alpha"

instance : Keyword MaskType := ⟨[.luminance, .alpha], MaskType.css⟩

/-- The text of a mask's reading reads back as it. -/
theorem MaskType.read?_css (k : MaskType) : Keyword.read? k.css = some k := by cases k <;> rfl

/-! ## Attributes of any element -/

namespace SvgAttr

variable {t : Tag}

/-- `stroke-linecap`. -/
def strokeLinecap (cap : LineCap) : SvgAttr t := .attr .stroke_linecap cap.css

/-- `stroke-linejoin`. -/
def strokeLinejoin (join : LineJoin) : SvgAttr t := .attr .stroke_linejoin join.css

/-- `stroke-miterlimit`, a number. -/
def strokeMiterlimit (limit : Decimal) : SvgAttr t := .attr .stroke_miterlimit (numberText limit)

/-- `stroke-dashoffset`, a number of user units. -/
def strokeDashoffset (offset : Decimal) : SvgAttr t :=
  .attr .stroke_dashoffset (numberText offset)

/-- `fill-rule`. -/
def fillRule (rule : FillRule) : SvgAttr t := .attr .fill_rule rule.css

/-- `clip-rule`: the rule of a shape inside a `clipPath`. -/
def clipRule (rule : FillRule) : SvgAttr t := .attr .clip_rule rule.css

/-- `paint-order`: the layers in the order they are painted, the rest after them in their
usual order. No layer is `normal`. -/
def paintOrder (layers : List PaintLayer) : SvgAttr t :=
  .attr .paint_order (if layers.isEmpty then "normal" else " ".intercalate (layers.map (·.css)))

/-- `vector-effect`. -/
def vectorEffect (effect : VectorEffect) : SvgAttr t := .attr .vector_effect effect.css

/-- `font-style`. -/
def fontStyle (style : FontStyle) : SvgAttr t := .attr .font_style style.css

/-- `dominant-baseline`. -/
def dominantBaseline (baseline : DominantBaseline) : SvgAttr t :=
  .attr .dominant_baseline baseline.css

/-- `pointer-events`. -/
def pointerEvents (events : PointerEvents) : SvgAttr t := .attr .pointer_events events.css

/-- `visibility`. -/
def visibility (v : Visibility) : SvgAttr t := .attr .visibility v.css

/-- `gradientUnits`, on a gradient. -/
def gradientUnits (units : Units) : SvgAttr t := .attr .gradientUnits units.css

/-- `spreadMethod`, on a gradient. -/
def spreadMethod (method : SpreadMethod) : SvgAttr t := .attr .spreadMethod method.css

/-- `maskUnits`: the coordinate system of a mask's own box. -/
def maskUnits (units : Units) : SvgAttr t := .attr .maskUnits units.css

/-- `maskContentUnits`: the coordinate system of what stands in a mask. -/
def maskContentUnits (units : Units) : SvgAttr t := .attr .maskContentUnits units.css

/-- `mask-type`. -/
def maskType (type : MaskType) : SvgAttr t := .attr .mask_type type.css

/-- `clipPathUnits`, on a `clipPath`. -/
def clipPathUnits (units : Units) : SvgAttr t := .attr .clipPathUnits units.css

/-- `filterUnits`: the coordinate system of a filter's own box. -/
def filterUnits (units : Units) : SvgAttr t := .attr .filterUnits units.css

/-- `primitiveUnits`: the coordinate system of the numbers of a filter's primitives. -/
def primitiveUnits (units : Units) : SvgAttr t := .attr .primitiveUnits units.css

/-- `patternUnits`, on a `pattern`. -/
def patternUnits (units : Units) : SvgAttr t := .attr .patternUnits units.css

/-- `patternContentUnits`, on a `pattern`. -/
def patternContentUnits (units : Units) : SvgAttr t := .attr .patternContentUnits units.css

/-- `markerUnits`, on a `marker`. -/
def markerUnits (units : MarkerUnits) : SvgAttr t := .attr .markerUnits units.css

end SvgAttr

/-- The text of a marker's turning: a keyword, or a number of degrees. -/
def Orient.css : Orient → String
  | .auto => "auto"
  | .autoStartReverse => "auto-start-reverse"
  | .angle degrees => SvgAttr.numberText degrees

/-- `orient`, on a `marker`. -/
def SvgAttr.orient {t : Tag} (o : Orient) : SvgAttr t := .attr .orient o.css

end Whatwg.Html
