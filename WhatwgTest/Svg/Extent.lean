import Whatwg.Svg.Value.Extent
import Whatwg.Svg.Value.Deterministic

/-!
# WhatwgTest.Svg.Extent

Readers, controls and finite evaluations of the two grammars of a length that is not negative
(debt D93 of `COORDINATION.md`; slice S5 and rulings SV-26 and SV-31 of
`docs/SVG-PACKAGE-PLAN.md`): `Whatwg/Svg/Value/Extent.lean`.

The first section replays the three property values that the sealed chapter
`vendor/w3c-svgwg-47e645ef/master/geometry.html` writes out: `0` and `auto`, the initial values
in the table after the paragraph `geometry-negative-values`, and `100%`, in the table under
`Sizing`. Every other text is made for the battery.

A reader applies a law of `Whatwg/Svg/Value/Grammar.lean`, of
`Whatwg/Svg/Value/Deterministic.lean` or of the module at a real value. A control shows where a
grammar or a law stops. Every other line is a finite evaluation: what one text reads as, or what
one value prints as.

What this battery does not claim: the fallback of the sealed text. The paragraph
`geometry-negative-values` treats a negative value as the initial value of its property. The
grammars refuse the text and put no value in its place, and the controls below show the refusal
alone.
-/

namespace WhatwgTest.Svg.Extent

open Whatwg.Svg.Value

/-! ## The sealed chapter's values -/

-- The table after `geometry-negative-values` writes the two initial values, `0` and `auto`.
#guard Extent.grammar.read "0".toList == some ⟨⟨0, 0⟩, .number⟩
#guard AutoExtent.grammar.read "auto".toList == some .auto

-- The table under `Sizing` writes `100%`, what `auto` is treated as on the outermost `svg`.
#guard AutoExtent.grammar.read "100%".toList == some (.extent ⟨⟨100, 0⟩, .percentage⟩)

/-! ## The one spelling of a value -/

-- An extent: the number as `Magnitude.grammar` spells it, and the mark after it in lower case
-- with nothing between. A number with no unit has no mark, and no spelling has a sign.
#guard Extent.grammar.print ⟨⟨10, 0⟩, .number⟩ == "10".toList
#guard Extent.grammar.print ⟨⟨15, -1⟩, .em⟩ == "1.5em".toList
#guard Extent.grammar.print ⟨⟨50, 0⟩, .percentage⟩ == "50%".toList
#guard Extent.grammar.print ⟨⟨0, 0⟩, .number⟩ == "0".toList

-- The keyword in lower case, and three of the extents again, with the same three texts.
#guard AutoExtent.grammar.print .auto == "auto".toList
#guard AutoExtent.grammar.print (.extent ⟨⟨10, 0⟩, .number⟩) == "10".toList
#guard AutoExtent.grammar.print (.extent ⟨⟨15, -1⟩, .em⟩) == "1.5em".toList
#guard AutoExtent.grammar.print (.extent ⟨⟨50, 0⟩, .percentage⟩) == "50%".toList

-- A value in user units, from the exact constructor of `Magnitude`.
#guard Extent.grammar.print (.user (.ofNat 40)) == "40".toList
#guard AutoExtent.grammar.print (.user (.ofNat 40)) == "40".toList

/-! ## What the readers take -/

-- A number with no unit, and a mark after a number.
#guard Extent.grammar.read "10".toList == some ⟨⟨10, 0⟩, .number⟩
#guard Extent.grammar.read "1.5em".toList == some ⟨⟨15, -1⟩, .em⟩
#guard Extent.grammar.read "50%".toList == some ⟨⟨50, 0⟩, .percentage⟩

-- A plus sign and white space at both ends are read and not kept.
#guard Extent.grammar.read "+10px".toList == some ⟨⟨10, 0⟩, .px⟩
#guard Extent.grammar.read " 10 ".toList == some ⟨⟨10, 0⟩, .number⟩

-- The same five texts at the other grammar, and zero: each is the extent.
#guard AutoExtent.grammar.read "10".toList == some (.extent ⟨⟨10, 0⟩, .number⟩)
#guard AutoExtent.grammar.read "1.5em".toList == some (.extent ⟨⟨15, -1⟩, .em⟩)
#guard AutoExtent.grammar.read "50%".toList == some (.extent ⟨⟨50, 0⟩, .percentage⟩)
#guard AutoExtent.grammar.read "+10px".toList == some (.extent ⟨⟨10, 0⟩, .px⟩)
#guard AutoExtent.grammar.read " 10 ".toList == some (.extent ⟨⟨10, 0⟩, .number⟩)
#guard AutoExtent.grammar.read "0".toList == some (.extent ⟨⟨0, 0⟩, .number⟩)

-- The keyword in either letter case, letter by letter, and with white space at both ends: the
-- resolution of the annotation in the section `syntax` of `types.html`.
#guard AutoExtent.grammar.read "AUTO".toList == some .auto
#guard AutoExtent.grammar.read " Auto ".toList == some .auto
#guard AutoExtent.grammar.read "aUtO".toList == some .auto

-- The tail is that of a length: an exponent, a mark in capitals, and the `e` that opens either.
#guard Extent.grammar.read "1e3".toList == some ⟨⟨1, 3⟩, .number⟩
#guard Extent.grammar.read "1em".toList == some ⟨⟨1, 0⟩, .em⟩
#guard Extent.grammar.read "1E2PX".toList == some ⟨⟨1, 2⟩, .px⟩

/-! ## Where the grammars stop -/

-- A minus sign, before a zero too. Zero is not negative, and the readers refuse `-0`: a
-- description cannot read a sign and then decide by the value.
#guard !Extent.grammar.check "-1".toList && !AutoExtent.grammar.check "-1".toList
#guard !Extent.grammar.check "-0".toList && !AutoExtent.grammar.check "-0".toList
#guard !Extent.grammar.check "-1px".toList && !AutoExtent.grammar.check "-1px".toList

-- Control: the length grammar reads the three texts. The refusal is the sign's, and no other
-- part of the text earns it.
#guard Length.grammar.read "-1".toList == some ⟨⟨-1, 0⟩, .number⟩
#guard Length.grammar.read "-0".toList == some ⟨⟨0, 0⟩, .number⟩
#guard Length.grammar.read "-1px".toList == some ⟨⟨-1, 0⟩, .px⟩

-- The keyword is no extent, in either letter case.
#guard !Extent.grammar.check "auto".toList && !Extent.grammar.check "AUTO".toList

-- White space between the number and the mark. The reader takes `10` as a number with no unit
-- and leaves the mark, so the whole text is refused.
#guard !Extent.grammar.check "10 px".toList && !AutoExtent.grammar.check "10 px".toList
#guard Extent.syn.read "10 px".toList == some (⟨⟨10, 0⟩, .number⟩, "px".toList)

-- A unit that the table of `SVGLength` does not name.
#guard !Extent.grammar.check "10rem".toList && !AutoExtent.grammar.check "10rem".toList

-- The keyword and then a length. The reader takes the keyword and leaves the length.
#guard !AutoExtent.grammar.check "auto 10".toList
#guard AutoExtent.syn.read "auto 10".toList == some (.auto, "10".toList)

-- A part of the keyword, the keyword with a mark, and the keyword after a plus sign.
#guard !AutoExtent.grammar.check "aut".toList && !AutoExtent.grammar.check "autopx".toList
#guard !AutoExtent.grammar.check "+auto".toList

-- The empty text, and white space alone.
#guard !Extent.grammar.check "".toList && !AutoExtent.grammar.check "".toList
#guard !Extent.grammar.check " ".toList && !AutoExtent.grammar.check " ".toList

/-! ## One character decides -/

-- Both descriptions pass the test of `Whatwg/Svg/Value/Deterministic.lean`, so its bridge
-- applies to each.
#guard Extent.syn.deterministic && AutoExtent.syn.deterministic

-- Reader of the check law: the check of `auto` or an extent decides the language of the
-- description's expression.
example (s : List Char) :
    AutoExtent.grammar.check s = true ↔ AutoExtent.syn.erase.Matches s :=
  AutoExtent.grammar.check_iff_matches (by decide +kernel) s

-- Reader of the check law from the reader to the language: a refusal by the reader proves that
-- the language has no such text. `-0` is no text of an extent.
example : ¬ Extent.syn.erase.Matches ['-', '0'] := fun h =>
  absurd ((Extent.grammar.check_iff_matches (by decide +kernel) _).mpr h) (by decide +kernel)

-- Reader of the head law: no text of an extent without its white space opens with a minus
-- sign, whatever follows the sign.
example (t : List Char) : ¬ Extent.core.erase.Matches ('-' :: t) := fun h =>
  absurd ((Syn.matches_head Extent.core _ h).2 '-' t rfl) (by decide +kernel)

/-! ## The laws at these grammars -/

-- Reader of V1: every value reads back from its spelling. The value here is not a literal.
example (m : Magnitude) (u : LengthUnit) :
    AutoExtent.grammar.read (AutoExtent.grammar.print (.extent ⟨m, u⟩)) = some (.extent ⟨m, u⟩) :=
  AutoExtent.grammar.read_print _

-- Reader of the embedding at the two constructors: the keyword and a size in user units never
-- have one spelling.
example (m : Magnitude) : AutoExtent.grammar.print .auto ≠ AutoExtent.grammar.print (.user m) :=
  fun h => nomatch AutoExtent.grammar.print_injective h

-- Control: the reader is no embedding. Capitals, a plus sign and white space are read and not
-- printed, and the printer writes its own spelling back: the digits `15` at exponent zero.
#guard AutoExtent.grammar.read " AUTO ".toList == AutoExtent.grammar.read "auto".toList
#guard (AutoExtent.grammar.read " AUTO ".toList).map AutoExtent.grammar.print
  == some "auto".toList
#guard (AutoExtent.grammar.read " +1.5E1PX ".toList).map AutoExtent.grammar.print
  == some "15px".toList

/-! ## An extent is a length -/

-- Reader of `Extent.print_eq_length` at a value that is no literal: a size in user units has
-- the text of the length in user units.
example (m : Magnitude) :
    Extent.grammar.print (.user m) = Length.grammar.print (.user ⟨m.mantissa, m.exponent⟩) :=
  Extent.print_eq_length _

-- Reader of that law and of V1 together: the length grammar reads the text of an extent as its
-- length.
example (e : Extent) : Length.grammar.read (Extent.grammar.print e) = some e.toLength := by
  rw [Extent.print_eq_length]
  exact Length.grammar.read_print _

-- The two readers agree on a spelling that the printer does not write. No theorem says so.
#guard (Extent.grammar.read " +1.5E1PX ".toList).map Extent.toLength
  == Length.grammar.read " +1.5E1PX ".toList

/-! ## A size from a number -/

-- A numeral is that many user units, at both types.
#guard (320 : AutoExtent) == .user (.ofNat 320) && (5 : Extent) == .user (.ofNat 5)
#guard String.ofList (AutoExtent.grammar.print 320) == "320"

-- A size from an integer: a negative one is no value (ruling SV-35).
#guard AutoExtent.ofInt? 30 == some 30 && AutoExtent.ofInt? (-3) == none

end WhatwgTest.Svg.Extent
