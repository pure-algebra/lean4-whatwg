import Whatwg.Auto.RuleSets
import Whatwg.Svg.Value.Number
import Whatwg.Svg.Value.Path
import Whatwg.Svg.Value.Points
import Whatwg.Svg.Value.ViewBox
import Whatwg.Svg.Value.Transform
import Whatwg.Svg.Value.Length
import Whatwg.Svg.Value.Extent
import Whatwg.Svg.Value.Lists

/-!
# Whatwg.Svg.Value.Bank

Owner: the rules of the Aesop bank `Whatwg.Syn` (`Whatwg/Auto/RuleSets.lean`; ruling R-S10 of
`COORDINATION.md`): a description of typed parts prints every value. The rules are theorems of
`Whatwg/Svg/Value/Grammar.lean` and of the eight grammar modules, and this module registers
them. It declares one theorem and no definition.

It is a module of its own because it imports the bank, and the bank imports Aesop. A program
that reads or prints a value imports a grammar module. A grammar module asks for no proof
search: it proves its totality by a term that follows its description, or reads it off the
totality of a description that holds the same parts. So its import closure holds Lean alone.
A proof that asks for the bank imports this module: `aesop (rule_sets := [Whatwg.Syn])`.

What the bank holds:

- one rule for each form of a description: `Syn.Total.eps`, `seq`, `alt`, `many` and `map`,
  and the derived forms `opt`, `many1`, `left`, `right` and `sepBy1`;
- the totality of each part that states a lemma: the separators, an exact text, a digit, a
  sign, a flag and a letter;
- the totality of each description that a grammar names, so that the search closes at a
  description which another one holds.

A part with no type of its own is an `abbrev` and states no lemma. The search reads through
it.

`Length.tail_total` is the theorem that closes only with the bank's clause.
`WhatwgTest/Auto/Banks.lean` holds the control of the bank, where the search without the
clause fails.
-/

namespace Whatwg.Svg.Value

/-! ## The forms of a description (`Grammar.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  Syn.Total.eps Syn.Total.seq Syn.Total.alt Syn.Total.many Syn.Total.map Syn.Total.opt
  Syn.Total.many1 Syn.Total.left Syn.Total.right Syn.Total.sepBy1

/-! ## The number and the separators (`Number.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  wsps_total commaWsp_total spaceSep_total commaSep_total lit_total digit_total natural_total
  plus_total sign_total exponentPart_total Magnitude.syn_total Decimal.syn_total Point.syn_total

/-! ## Path data (`Path.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  flag_total letter_total Arc.syn_total Command.syn_total Path.syn_total noneKeyword_total
  PathData.syn_total

/-! ## `points` and `viewBox` (`Points.lean`, `ViewBox.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])] Points.syn_total ViewBox.syn_total

/-! ## `transform` (`Transform.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  Transform.wsps_total Transform.argSep_total Transform.syn_total TransformList.sep_total
  TransformList.syn_total

/-! ## Lengths (`Length.lean`, `Extent.lean`, `Lists.lean`) -/

attribute [aesop safe apply (rule_sets := [Whatwg.Syn])]
  Length.letter_total Length.syn_total Extent.syn_total AutoExtent.syn_total Length.item_total

/-! ## A part that three descriptions hold -/

/-- What follows `fractional-constant` in a length prints every exponent and every unit.
`Length.syn`, `Length.item` and `Extent.core` hold this part, and no module states its
totality: the part is an `abbrev`. The proof is the bank's. It composes the rules of the forms
with `Length.letter_total`, `lit_total`, `sign_total` and `natural_total`, and it closes only
with the clause. A grammar module cannot cite this theorem, because it imports no proof search:
`Length.syn_total` says in place that the part is total, and `Length.item_total` and
`Extent.syn_total` read that off it. -/
theorem Length.tail_total : Length.tail.Total := by
  aesop (rule_sets := [Whatwg.Syn])

end Whatwg.Svg.Value
