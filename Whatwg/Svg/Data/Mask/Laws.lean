import Whatwg.Auto.RuleSets
import Whatwg.Svg.Data.Mask

/-!
# Whatwg.Svg.Data.Mask.Laws

Owner: the rules of the Aesop bank `Whatwg.Mask` (`Whatwg/Auto/RuleSets.lean`; ruling R-S10 of
`COORDINATION.md`), and the law of a mask that the bank proves. The definitions and the laws of
membership are `Whatwg/Svg/Data/Mask.lean`, and the declarations here are in its namespace.

It is a module of its own because it imports the bank, and the bank imports Aesop. A program
that computes with a mask imports `Mask.lean`, which asks for no proof search, so its import
closure holds Lean alone. A proof that asks for the bank imports this module.

What this module holds:

- the registrations: the equations of membership as normalisation rules, and `mem_of_subset`
  as a forward rule;
- `Mask.mem_union_of_subset`, which closes only with the bank's clause.
  `WhatwgTest/Auto/Banks.lean` holds the control that omits the clause.
-/

namespace Whatwg.Svg.Data

namespace Mask

variable {α : Type} [Universe α]

/-! ## The bank `Whatwg.Mask`

The laws of membership are the rules of the Aesop bank `Whatwg.Mask`
(`Whatwg/Auto/RuleSets.lean`). The equations of membership are normalisation rules, and
`mem_of_subset` is a forward rule. A proof about members asks for the bank:
`aesop (rule_sets := [Whatwg.Mask])`. -/

attribute [aesop norm simp (rule_sets := [Whatwg.Mask])] mem_empty mem_union mem_inter mem_diff
  mem_single mem_insert mem_ofList mem_toList

attribute [aesop safe forward (rule_sets := [Whatwg.Mask])] mem_of_subset

/-- A member of a union stays one when the left set grows. The proof is the bank's: it closes
only with the clause (`WhatwgTest/Auto/Banks.lean` holds the fixture that omits it). -/
theorem mem_union_of_subset {m n k : Mask α} (h : m.subset n = true) {a : α}
    (ha : (m.union k).mem a = true) : (n.union k).mem a = true := by
  aesop (rule_sets := [Whatwg.Mask])

end Mask

end Whatwg.Svg.Data
