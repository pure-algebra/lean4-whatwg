import Whatwg.Svg

/-!
# WhatwgTest.Auto.Banks

The fixtures of the named Aesop rule banks (`Whatwg/Auto/RuleSets.lean`; ruling R-S10 of
`COORDINATION.md`). A bank lands with a theorem that closes only with its clause. This battery
holds the control for each bank: the same goal, where the search without the clause fails and
the search with it closes.

A line here is a control of the bank, not of the law: the law is the theorem beside the bank's
rules, in the bank's law module, and this module restates none.
-/

namespace WhatwgTest.Auto.Banks

open Whatwg.Svg.Data

/-! ## `Whatwg.Mask` -/

-- Control: the goal of `Mask.mem_union_of_subset`. The default rule set does not know the
-- laws of membership, so the search fails without the clause and closes with it.
example {α : Type} [Universe α] {m n k : Mask α} (h : m.subset n = true) {a : α}
    (ha : (m.union k).mem a = true) : (n.union k).mem a = true := by
  fail_if_success aesop
  aesop (rule_sets := [Whatwg.Mask])

/-! ## `Whatwg.Syn` -/

open Whatwg.Svg.Value in
-- Control: a description of typed parts, such as the one whose totality `Decimal.syn_total`
-- states by a term. The default rule set does not know that each form of a description keeps
-- totality, so the search fails without the clause and closes with it. The bank's own theorem
-- is `Length.tail_total` of `Whatwg/Svg/Value/Bank.lean`.
example : (Syn.seq sign.opt natural).Total := by
  fail_if_success aesop
  aesop (rule_sets := [Whatwg.Syn])

end WhatwgTest.Auto.Banks