import Aesop

/-!
# Whatwg.Auto.RuleSets

Owner: the named Aesop rule banks of this package (owner direction of 2026-10-11, ruling R-S10
of `COORDINATION.md`). Proof search here is `aesop`, used as lean4-effect4 uses it: a lemma is
registered in the bank that fits, and a proof asks for a bank by name,
`aesop (rule_sets := [Whatwg.Mask])`. Nothing lands in the `default` rule set, which every
call pays for.

This module only declares the banks. A bank's registrations are in a law module of its own,
and no module of definitions imports this one: a program that imports the definitions of this
package then reaches Lean alone, and links no proof search (slice S16 of
`docs/SVG-PACKAGE-PLAN.md`, ruling SV-91). Each bank lands with a theorem that closes only
with its clause and a fixture that omits the clause (`WhatwgTest/Auto/Banks.lean`). A bank with
no rule is deleted, and it returns with the lemma that needs it.

- `Whatwg.Mask`: membership in a mask as a homomorphism into `Bool`. Its rules and its
  theorem are in `Whatwg/Svg/Data/Mask/Laws.lean`.
- `Whatwg.Syn`: a description of typed parts prints every value, one rule per form of a
  description, and the totality of each description that a grammar names. Its rules and its
  theorem are in `Whatwg/Svg/Value/Bank.lean`. The grammars prove their own totality by a
  term, with no search, since each is a definition that a consumer imports.

The declaration registers one environment extension and one simp extension per bank. It runs
no proof and states no law.
-/

declare_aesop_rule_sets [Whatwg.Mask, Whatwg.Syn]