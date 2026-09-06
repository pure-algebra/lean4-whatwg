import Lean
import Lean.Util.CollectAxioms
import Whatwg.Infra.Text.Scalar

/-!
Breaker-owned constructive scalar/Char contract, frozen before proof-term repair.
Authority: `docs/INFRA-SCALAR-ASSURANCE.md`.
Packet and retained witness: `test/contracts/infra-scalar-constructive.contract.md`,
`INFRA-SCALAR-CE-001`.

The exact existing signatures remain fixed. The actual transitive axiom set of every listed
declaration must be contained in `[propext, Quot.sound]`. This local trust target does not
change the repository-wide ceiling or assert a corresponding result for string adapters.
-/

set_option autoImplicit false

namespace WhatwgTest.Infra.ScalarConstructiveContract

#check (@Whatwg.Infra.CodePoint.char_toNat_le : (c : Char) → c.toNat ≤ 0x10FFFF)
#check (@Whatwg.Infra.CodePoint.ofChar : Char → Whatwg.Infra.CodePoint)
#check (@Whatwg.Infra.CodePoint.ofChar_isSurrogate :
  (c : Char) → (Whatwg.Infra.CodePoint.ofChar c).isSurrogate = false)
#check (@Whatwg.Infra.ScalarValue.isValidChar :
  (s : Whatwg.Infra.ScalarValue) → Nat.isValidChar s.val.val)
#check (@Whatwg.Infra.ScalarValue.toChar : Whatwg.Infra.ScalarValue → Char)
#check (@Whatwg.Infra.ScalarValue.ofChar : Char → Whatwg.Infra.ScalarValue)
#check (@Whatwg.Infra.ScalarValue.toNat_ofNatAux :
  (n : Nat) → (h : Nat.isValidChar n) → (Char.ofNatAux n h).toNat = n)
#check (@Whatwg.Infra.ScalarValue.ofChar_toChar :
  (s : Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.ScalarValue.ofChar (Whatwg.Infra.ScalarValue.toChar s) = s)
#check (@Whatwg.Infra.ScalarValue.toChar_ofChar :
  (c : Char) → Whatwg.Infra.ScalarValue.toChar (Whatwg.Infra.ScalarValue.ofChar c) = c)

-- This command inspects the compiled declarations, including axioms reachable through their
-- types and proof bodies. It prints every receipt before rejecting all offending names together.
open Lean Elab Command in
run_cmd do
  let declarations : Array Name := #[
    ``Whatwg.Infra.CodePoint.char_toNat_le,
    ``Whatwg.Infra.CodePoint.ofChar,
    ``Whatwg.Infra.CodePoint.ofChar_isSurrogate,
    ``Whatwg.Infra.ScalarValue.isValidChar,
    ``Whatwg.Infra.ScalarValue.toChar,
    ``Whatwg.Infra.ScalarValue.ofChar,
    ``Whatwg.Infra.ScalarValue.toNat_ofNatAux,
    ``Whatwg.Infra.ScalarValue.ofChar_toChar,
    ``Whatwg.Infra.ScalarValue.toChar_ofChar]
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let mut failures : Array String := #[]
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    logInfo m!"INFRA-SCALAR-CE-001 axioms {declaration}: {axioms}"
    for axiomName in axioms do
      if !allowed.contains axiomName then
        failures := failures.push s!"{declaration} reaches {axiomName}"
  if !failures.isEmpty then
    let detail := String.intercalate "; " failures.toList
    throwError m!"INFRA-SCALAR-CE-001 constructive ceiling failed: {detail}; allowed: {allowed}"
  logInfo "INFRA-SCALAR-CE-001: all nine declarations meet [propext, Quot.sound]"

end WhatwgTest.Infra.ScalarConstructiveContract
