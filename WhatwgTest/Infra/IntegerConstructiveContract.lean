import Lean
import Lean.Util.CollectAxioms
import Whatwg.Infra.Primitive.Integer

/-!
Breaker-owned integer constructive proof contract, frozen before proof-term repair.
Authority: `docs/INFRA-INTEGER-CONSTRUCTIVE.md`.
Packet and retained witness: `test/contracts/infra-integer-constructive.contract.md`,
`INFRA-INTEGER-CE-001`.

All nine existing carrier aliases and universally quantified range statements remain fixed.
The actual transitive axiom set of each named range proof must be contained in
`[propext, Quot.sound]`. This local receipt does not establish repository-wide choice removal.
-/

set_option autoImplicit false

namespace WhatwgTest.Infra.IntegerConstructiveContract

-- Definitional equality fixes the existing native carrier views without adding replacement types.
#check (rfl : Whatwg.Infra.Unsigned8 = UInt8)
#check (rfl : Whatwg.Infra.Unsigned16 = UInt16)
#check (rfl : Whatwg.Infra.Unsigned32 = UInt32)
#check (rfl : Whatwg.Infra.Unsigned64 = UInt64)
#check (rfl : Whatwg.Infra.Unsigned128 = BitVec 128)
#check (rfl : Whatwg.Infra.Signed8 = Int8)
#check (rfl : Whatwg.Infra.Signed16 = Int16)
#check (rfl : Whatwg.Infra.Signed32 = Int32)
#check (rfl : Whatwg.Infra.Signed64 = Int64)

#check (@Whatwg.Infra.Unsigned8.inRange :
  (x : Whatwg.Infra.Unsigned8) → 0 ≤ x.toNat ∧ x.toNat ≤ 255)
#check (@Whatwg.Infra.Unsigned16.inRange :
  (x : Whatwg.Infra.Unsigned16) → 0 ≤ x.toNat ∧ x.toNat ≤ 65535)
#check (@Whatwg.Infra.Unsigned32.inRange :
  (x : Whatwg.Infra.Unsigned32) → 0 ≤ x.toNat ∧ x.toNat ≤ 4294967295)
#check (@Whatwg.Infra.Unsigned64.inRange :
  (x : Whatwg.Infra.Unsigned64) → 0 ≤ x.toNat ∧ x.toNat ≤ 18446744073709551615)
#check (@Whatwg.Infra.Unsigned128.inRange :
  (x : Whatwg.Infra.Unsigned128) →
    0 ≤ x.toNat ∧ x.toNat ≤ 340282366920938463463374607431768211455)
#check (@Whatwg.Infra.Signed8.inRange :
  (x : Whatwg.Infra.Signed8) → -128 ≤ x.toInt ∧ x.toInt ≤ 127)
#check (@Whatwg.Infra.Signed16.inRange :
  (x : Whatwg.Infra.Signed16) → -32768 ≤ x.toInt ∧ x.toInt ≤ 32767)
#check (@Whatwg.Infra.Signed32.inRange :
  (x : Whatwg.Infra.Signed32) → -2147483648 ≤ x.toInt ∧ x.toInt ≤ 2147483647)
#check (@Whatwg.Infra.Signed64.inRange :
  (x : Whatwg.Infra.Signed64) → -9223372036854775808 ≤ x.toInt ∧ x.toInt ≤ 9223372036854775807)

-- Inspect actual compiled declarations, including their types and generated proof dependencies.
-- Print every transitive receipt before rejecting all offending declaration/axiom pairs together.
open Lean Elab Command in
run_cmd do
  let declarations : Array Name := #[
    ``Whatwg.Infra.Unsigned8.inRange,
    ``Whatwg.Infra.Unsigned16.inRange,
    ``Whatwg.Infra.Unsigned32.inRange,
    ``Whatwg.Infra.Unsigned64.inRange,
    ``Whatwg.Infra.Unsigned128.inRange,
    ``Whatwg.Infra.Signed8.inRange,
    ``Whatwg.Infra.Signed16.inRange,
    ``Whatwg.Infra.Signed32.inRange,
    ``Whatwg.Infra.Signed64.inRange]
  let allowed : Array Name := #[``propext, ``Quot.sound]
  let mut failures : Array String := #[]
  for declaration in declarations do
    let axioms ← Lean.collectAxioms declaration
    logInfo m!"INFRA-INTEGER-CE-001 axioms {declaration}: {axioms}"
    for axiomName in axioms do
      if !allowed.contains axiomName then
        failures := failures.push s!"{declaration} reaches {axiomName}"
  if !failures.isEmpty then
    let detail := String.intercalate "; " failures.toList
    throwError m!"INFRA-INTEGER-CE-001 constructive ceiling failed: {detail}; allowed: {allowed}"
  logInfo "INFRA-INTEGER-CE-001: all nine range proofs meet [propext, Quot.sound]"

end WhatwgTest.Infra.IntegerConstructiveContract
