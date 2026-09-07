import Whatwg.Streams.Data.Queue
import Whatwg.WebIdl.Exceptions

/-!
# Shared exception reasons

Owner: `READABLE-PG-DEFAULT`, representation edge and ruling P3-R2.
`op.readable-stream-default-controller-enqueue` creates fresh RangeErrors;
`op.readable-stream-error` retains the exact stored reason. Allocation identities
are first-order data. The global allocation-supply embedding remains open.
-/

namespace Whatwg.Streams.Boundary

/-- Modeled exception objects carry allocation identities; foreign reasons retain their data. -/
inductive Exception (ε : Type) where
  | rangeError (id : Nat)
  | typeError (id : Nat)
  | foreign (reason : ε)
  deriving DecidableEq, Repr

namespace Exception

/-- P3-R2: embed the P3 error kind at the identity allocated by the consuming calculus. -/
def ofRangeError {ε : Type} (id : Nat) : Data.RangeError → Exception ε
  | .rangeError => .rangeError id

/-- P3-R2: the retraction forgets identity, retaining only P3's error-kind view. -/
def toRangeError {ε : Type} : Exception ε → Option Data.RangeError
  | .rangeError _ => some .rangeError
  | _ => none

/-- P3-R2 retraction, contributing to the M1 reason representation. -/
theorem toRangeError_ofRangeError {ε : Type} (id : Nat) (e : Data.RangeError) :
    toRangeError (ofRangeError (ε := ε) id e) = some e := by cases e; rfl

/-- The modeled TypeError constructor does not enter P3's RangeError view. -/
theorem toRangeError_typeError {ε : Type} (id : Nat) :
    toRangeError (.typeError id : Exception ε) = none := rfl

/-- A foreign reason is not classified by its host spelling. -/
theorem toRangeError_foreign {ε : Type} (e : ε) :
    toRangeError (.foreign e) = none := rfl

/-- `op.readable-stream-default-controller-enqueue`: allocation identity is retained. -/
theorem ofRangeError_eq {ε : Type} (id : Nat) :
    ofRangeError (ε := ε) id .rangeError = .rangeError id := rfl

/-- Distinct allocations remain distinct reasons under M1 and M2. -/
theorem rangeError_eq_iff {ε : Type} (left right : Nat) :
    (.rangeError left : Exception ε) = .rangeError right ↔ left = right := by simp

/-- TypeError identities are likewise retained by the shared reason carrier. -/
theorem typeError_eq_iff {ε : Type} (left right : Nat) :
    (.typeError left : Exception ε) = .typeError right ↔ left = right := by simp

/-! ## `PROMISE-PG-FIRST` part C: the Web IDL exception embedding (R-P14)

`E-59` (generalize), `E-60`, `E-61` (keep). This type is *not* re-pointed: its two
identity-bearing constructors and its `foreign` escape stay exactly as
`READABLE-PG-DEFAULT` froze them, so the 69 dependent theorems in eight files are
unchanged by construction. A `move` would break every `.rangeError id` among them,
because the general constructor takes a kind as well as an identity; that is
WS-PROM-CE-017. The relation to the general type is the additive pair below. All five
laws are mask M1. -/

/-- `E-59`: the embedding into the five-kind Web IDL universe, preserving the model
allocation identity. -/
def toWebIdl {ε : Type} : Exception ε → Whatwg.WebIdl.Exceptions.Exception ε
  | .rangeError id =>
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.rangeError id
  | .typeError id =>
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.typeError id
  | .foreign reason => Whatwg.WebIdl.Exceptions.Exception.foreign reason

/-- `E-59`: the retraction, partial because Streams models two of the five simple kinds
and no `DOMException` name. -/
def ofWebIdl {ε : Type} : Whatwg.WebIdl.Exceptions.Exception ε → Option (Exception ε)
  | .simple Whatwg.WebIdl.Exceptions.Simple.rangeError id => some (.rangeError id)
  | .simple Whatwg.WebIdl.Exceptions.Simple.typeError id => some (.typeError id)
  | .simple _ _ => none
  | .domException _ _ => none
  | .foreign reason => some (.foreign reason)

/-- Mask M1. -/
theorem toWebIdl_rangeError {ε : Type} (id : Nat) :
    toWebIdl (.rangeError id : Exception ε) =
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.rangeError id := rfl

/-- Mask M1. -/
theorem toWebIdl_typeError {ε : Type} (id : Nat) :
    toWebIdl (.typeError id : Exception ε) =
      Whatwg.WebIdl.Exceptions.Exception.simple
        Whatwg.WebIdl.Exceptions.Simple.typeError id := rfl

/-- A foreign reason crosses unchanged and stays unclassified. Mask M1. -/
theorem toWebIdl_foreign {ε : Type} (r : ε) :
    toWebIdl (.foreign r) = Whatwg.WebIdl.Exceptions.Exception.foreign r := rfl

/-- The retraction recovers the Streams reason exactly. Mask M1. -/
theorem ofWebIdl_toWebIdl {ε : Type} (e : Exception ε) : ofWebIdl (toWebIdl e) = some e := by
  cases e <;> rfl

/-- R-P14: a Web IDL exception without an allocation identity cannot host the
nested-size-callback distinctness witnesses, so the embedding is injective. Mask M1. -/
theorem toWebIdl_injective {ε : Type} (left right : Exception ε) :
    toWebIdl left = toWebIdl right → left = right := by
  intro h
  have := congrArg ofWebIdl h
  rw [ofWebIdl_toWebIdl, ofWebIdl_toWebIdl] at this
  exact Option.some.inj this

/-- `E-60` (keep): P3-R2's embedding, read through the Web IDL universe, is
`op.to-create-a-simple-exception` at the identity the consuming calculus allocated.
Mask M1. -/
theorem toWebIdl_ofRangeError {ε : Type} (id : Nat) (e : Data.RangeError) :
    toWebIdl (ofRangeError (ε := ε) id e) =
      Whatwg.WebIdl.Exceptions.createSimple
        Whatwg.WebIdl.Exceptions.Simple.rangeError id := by
  cases e; rfl

end Exception
end Whatwg.Streams.Boundary
