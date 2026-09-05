import Whatwg.Streams.Data.Queue

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

end Exception
end Whatwg.Streams.Boundary
