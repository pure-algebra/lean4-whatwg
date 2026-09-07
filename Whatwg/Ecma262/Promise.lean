import Whatwg.Ecma262.Jobs
import Whatwg.Infra

/-!
# ECMAScript promise objects

Owner: the Promise Objects clause of the pinned ES2026 source, at the first
packet surface `PROMISE-PG-FIRST` freezes
(`test/contracts/promise-first-packet.contract.md`).

Landed here: the promise state carrier (`E-01`, move), the settled-outcome and
callback-return carriers (`E-02`, `E-03`, move), promise identity (`E-14`,
`E-23`, generalize), the general promise table with its allocation, lookup,
settle and mark-handled operations (`E-13`..`E-15`, `E-18`..`E-23`,
generalize), the reaction records and the two reaction lists (`E-29`..`E-33`,
generalize; gap `G-01`), `TriggerPromiseReactions` with its order and
once-only laws (`G-01`), the capability record and the resolving functions
(`G-03`), and `PerformPromiseThen` with a result capability (`G-11`).

Still open, with their gap ids: the handled-bit consumer and
`HostPromiseRejectionTracker` (`G-02` remainder); `IsPromise` and the value
universe (`G-04`); thenable adoption and `NewPromiseResolveThenableJob`
(`G-05`); the Completion carrier beyond `Except` (`G-10`);
`Promise.prototype.then`/`catch`/`finally`, the four combinators, the
`Promise` constructor and the static resolve/reject helpers (`G-11`
remainder).

Layering (DB-11): this module imports `Whatwg.Ecma262.Jobs` and
`Whatwg.Infra`, and nothing else. The reason parameter stays free
(decision 2); `Whatwg.WebIdl.Exceptions` is the instantiation Streams uses.
-/

namespace Whatwg.Ecma262.Promise

/-! ## Part A — the moved carriers -/

/--
`slot.PromiseState` (2744957..2745252) fused with `slot.PromiseResult`
(2745263..2745619): the first-order promise-outcome view, with the three tags
the clause names. `E-01` (move) relocates
`Whatwg.Streams.Readable.PromiseState` here; two type parameters per R-P13,
because `E-22` (`Readable.State.readPromises`) already needs a non-unit value.
-/
inductive State (value reason : Type) where
  | pending
  | fulfilled (value : value)
  | rejected (reason : reason)
  deriving DecidableEq, Repr

/--
`op.fulfillpromise` (2695419..2696230) and `op.rejectpromise`
(2699323..2700252): the settled outcome a foreign callback's promise delivers,
with the value fixed to unit. `E-02` (move). One parameter, not two
(decision 12): `Readable.PullAnswer.fulfilled` takes no argument, and the
value-carrying settled outcome already exists as `Except reason value`.
-/
inductive Outcome (reason : Type) where
  | fulfilled
  | rejected (reason : reason)
  deriving DecidableEq, Repr

/--
The `[[PromiseState]]` of a returned promise observed at callback-return time,
before any reaction runs. `E-03` (move). Decision 6 keeps `State`, `Outcome`
and `Returned` distinct; their isomorphisms are bridging lemmas, not
identifications.
-/
inductive Returned (reason : Type) where
  | pending
  | settled (answer : Outcome reason)
  deriving DecidableEq, Repr

/--
The owner-qualified promise identity. P8a rename class "rename only":
`PromiseRef` becomes `Ref` and `PromiseRef.local` becomes `Ref.cell`, because
`local` is a Lean 4 keyword and cannot be a field name (§11 of the contract).
`E-14`, `E-23` (generalize) and decision 3 keep identities `Nat` with a
monotone cursor; Streams keeps bare `Nat` under a single-owner view until P8.
-/
structure Ref where
  owner : Nat
  cell : Nat
  deriving DecidableEq

/-! ## Part A — the general promise table -/

/--
One promise instance: its `[[PromiseState]]`/`[[PromiseResult]]` fusion and its
`slot.PromiseIsHandled` flag (2746322..2746637). Decision 9 puts `handled` in
the cell rather than in a separate identity list, which is what the slot says
and what `HostPromiseRejectionTracker` will need.
-/
structure Cell (value reason : Type) where
  state : State value reason
  handled : Bool
  deriving DecidableEq, Repr

/--
`clause.properties-of-promise-instances` (2744135..2746691) as an append-only
table over `Nat` identities with a monotone cursor. `E-13`..`E-15`,
`E-18`..`E-23` (generalize): `Writable.State.promises`/`nextPromise`/`handled`
and `Readable.State.readPromises`/`nextRead` are two instances of it at two
different value parameters.
-/
structure Table (value reason : Type) where
  entries : List (Nat × Cell value reason)
  next : Nat
  deriving DecidableEq, Repr

/-- The table before any promise is allocated. -/
def Table.empty {value reason : Type} : Table value reason := Table.mk [] 0

/-- `E-18` (generalize): the target of `Writable.lookupPromise`. -/
def Table.getCell {value reason : Type} (t : Table value reason) (id : Nat) :
    Option (Cell value reason) :=
  (t.entries.find? (fun e => e.1 == id)).map Prod.snd

/-- The promise state of an allocated identity, forgetting the handled flag. -/
def Table.get {value reason : Type} (t : Table value reason) (id : Nat) :
    Option (State value reason) :=
  (Table.getCell t id).map Cell.state

/-- `FulfillPromise` step 1 and `RejectPromise` step 1 assert exactly this. -/
def Table.isPending {value reason : Type} (t : Table value reason) (id : Nat) : Bool :=
  match Table.get t id with
  | some State.pending => true
  | _ => false

/--
`op.newpromisecapability` (2696238..2698770): allocate a fresh cell at the
cursor, retaining every earlier cell. `E-19` (generalize): the Streams
instance additionally appends a `.settled` trace event in two of its three
branches; the trace stays in Streams, so this allocates only.
-/
def Table.fresh {value reason : Type} (t : Table value reason)
    (outcome : State value reason) : Table value reason × Nat :=
  (Table.mk (t.entries ++ [(t.next, Cell.mk outcome false)]) (t.next + 1), t.next)

/--
`op.fulfillpromise` (2695419..2696230) and `op.rejectpromise`
(2699323..2700252). `E-20` (generalize) and decision 7: the total guarded
function, with the specification's assertion recovered as `settle_assert`.
A non-pending settle is the identity, which is what `settle_other` receipts.
-/
def Table.settle {value reason : Type} (t : Table value reason) (id : Nat)
    (result : Except reason value) : Table value reason :=
  if Table.isPending t id then
    Table.mk
      (t.entries.map (fun e =>
        if e.1 == id then
          (e.1, Cell.mk
            (match result with
              | .ok v => State.fulfilled v
              | .error r => State.rejected r) e.2.handled)
        else e))
      t.next
  else t

/--
`op.mark-a-promise-as-handled` (356060..356713). `E-21` (generalize): the
target of `Writable.markHandled`. `G-02` records that nothing reads the bit in
this packet, so the only laws are placement and idempotence.
-/
def Table.markHandled {value reason : Type} (t : Table value reason) (id : Nat) :
    Table value reason :=
  Table.mk
    (t.entries.map (fun e => if e.1 == id then (e.1, Cell.mk e.2.state true) else e))
    t.next

/-! ### Table equations — mask M1 -/

/-- The empty table allocates from zero. Mask M1. -/
theorem Table.empty_eq {value reason : Type} :
    (Table.empty : Table value reason) = Table.mk [] 0 := rfl

/-- Lookup is the first entry with a matching identity. Mask M1. -/
theorem Table.getCell_eq {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.getCell t id = (t.entries.find? (fun e => e.1 == id)).map Prod.snd := rfl

/-- The state view forgets the handled flag. Mask M1. -/
theorem Table.get_eq {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.get t id = (Table.getCell t id).map Cell.state := rfl

/-- The `Bool` and `Prop` faces of "still pending" agree. Mask M1. -/
theorem Table.isPending_iff {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.isPending t id = true ↔ Table.get t id = some State.pending := by
  unfold Table.isPending
  cases h : Table.get t id with
  | none => simp
  | some cell => cases cell <;> simp

/-- `E-13` risk: the table is append-only, and the three `freshPromise_*`
Streams receipts state this append shape verbatim. Mask M1. -/
theorem Table.fresh_eq {value reason : Type} (t : Table value reason)
    (outcome : State value reason) :
    Table.fresh t outcome =
      (Table.mk (t.entries ++ [(t.next, Cell.mk outcome false)]) (t.next + 1), t.next) := rfl

/-- Allocation returns the cursor it consumed. Mask M1. -/
theorem Table.fresh_id {value reason : Type} (t : Table value reason)
    (outcome : State value reason) : (Table.fresh t outcome).2 = t.next := rfl

/-- Allocation advances the cursor by one. Mask M1. -/
theorem Table.fresh_next {value reason : Type} (t : Table value reason)
    (outcome : State value reason) : (Table.fresh t outcome).1.next = t.next + 1 := rfl

/--
Retention: allocating never overwrites an earlier cell. This is what `E-43`
(`Writable.updateBackpressure` replaces a settled ready cell with a new one and
old references keep their outcomes) depends on. Mask M1.
-/
theorem Table.fresh_old {value reason : Type} (t : Table value reason)
    (outcome : State value reason) (id : Nat) :
    id ≠ t.next → Table.getCell (Table.fresh t outcome).1 id = Table.getCell t id := by
  intro hne
  have hfalse :
      ¬ ((fun (e : Nat × Cell value reason) => e.1 == id)
        (t.next, Cell.mk outcome false)) = true := by
    simp only [beq_iff_eq]
    exact fun h => hne h.symm
  show Option.map Prod.snd
      (List.find? (fun e => e.1 == id) (t.entries ++ [(t.next, Cell.mk outcome false)])) =
    Option.map Prod.snd (List.find? (fun e => e.1 == id) t.entries)
  rw [List.find?_append,
    List.find?_cons_of_neg (p := fun (e : Nat × Cell value reason) => e.1 == id) hfalse,
    List.find?_nil]
  cases List.find? (fun (e : Nat × Cell value reason) => e.1 == id) t.entries <;> rfl

/-- A fresh allocation is observable at the identity it consumed. Mask M1. -/
theorem Table.fresh_get {value reason : Type} (t : Table value reason)
    (outcome : State value reason) :
    Table.getCell t t.next = none →
      Table.get (Table.fresh t outcome).1 t.next = some outcome := by
  intro hnone
  have hfind :
      List.find? (fun (e : Nat × Cell value reason) => e.1 == t.next) t.entries = none := by
    cases hf : List.find? (fun (e : Nat × Cell value reason) => e.1 == t.next) t.entries with
    | none => rfl
    | some v => simp [Table.getCell, hf] at hnone
  have htrue :
      ((fun (e : Nat × Cell value reason) => e.1 == t.next)
        (t.next, Cell.mk outcome false)) = true := by
    simp
  show Option.map Cell.state (Option.map Prod.snd
      (List.find? (fun e => e.1 == t.next)
        (t.entries ++ [(t.next, Cell.mk outcome false)]))) = some outcome
  rw [List.find?_append, hfind,
    List.find?_cons_of_pos (p := fun (e : Nat × Cell value reason) => e.1 == t.next) htrue]
  rfl

/-! ### Settling: the guard, and the assertion as a side condition — mask M1 -/

/-- `E-20`: the pending branch, whose shape the Streams `settle_pending`
receipt states verbatim. Mask M1. -/
theorem Table.settle_pending {value reason : Type} (t : Table value reason) (id : Nat)
    (result : Except reason value) :
    Table.get t id = some State.pending →
      Table.settle t id result =
        Table.mk
          (t.entries.map (fun e =>
            if e.1 == id then
              (e.1, Cell.mk
                (match result with
                  | .ok v => State.fulfilled v
                  | .error r => State.rejected r) e.2.handled)
            else e))
          t.next := by
  intro h
  simp [Table.settle, (Table.isPending_iff t id).mpr h]

/-- Decision 7: a non-pending settle is the identity, never a failure. Mask M1. -/
theorem Table.settle_other {value reason : Type} (t : Table value reason) (id : Nat)
    (result : Except reason value) :
    Table.get t id ≠ some State.pending → Table.settle t id result = t := by
  intro h
  have : Table.isPending t id = false := by
    cases hp : Table.isPending t id with
    | false => rfl
    | true => exact absurd ((Table.isPending_iff t id).mp hp) h
  simp [Table.settle, this]

/-- Decision 7: the specification's assertion, recovered as a side condition
under the pending hypothesis. Mask M1. -/
theorem Table.settle_assert {value reason : Type} (t : Table value reason) (id : Nat)
    (result : Except reason value) :
    Table.get t id = some State.pending →
      Table.get (Table.settle t id result) id =
        some (match result with
          | .ok v => State.fulfilled v
          | .error r => State.rejected r) := by
  intro h
  -- The replacement preserves each entry's identity, so `find?` commutes with it.
  have key : ∀ (g : Cell value reason → Cell value reason)
      (l : List (Nat × Cell value reason)),
      List.find? (fun e => e.1 == id) (l.map (fun e => if e.1 == id then (e.1, g e.2) else e)) =
        (List.find? (fun e => e.1 == id) l).map (fun e => (e.1, g e.2)) := by
    intro g l
    induction l with
    | nil => rfl
    | cons e rest ih =>
        by_cases hb : (e.1 == id) = true
        · have hhead :
              ((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id := by
            rw [if_pos hb]; exact hb
          simp only [List.map_cons]
          rw [List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hb,
            if_pos hb]
          rfl
        · have hhead :
              ¬ (((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id) =
                true := by
            rw [if_neg hb]; exact hb
          simp only [List.map_cons]
          rw [List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hb, ih]
  rw [Table.settle_pending t id result h]
  simp only [Table.get, Table.getCell] at h ⊢
  rw [key (fun c => Cell.mk (match result with
    | .ok v => State.fulfilled v
    | .error r => State.rejected r) c.handled) t.entries]
  cases hf : List.find? (fun (e : Nat × Cell value reason) => e.1 == id) t.entries with
  | none => rw [hf] at h; simp at h
  | some v => rfl

/-- Settling never changes the handled flag. Mask M1. -/
theorem Table.settle_handled {value reason : Type} (t : Table value reason) (id : Nat)
    (result : Except reason value) :
    (Table.getCell (Table.settle t id result) id).map Cell.handled =
      (Table.getCell t id).map Cell.handled := by
  by_cases hp : Table.get t id = some State.pending
  · have key : ∀ (g : Cell value reason → Cell value reason)
        (l : List (Nat × Cell value reason)),
        List.find? (fun e => e.1 == id) (l.map (fun e => if e.1 == id then (e.1, g e.2) else e)) =
          (List.find? (fun e => e.1 == id) l).map (fun e => (e.1, g e.2)) := by
      intro g l
      induction l with
      | nil => rfl
      | cons e rest ih =>
          by_cases hb : (e.1 == id) = true
          · have hhead :
                ((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id := by
              rw [if_pos hb]; exact hb
            simp only [List.map_cons]
            rw [List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hb,
            if_pos hb]
            rfl
          · have hhead :
                ¬ (((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id) =
                  true := by
              rw [if_neg hb]; exact hb
            simp only [List.map_cons]
            rw [List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hb, ih]
    rw [Table.settle_pending t id result hp]
    simp only [Table.getCell]
    rw [key (fun c => Cell.mk (match result with
      | .ok v => State.fulfilled v
      | .error r => State.rejected r) c.handled) t.entries]
    cases List.find? (fun (e : Nat × Cell value reason) => e.1 == id) t.entries <;> rfl
  · rw [Table.settle_other t id result hp]

/-! ### The handled bit — mask M1 -/

/-- `E-21`: the placement law, whose Streams counterpart is `markHandled_eq`.
Mask M1. -/
theorem Table.markHandled_eq {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.markHandled t id =
      Table.mk
        (t.entries.map (fun e => if e.1 == id then (e.1, Cell.mk e.2.state true) else e))
        t.next := rfl

/-- Marking a promise handled twice marks it once. Mask M1. -/
theorem Table.markHandled_idem {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.markHandled (Table.markHandled t id) id = Table.markHandled t id := by
  simp only [Table.markHandled, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  by_cases hb : e.1 = id <;> simp [hb]

/-- `G-02`: nothing reads the bit in this packet, and marking does not change
the promise state. Mask M1. -/
theorem Table.markHandled_state {value reason : Type} (t : Table value reason) (id : Nat) :
    Table.get (Table.markHandled t id) id = Table.get t id := by
  have key : ∀ (g : Cell value reason → Cell value reason)
      (l : List (Nat × Cell value reason)),
      List.find? (fun e => e.1 == id) (l.map (fun e => if e.1 == id then (e.1, g e.2) else e)) =
        (List.find? (fun e => e.1 == id) l).map (fun e => (e.1, g e.2)) := by
    intro g l
    induction l with
    | nil => rfl
    | cons e rest ih =>
        by_cases hb : (e.1 == id) = true
        · have hhead :
              ((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id := by
            rw [if_pos hb]; exact hb
          simp only [List.map_cons]
          rw [List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_pos (p := fun (x : Nat × Cell value reason) => x.1 == id) hb,
            if_pos hb]
          rfl
        · have hhead :
              ¬ (((if e.1 == id then (e.1, g e.2) else e) : Nat × Cell value reason).1 == id) =
                true := by
            rw [if_neg hb]; exact hb
          simp only [List.map_cons]
          rw [List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hhead,
            List.find?_cons_of_neg (p := fun (x : Nat × Cell value reason) => x.1 == id) hb, ih]
  simp only [Table.get, Table.getCell, Table.markHandled]
  rw [key (fun c => Cell.mk c.state true) t.entries]
  cases List.find? (fun (e : Nat × Cell value reason) => e.1 == id) t.entries <;> rfl

end Whatwg.Ecma262.Promise
