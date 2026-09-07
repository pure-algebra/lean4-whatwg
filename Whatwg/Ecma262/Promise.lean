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

/-! ## Part A/B — reactions and registration

`E-29`..`E-33`, `E-37`, `E-38` (generalize) supply the extraction; `G-01`
supplies the gap. Decision 8 splits the one Streams subscription list into the
two ES2026 lists, with `Reactions.registered` as the one-list view Streams
instantiates. -/

/--
`field.promisereaction-records.Type` (2691815..2692138). `Reaction.kind` is new
content under `G-01`, not a rename: Streams has no `[[Type]]` tag.
-/
inductive ReactionType where
  | fulfill
  | reject
  deriving DecidableEq, Repr

/--
P8a rename class "rename only": `Semantics.Ordering.ObserverPhase` becomes
`ReactionPhase` with its four constructors unchanged. `E-36` (keep) fixes that
`Writable.OperationPhase` is *not* unified with it in this packet: its fourteen
receipts guard `acceptAnswer` and `attachSink`.
-/
inductive ReactionPhase where
  | waiting
  | queued (job : Nat)
  | running (job : Nat)
  | done
  deriving DecidableEq, Repr

/--
`record.promisereaction-records` (2690445..2692671). `E-29` (generalize) and
P8a `Registration` (rename only). `handler` is `Option body` because
`field.promisereaction-records.Handler` (2692151..2692611) admits an empty
handler, which is what Web IDL's one-sided "upon fulfillment" and "upon
rejection" register. `E-29` risk: `deriving Repr` only — the general record
must not gain `DecidableEq`, or `Transform.State` stops being `Repr`-only in
the same way.
-/
structure Reaction (body : Type) where
  id : Nat
  promise : Nat
  kind : ReactionType
  handler : Option body
  phase : ReactionPhase
  deriving Repr

/--
`slot.PromiseFulfillReactions` (2745630..2745966) and
`slot.PromiseRejectReactions` (2745977..2746311): the two reaction lists
Streams does not have, under `G-01`, with one shared registration cursor.
-/
structure Reactions (body : Type) where
  fulfill : List (Reaction body)
  reject : List (Reaction body)
  next : Nat

/-- No registration has been made yet. -/
def Reactions.empty {body : Type} : Reactions body := Reactions.mk [] [] 0

/-- Keyed by list *and* id: `Reactions.add` gives the two paired entries one
shared id, so an id alone does not name a reaction. -/
def Reactions.get {body : Type} (rs : Reactions body) (kind : ReactionType) (id : Nat) :
    Option (Reaction body) :=
  (match kind with
    | .fulfill => rs.fulfill
    | .reject => rs.reject).find? (fun r => r.id == id)

/--
`op.performpromisethen` steps 8 to 10, registration half. Decision 8: one call
registers into both lists under one id, so the two lists carry the same ids in
the same order (`add_paired`).
-/
def Reactions.add {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) : Reactions body × Nat :=
  (Reactions.mk
    (rs.fulfill ++
      [Reaction.mk rs.next promise ReactionType.fulfill onFulfilled ReactionPhase.waiting])
    (rs.reject ++
      [Reaction.mk rs.next promise ReactionType.reject onRejected ReactionPhase.waiting])
    (rs.next + 1), rs.next)

/-- Advance one registration's phase, retaining its identity and handler. -/
def Reactions.setPhase {body : Type} (rs : Reactions body) (kind : ReactionType) (id : Nat)
    (phase : ReactionPhase) : Reactions body :=
  match kind with
  | .fulfill =>
      Reactions.mk (rs.fulfill.map (fun r => if r.id == id then { r with phase := phase } else r))
        rs.reject rs.next
  | .reject =>
      Reactions.mk rs.fulfill
        (rs.reject.map (fun r => if r.id == id then { r with phase := phase } else r)) rs.next

/-- The registrations `TriggerPromiseReactions` would enqueue, in list order. -/
def Reactions.waitingOn {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) : List (Reaction body) :=
  (match kind with
    | .fulfill => rs.fulfill
    | .reject => rs.reject).filter
    (fun r => r.promise == promise && r.phase == ReactionPhase.waiting)

/-- Decision 8's one-list view: a registration made by `WebIdl.Promise.react`
contributes one entry to each list under one id, so the fulfil list alone is
the registration order `Transform.State.subscriptions` records (`E-29`). -/
def Reactions.registered {body : Type} (rs : Reactions body) : List (Reaction body) :=
  rs.fulfill

/--
`op.triggerpromisereactions` (2700260..2701212), whose entire content is
"enqueue a reaction job for each reaction, in list order". `E-33` records that
`Transform.settle` states only `settle_pending` and `settle_other`, so the
order and once-only laws below are new content under `G-01`, not extraction.
-/
def triggerReactions {value reason body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    Reactions body × Jobs.Queue (Jobs.ReactionJob (Except reason value)) :=
  let advance : List (Reaction body) → List (Reaction body) := fun l =>
    l.map (fun r =>
      if r.promise == promise && r.phase == ReactionPhase.waiting then
        { r with phase := ReactionPhase.queued r.id }
      else r)
  (match kind with
    | .fulfill => Reactions.mk (advance rs.fulfill) rs.reject rs.next
    | .reject => Reactions.mk rs.fulfill (advance rs.reject) rs.next,
    Jobs.Queue.enqueueAll q
      ((Reactions.waitingOn rs promise kind).map (fun r => Jobs.ReactionJob.mk r.id argument)))

/-- `E-33`'s target: `op.fulfillpromise`/`op.rejectpromise` followed by
`op.triggerpromisereactions`. -/
def Table.settleAndTrigger {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) :
    Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) :=
  if Table.isPending t id then
    (Table.settle t id result,
      triggerReactions rs id
        (match result with
          | .ok _ => ReactionType.fulfill
          | .error _ => ReactionType.reject) result q)
  else (t, rs, q)

/-- `op.fulfillpromise` (2695419..2696230) as the whole operation. -/
def fulfillPromise {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (v : value) :
    Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) :=
  Table.settleAndTrigger t rs q id (Except.ok v)

/-- `op.rejectpromise` (2699323..2700252) as the whole operation. -/
def rejectPromise {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (r : reason) :
    Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) :=
  Table.settleAndTrigger t rs q id (Except.error r)

/-! ## Part B — the capability record and the resolving functions

`G-03`, wholly absent from Streams. `[[Resolve]]` and `[[Reject]]` are
first-order function identities, never Lean functions: the representation rule
in `AGENTS.md` forbids storing a body. -/

/-- `record.promisecapability-records` (2687751..2690437) with its three field
rows, as first-order identities. -/
structure Capability where
  promise : Nat
  resolve : Nat
  reject : Nat
  deriving DecidableEq

/-- `op.createresolvingfunctions` (2692679..2695411), with `[[AlreadyResolved]]`
as the one-shot marker. `G-05` (thenable adoption) stays out of this packet. -/
structure ResolvingFunctions where
  promise : Nat
  resolve : Nat
  reject : Nat
  alreadyResolved : Bool
  deriving DecidableEq

/-- `op.newpromisecapability` (2696238..2698770), restricted to the intrinsic
constructor: allocate a pending promise and name its two resolving functions. -/
def newPromiseCapability {value reason : Type} (t : Table value reason) (functionSeed : Nat) :
    Table value reason × Capability :=
  ((Table.fresh t State.pending).1,
    Capability.mk (Table.fresh t State.pending).2 functionSeed (functionSeed + 1))

/-- `op.createresolvingfunctions` (2692679..2695411). -/
def createResolvingFunctions (promise functionSeed : Nat) : ResolvingFunctions :=
  ResolvingFunctions.mk promise functionSeed (functionSeed + 1) false

/-- The resolve function, one-shot. `G-05`: it settles with a plain value and
never looks up a `then` method. -/
def ResolvingFunctions.callResolve {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (v : value) : ResolvingFunctions × Table value reason :=
  if f.alreadyResolved then (f, t)
  else ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.ok v))

/-- The reject function, one-shot. -/
def ResolvingFunctions.callReject {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (r : reason) : ResolvingFunctions × Table value reason :=
  if f.alreadyResolved then (f, t)
  else ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.error r))

/-! ## Part B — `PerformPromiseThen` as a whole operation

`G-11`. Streams has steps 8 to 10 twice over (`E-31`, `E-37`), specialized and
with no result capability. Anchor: `op.performpromisethen`, 2740635..2743669.
-/

/-- `op.performpromisethen` (2740635..2743669) with its capability argument and
its returned promise identity. It keeps `E-31`'s `Option` result: a missing
cell has no transition, where `PerformPromiseThen` is total. Step 12 sets
`[[PromiseIsHandled]]`, which is why the two settled branches mark handled. -/
def performPromiseThen {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Option (Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) × Option Nat) :=
  match Table.get t promise with
  | none => none
  | some State.pending =>
      some (t, (Reactions.add rs promise onFulfilled onRejected).1, q,
        capability.map Capability.promise)
  | some (State.fulfilled v) =>
      some (Table.markHandled t promise,
        Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
          ReactionType.fulfill rs.next (ReactionPhase.queued rs.next),
        Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.ok v)),
        capability.map Capability.promise)
  | some (State.rejected r) =>
      some (Table.markHandled t promise,
        Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
          ReactionType.reject rs.next (ReactionPhase.queued rs.next),
        Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.error r)),
        capability.map Capability.promise)

/-! ### The two reaction lists — mask M1 -/

/-- No registration has been made yet. Mask M1. -/
theorem Reactions.empty_eq {body : Type} :
    (Reactions.empty : Reactions body) = Reactions.mk [] [] 0 := rfl

/-- Lookup is keyed by list and id together. Mask M1. -/
theorem Reactions.get_eq {body : Type} (rs : Reactions body) (kind : ReactionType) (id : Nat) :
    Reactions.get rs kind id =
      (match kind with
        | .fulfill => rs.fulfill
        | .reject => rs.reject).find? (fun r => r.id == id) := rfl

/-- Registration returns the cursor it consumed. Mask M1. -/
theorem Reactions.add_id {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) :
    (Reactions.add rs promise onFulfilled onRejected).2 = rs.next := rfl

/-- Registration advances the shared cursor by one. Mask M1. -/
theorem Reactions.add_next {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) :
    (Reactions.add rs promise onFulfilled onRejected).1.next = rs.next + 1 := rfl

/-- The fulfil-side entry is appended with the `[[Type]]` tag `fulfill`. Mask M1. -/
theorem Reactions.add_fulfill {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) :
    (Reactions.add rs promise onFulfilled onRejected).1.fulfill =
      rs.fulfill ++ [Reaction.mk rs.next promise ReactionType.fulfill onFulfilled
        ReactionPhase.waiting] := rfl

/-- The reject-side entry is appended with the `[[Type]]` tag `reject`. Mask M1. -/
theorem Reactions.add_reject {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) :
    (Reactions.add rs promise onFulfilled onRejected).1.reject =
      rs.reject ++ [Reaction.mk rs.next promise ReactionType.reject onRejected
        ReactionPhase.waiting] := rfl

/-- Only the named list's matching entry changes phase. Mask M1. -/
theorem Reactions.setPhase_eq {body : Type} (rs : Reactions body) (kind : ReactionType)
    (id : Nat) (phase : ReactionPhase) :
    Reactions.setPhase rs kind id phase =
      (match kind with
        | .fulfill =>
            Reactions.mk
              (rs.fulfill.map (fun r => if r.id == id then { r with phase := phase } else r))
              rs.reject rs.next
        | .reject =>
            Reactions.mk rs.fulfill
              (rs.reject.map (fun r => if r.id == id then { r with phase := phase } else r))
              rs.next) := by
  cases kind <;> rfl

/-- The registrations still waiting on one promise, in list order. Mask M1. -/
theorem Reactions.waitingOn_eq {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) :
    Reactions.waitingOn rs promise kind =
      (match kind with
        | .fulfill => rs.fulfill
        | .reject => rs.reject).filter
        (fun r => r.promise == promise && r.phase == ReactionPhase.waiting) := rfl

/-- Decision 8's one-list view is the fulfil list. Mask M1. -/
theorem Reactions.registered_eq {body : Type} (rs : Reactions body) :
    Reactions.registered rs = rs.fulfill := rfl

/-- Decision 8: `add` gives the paired entries one id, so the two lists carry
the same ids in the same order. Mask M1. -/
theorem Reactions.add_paired {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) :
    rs.fulfill.map Reaction.id = rs.reject.map Reaction.id →
      (Reactions.add rs promise onFulfilled onRejected).1.fulfill.map Reaction.id =
        (Reactions.add rs promise onFulfilled onRejected).1.reject.map Reaction.id := by
  intro h
  simp [Reactions.add, h]

/-! ### `TriggerPromiseReactions` — the order law `E-33` does not have -/

/-- Mask M2: the statement observes the order in which reaction jobs enter the
queue, which is the whole content of `op.triggerpromisereactions`. -/
theorem triggerReactions_order {value reason body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    (triggerReactions rs promise kind argument q).2.pending =
      q.pending ++ (Reactions.waitingOn rs promise kind).map
        (fun r => Jobs.ReactionJob.mk r.id argument) := rfl

/-- Mask M1: once triggered, the same promise and list have no waiting
reaction left, so no reaction job is enqueued twice. -/
theorem triggerReactions_once {value reason body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    Reactions.waitingOn
      (triggerReactions (value := value) rs promise kind argument q).1 promise kind = [] := by
  have key : ∀ (l : List (Reaction body)),
      (l.map (fun r =>
        if r.promise == promise && r.phase == ReactionPhase.waiting then
          { r with phase := ReactionPhase.queued r.id }
        else r)).filter
        (fun r => r.promise == promise && r.phase == ReactionPhase.waiting) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons r rest ih =>
        by_cases hb : (r.promise == promise && r.phase == ReactionPhase.waiting) = true
        · simp only [List.map_cons, if_pos hb, List.filter_cons]
          rw [if_neg (by simp)]
          exact ih
        · simp only [List.map_cons, if_neg hb, List.filter_cons]
          exact ih
  cases kind <;> exact key _

/-- Mask M1: triggering one promise leaves every other promise's registrations
untouched. -/
theorem triggerReactions_other_promise {value reason body : Type} (rs : Reactions body)
    (promise other : Nat) (kind : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    other ≠ promise →
      Reactions.waitingOn
          (triggerReactions (value := value) rs promise kind argument q).1 other kind =
        Reactions.waitingOn rs other kind := by
  intro hne
  have key : ∀ (l : List (Reaction body)),
      (l.map (fun r =>
        if r.promise == promise && r.phase == ReactionPhase.waiting then
          { r with phase := ReactionPhase.queued r.id }
        else r)).filter
        (fun r => r.promise == other && r.phase == ReactionPhase.waiting) =
      l.filter (fun r => r.promise == other && r.phase == ReactionPhase.waiting) := by
    intro l
    induction l with
    | nil => rfl
    | cons r rest ih =>
        by_cases hb : (r.promise == promise && r.phase == ReactionPhase.waiting) = true
        · have hp : r.promise = promise := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hb
            exact hb.1
          have hpo : promise ≠ other := Ne.symm hne
          simp only [List.map_cons, if_pos hb, List.filter_cons]
          rw [if_neg (by simp), if_neg (by simp [hp, hpo])]
          exact ih
        · simp only [List.map_cons, if_neg hb, List.filter_cons, ih]
  cases kind <;> exact key _

/-- Mask M1: triggering one list leaves the other list untouched. -/
theorem triggerReactions_other_kind {value reason body : Type} (rs : Reactions body)
    (promise : Nat) (kind other : ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    other ≠ kind →
      Reactions.waitingOn
          (triggerReactions (value := value) rs promise kind argument q).1 promise other =
        Reactions.waitingOn rs promise other := by
  intro hne
  cases kind <;> cases other <;> first | rfl | exact absurd rfl hne

/-! ### Settle-and-trigger, `FulfillPromise` and `RejectPromise` -/

/-- Mask M2. `E-33`'s target: settling followed by the ordered trigger. -/
theorem Table.settleAndTrigger_pending {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) :
    Table.get t id = some State.pending →
      Table.settleAndTrigger t rs q id result =
        (Table.settle t id result,
          triggerReactions rs id
            (match result with
              | .ok _ => ReactionType.fulfill
              | .error _ => ReactionType.reject) result q) := by
  intro h
  simp [Table.settleAndTrigger, (Table.isPending_iff t id).mpr h]

/-- Mask M1. The guard of decision 7 propagates: a non-pending promise
notifies nobody. -/
theorem Table.settleAndTrigger_other {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) :
    Table.get t id ≠ some State.pending →
      Table.settleAndTrigger t rs q id result = (t, rs, q) := by
  intro h
  have hfalse : Table.isPending t id = false := by
    cases hp : Table.isPending t id with
    | false => rfl
    | true => exact absurd ((Table.isPending_iff t id).mp hp) h
  simp [Table.settleAndTrigger, hfalse]

/-- `op.fulfillpromise` is settle-and-trigger at an `ok` result. Mask M1. -/
theorem fulfillPromise_eq {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (v : value) :
    fulfillPromise t rs q id v = Table.settleAndTrigger t rs q id (Except.ok v) := rfl

/-- `op.rejectpromise` is settle-and-trigger at an `error` result. Mask M1. -/
theorem rejectPromise_eq {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (r : reason) :
    rejectPromise t rs q id r = Table.settleAndTrigger t rs q id (Except.error r) := rfl

/-! ### `PerformPromiseThen` — mask M2 for the two settled branches -/

/-- `E-31` risk: `PerformPromiseThen` is total where this is partial; the
packet keeps the Streams `Option` and records the difference. Mask M1. -/
theorem performPromiseThen_missing {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = none →
      performPromiseThen t rs q promise onFulfilled onRejected capability = none := by
  intro h
  simp [performPromiseThen, h]

/-- Steps 8 to 10, pending branch: registration only. Mask M1. -/
theorem performPromiseThen_pending {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some State.pending →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (t, (Reactions.add rs promise onFulfilled onRejected).1, q,
          capability.map Capability.promise) := by
  intro h
  simp [performPromiseThen, h]

/-- Steps 8 to 10, fulfilled branch: a reaction job enters the queue, and
step 12 marks the promise handled. Mask M2. -/
theorem performPromiseThen_fulfilled {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some (State.fulfilled v) →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (Table.markHandled t promise,
          Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
            ReactionType.fulfill rs.next (ReactionPhase.queued rs.next),
          Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.ok v)),
          capability.map Capability.promise) := by
  intro h
  simp [performPromiseThen, h]

/-- Steps 8 to 10, rejected branch. Mask M2. -/
theorem performPromiseThen_rejected {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some (State.rejected r) →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (Table.markHandled t promise,
          Reactions.setPhase (Reactions.add rs promise onFulfilled onRejected).1
            ReactionType.reject rs.next (ReactionPhase.queued rs.next),
          Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.error r)),
          capability.map Capability.promise) := by
  intro h
  simp [performPromiseThen, h]

/-! ### Capability and resolving functions — mask M1 -/

/-- `op.newpromisecapability` allocates a pending promise and names its two
resolving functions. Mask M1. -/
theorem newPromiseCapability_eq {value reason : Type} (t : Table value reason)
    (functionSeed : Nat) :
    newPromiseCapability t functionSeed =
      ((Table.fresh t State.pending).1,
        Capability.mk (Table.fresh t State.pending).2 functionSeed (functionSeed + 1)) := rfl

/-- `op.createresolvingfunctions` mints an unresolved pair. Mask M1. -/
theorem createResolvingFunctions_eq (promise functionSeed : Nat) :
    createResolvingFunctions promise functionSeed =
      ResolvingFunctions.mk promise functionSeed (functionSeed + 1) false := rfl

/-- `[[AlreadyResolved]]` is the one-shot marker: the first call settles. Mask M1. -/
theorem ResolvingFunctions.callResolve_fresh {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (v : value) :
    f.alreadyResolved = false →
      ResolvingFunctions.callResolve f t v =
        ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.ok v)) := by
  intro h
  simp [ResolvingFunctions.callResolve, h]

/-- A second call is inert. Mask M1. -/
theorem ResolvingFunctions.callResolve_alreadyResolved {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (v : value) :
    f.alreadyResolved = true → ResolvingFunctions.callResolve f t v = (f, t) := by
  intro h
  simp [ResolvingFunctions.callResolve, h]

/-- The reject function is one-shot the same way. Mask M1. -/
theorem ResolvingFunctions.callReject_fresh {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (r : reason) :
    f.alreadyResolved = false →
      ResolvingFunctions.callReject f t r =
        ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.error r)) := by
  intro h
  simp [ResolvingFunctions.callReject, h]

/-- A second call is inert. Mask M1. -/
theorem ResolvingFunctions.callReject_alreadyResolved {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (r : reason) :
    f.alreadyResolved = true → ResolvingFunctions.callReject f t r = (f, t) := by
  intro h
  simp [ResolvingFunctions.callReject, h]

end Whatwg.Ecma262.Promise
