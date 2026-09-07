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

/-! ## Part B — the capability record

`G-03`, wholly absent from Streams. `[[Resolve]]` and `[[Reject]]` are
first-order function identities, never Lean functions: the representation rule
in `AGENTS.md` forbids storing a body.

Declaration-order note, Q3b fidelity addendum
(`test/contracts/promise-first-packet-q3b.contract.md` §11, finding F4): this
record is declared here rather than beside `ResolvingFunctions` below, because
`field.promisereaction-records.Capability` (CAPFIELD, 2691475..2691802, digest
`67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77`) makes it a
field of `Reaction`. The order changed; the signature did not. -/

/-- `record.promisecapability-records` (2687751..2690437) with its three field
rows, as first-order identities. `G-03`, CAPREC.

`deriving Repr` is forced by finding F4 and is additive: `Reaction` derives
`Repr` and now carries an `Option Capability` field, so `Repr (Reaction Nat)` —
the `E-50` receipt of the Q3b addendum — cannot be synthesized without it. The
`DecidableEq` the base packet's battery ascribes is unchanged, and `Reaction`
still gains none: a capability is a triple of `Nat` identities. Builder note of
the Q3b landing. -/
structure Capability where
  promise : Nat
  resolve : Nat
  reject : Nat
  deriving DecidableEq, Repr

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

`capability` is `field.promisereaction-records.Capability` (CAPFIELD,
2691475..2691802, digest
`67b47fd1bc6773cb099432f10db3b5b427d445cd1a10077db3ec90ec381d6a77`), "a
PromiseCapability Record or *undefined*", added by finding F4 of the Q3b
fidelity addendum (WS-PROM-CE-026): `op.newpromisereactionjob` (REACTJOB,
2702885..2705591) reads it to resolve or reject the derived promise, and
without it `op.performpromisethen`'s `_resultCapability_` is stored nowhere.
`G-01`; `E-50` (`Transform.Job`, generalize) constrains the repair — the field
is a triple of `Nat` identities, so the record stays `Repr`-only and gains no
`DecidableEq`.
-/
structure Reaction (body : Type) where
  id : Nat
  promise : Nat
  kind : ReactionType
  handler : Option body
  capability : Option Capability
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
`op.performpromisethen` (THEN, 2740635..2743669) steps 7, 8 and 9, registration
half. Decision 8: one call registers into both lists under one id, so the two
lists carry the same ids in the same order (`add_paired`).

Q3b finding F4: steps 7 and 8 give **both** records the same
`_resultCapability_`, so the registering operation takes it. Streams supplies
`none` — a transform subscription has no result capability, which is `G-11`'s
remainder and which `E-31` already records. `G-01`; `E-29` (generalize),
CAPFIELD.
-/
def Reactions.add {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    Reactions body × Nat :=
  (Reactions.mk
    (rs.fulfill ++
      [Reaction.mk rs.next promise ReactionType.fulfill onFulfilled capability
        ReactionPhase.waiting])
    (rs.reject ++
      [Reaction.mk rs.next promise ReactionType.reject onRejected capability
        ReactionPhase.waiting])
    (rs.next + 1), rs.next)

/--
`op.performpromisethen` (THEN, 2740635..2743669) steps 7, 8, 10 and 11: the
PromiseReaction Record a **settled** branch builds and hands to the job it
enqueues. Steps 10 and 11 append to no list, so this record is not reachable
through `Reactions` and the caller holds it (finding F2, WS-PROM-CE-024).

It consumes the shared registration cursor, so the job it feeds carries an
identity no registered reaction can collide with, and it leaves both lists
exactly as they were, so no entry is left `waiting` on a promise that has
already settled. `G-01`; `E-29` (generalize), CAPFIELD.
-/
def Reactions.mint {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    Reactions body × Reaction body :=
  (Reactions.mk rs.fulfill rs.reject (rs.next + 1),
    Reaction.mk rs.next promise kind handler capability (ReactionPhase.queued rs.next))

/--
`op.fulfillpromise` (FULFILL, 2695419..2696230) steps 4 and 5 and
`op.rejectpromise` (REJECT, 2699323..2700252) steps 4 and 5, which each set
**both** `[[PromiseFulfillReactions]]` and `[[PromiseRejectReactions]]` to
*undefined* after step 2 has captured the one list that will be triggered
(finding F3, WS-PROM-CE-025). The first-order form of "set to *undefined*":
every registration on the settled promise, in either list, leaves the `waiting`
phase. `G-01`; `E-33` (generalize).
-/
def Reactions.clear {body : Type} (rs : Reactions body) (promise : Nat) : Reactions body :=
  Reactions.mk
    (rs.fulfill.map (fun r =>
      if r.promise == promise && r.phase == ReactionPhase.waiting then
        { r with phase := ReactionPhase.done }
      else r))
    (rs.reject.map (fun r =>
      if r.promise == promise && r.phase == ReactionPhase.waiting then
        { r with phase := ReactionPhase.done }
      else r))
    rs.next

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
`op.triggerpromisereactions`. Q3b finding F3: steps 4 and 5 of both callers
clear **both** reaction lists, so the triggered lists are cleared afterwards
and no registration on the settled promise is left `waiting`
(WS-PROM-CE-025). `G-01`; `E-33` (generalize), FULFILL, REJECT, TRIGGER. -/
def Table.settleAndTrigger {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) :
    Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) :=
  if Table.isPending t id then
    (Table.settle t id result,
      Reactions.clear
        (triggerReactions rs id
          (match result with
            | .ok _ => ReactionType.fulfill
            | .error _ => ReactionType.reject) result q).1 id,
      (triggerReactions rs id
        (match result with
          | .ok _ => ReactionType.fulfill
          | .error _ => ReactionType.reject) result q).2)
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

/-! ## Part B — the resolving functions

`G-03`, wholly absent from Streams. `Capability` itself is declared above,
because the Q3b addendum's finding F4 makes it a field of `Reaction`. -/

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

/-- `op.createresolvingfunctions` (RESOLVING, 2692679..2695411): `[[Resolve]]`
or `[[Reject]]` selected by a completion, through the same shared one-shot
marker. `op.newpromisereactionjob` inner steps 8 and 9 are exactly this
selection. `G-03`. -/
def ResolvingFunctions.callSettle {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (result : Except reason value) :
    ResolvingFunctions × Table value reason :=
  match result with
  | .ok v => ResolvingFunctions.callResolve f t v
  | .error r => ResolvingFunctions.callReject f t r

/-- `op.createresolvingfunctions` (RESOLVING, 2692679..2695411) resolve steps
step 4: if `SameValue(resolution, promise)` is *true*, reject the promise with
a newly created *TypeError* and return (WS-PROM-CE-033). The base packet's
`callResolve` takes a plain `value` and cannot see the case, because the value
universe in which a promise is one value among others is `G-04` and adoption is
`G-05`.

This states the branch at the one place the model can see it: the host supplies
the resolution's promise identity and the reason it allocated for the
*TypeError*. Off the self branch the answer is `none` — the `G-04`/`G-05`
frontier — rather than a guess. `G-03`. -/
def ResolvingFunctions.callResolveSelf {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (resolution : Nat) (selfError : reason) :
    Option (ResolvingFunctions × Table value reason) :=
  if resolution == f.promise then
    some (ResolvingFunctions.callReject f t selfError)
  else none

/-- `op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner steps 4 and 5.
DB-02 keeps the handler a first-order descriptor: the model never runs it, so
the handler's completion arrives as the `decision` argument and is returned
unexamined (WS-PROM-CE-027). With an empty handler the result is the argument,
which already carries the `~fulfill~`/`~reject~` tag `triggerReactions` put on
it, so `NormalCompletion` and `ThrowCompletion` are that tag and nothing more.
`requirement.jobs.4` (JOBS4, 626486..626589, digest
`22934fdf600a46d75443c562c8de0fdd4f441e8f67c4816d25ac4ec03aca194b`) is why the
step is total. `G-07`; `E-51` (`Transform.runJob`, generalize). -/
def reactionHandlerResult {value reason body : Type} (reaction : Reaction body)
    (argument decision : Except reason value) : Except reason value :=
  if reaction.handler.isSome then decision else argument

/-- `op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner steps 6 to 9
as one step: with `[[Capability]]` *undefined* the job returns `~empty~` and
settles nothing; otherwise an abrupt result calls `[[Reject]]` and a normal
result calls `[[Resolve]]`.

It takes the capability's resolving functions rather than minting them, because
the one-shot marker is state the configuration owns (`G-08` remainder, P8) and
a freshly minted pair would re-arm it. Nothing is stored and nothing is run
(DB-02). `G-07`, `G-03`; `E-51` (generalize). -/
def runReactionJob {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) :
    ResolvingFunctions × Table value reason :=
  if reaction.capability.isSome then
    ResolvingFunctions.callSettle f t (reactionHandlerResult reaction argument decision)
  else (f, t)

/-! ## Part B — the settlement order the general table lacks (Q3b, F6)

DB-04's M2 is "M1 plus the full order of promise settlements observable by the
consumer". The general table records what each identity settled *to* and not
*when*, so `op.wait-for-all`'s "the first rejection to settle" is inexpressible
over it. This is that order as first-order data, and it is a trace, never a
second table (R-P12, WS-PROM-CE-031): `Table.settleTraced` returns
`Table.settle`'s table unchanged and `Table.mk`'s arity is untouched. -/

/-- Settled identities with their outcomes, oldest first. Its shape is `E-71`'s
(`Whatwg.Streams.Writable.settlementTrace`, keep) lifted off the writable event
alphabet, which is why `Whatwg.Streams.Writable.settlementTrace_bridge` needs no
projection; `E-63` (`Readable.settlementTrace`, keep) is the readable
counterpart, whose bridge is deferred because the readable alphabet's `closed`
entry carries no promise identity. A model device under DB-04's M2: it has no
census row of its own. -/
abbrev SettlementTrace (value reason : Type) : Type := List (Nat × Except reason value)

/-- `op.fulfillpromise` (FULFILL, 2695419..2696230) and `op.rejectpromise`
(REJECT, 2699323..2700252) with the settlement order recorded beside the table.
Decision 7's guard propagates: a non-pending settle is the identity on both
components, so no identity is recorded twice. `E-20` (generalize), `G-06`. -/
def Table.settleTraced {value reason : Type} (t : Table value reason)
    (tr : SettlementTrace value reason) (id : Nat) (result : Except reason value) :
    Table value reason × SettlementTrace value reason :=
  if Table.isPending t id then (Table.settle t id result, tr ++ [(id, result)])
  else (t, tr)

/-- The first rejection **to settle** among a list of argument identities, which
is what `op.wait-for-all`'s (WAITALL, 353239..354879) rejection handler fires
on — not the first rejection in argument order (WS-PROM-CE-030). `G-06`;
`E-56` (generalize) is the settled predicate that cannot express it. -/
def SettlementTrace.firstRejection {value reason : Type}
    (tr : SettlementTrace value reason) (ids : List Nat) : Option reason :=
  List.findSome? (fun e =>
    if List.contains ids e.1 then
      match e.2 with
      | Except.error r => some r
      | Except.ok _ => none
    else none) tr

/-! ## Part B — `PerformPromiseThen` as a whole operation

`G-11`. Streams has steps 8 to 10 twice over (`E-31`, `E-37`), specialized and
with no result capability. Anchor: `op.performpromisethen`, 2740635..2743669.
-/

/-- `op.performpromisethen` (THEN, 2740635..2743669) with its capability
argument, the record a settled branch captures, and its returned promise
identity. It keeps `E-31`'s `Option` result: a missing cell has no transition,
where `PerformPromiseThen` is total.

Q3b findings F1 and F2. Step 12, "Set _promise_.[[PromiseIsHandled]] to
*true*", sits after the three-way branch of steps 9 to 11, not inside it, so
**every** branch marks the promise handled (WS-PROM-CE-023). Steps 10 and 11
build a job out of one of the records created at steps 7 and 8 and enqueue it,
appending to neither list; only step 9's pending branch appends, one record to
each (WS-PROM-CE-024). The captured record is returned because nothing else
holds it. `G-11`, `G-01`; `E-31`, `E-37` (generalize). -/
def performPromiseThen {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Option (Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) ×
      Option (Reaction body) × Option Nat) :=
  match Table.get t promise with
  | none => none
  | some State.pending =>
      some (Table.markHandled t promise,
        (Reactions.add rs promise onFulfilled onRejected capability).1, q, none,
        capability.map Capability.promise)
  | some (State.fulfilled v) =>
      some (Table.markHandled t promise,
        (Reactions.mint rs promise ReactionType.fulfill onFulfilled capability).1,
        Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.ok v)),
        some (Reactions.mint rs promise ReactionType.fulfill onFulfilled capability).2,
        capability.map Capability.promise)
  | some (State.rejected r) =>
      some (Table.markHandled t promise,
        (Reactions.mint rs promise ReactionType.reject onRejected capability).1,
        Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.error r)),
        some (Reactions.mint rs promise ReactionType.reject onRejected capability).2,
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
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    (Reactions.add rs promise onFulfilled onRejected capability).2 = rs.next := rfl

/-- Registration advances the shared cursor by one. Mask M1. -/
theorem Reactions.add_next {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    (Reactions.add rs promise onFulfilled onRejected capability).1.next = rs.next + 1 := rfl

/-- The fulfil-side entry is appended with the `[[Type]]` tag `fulfill` and the
shared `_resultCapability_` of THEN steps 7 and 8. Mask M1. -/
theorem Reactions.add_fulfill {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    (Reactions.add rs promise onFulfilled onRejected capability).1.fulfill =
      rs.fulfill ++ [Reaction.mk rs.next promise ReactionType.fulfill onFulfilled capability
        ReactionPhase.waiting] := rfl

/-- The reject-side entry is appended with the `[[Type]]` tag `reject` and the
same capability. Mask M1. -/
theorem Reactions.add_reject {body : Type} (rs : Reactions body) (promise : Nat)
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    (Reactions.add rs promise onFulfilled onRejected capability).1.reject =
      rs.reject ++ [Reaction.mk rs.next promise ReactionType.reject onRejected capability
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
    (onFulfilled onRejected : Option body) (capability : Option Capability) :
    rs.fulfill.map Reaction.id = rs.reject.map Reaction.id →
      (Reactions.add rs promise onFulfilled onRejected capability).1.fulfill.map Reaction.id =
        (Reactions.add rs promise onFulfilled onRejected capability).1.reject.map
          Reaction.id := by
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

/-- Mask M2. `E-33`'s target: settling, the ordered trigger, and the clearing
of both lists that FULFILL steps 4–5 and REJECT steps 4–5 perform (Q3b finding
F3, WS-PROM-CE-025). The job-queue component is unchanged, so the M2 content of
the law is exactly what it was. -/
theorem Table.settleAndTrigger_pending {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) :
    Table.get t id = some State.pending →
      Table.settleAndTrigger t rs q id result =
        (Table.settle t id result,
          Reactions.clear
            (triggerReactions rs id
              (match result with
                | .ok _ => ReactionType.fulfill
                | .error _ => ReactionType.reject) result q).1 id,
          (triggerReactions rs id
            (match result with
              | .ok _ => ReactionType.fulfill
              | .error _ => ReactionType.reject) result q).2) := by
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

/-- Step 9, the pending branch: both records are appended, neither is captured,
and step 12 marks the promise handled all the same (Q3b finding F1,
WS-PROM-CE-023). Mask M1. -/
theorem performPromiseThen_pending {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some State.pending →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (Table.markHandled t promise,
          (Reactions.add rs promise onFulfilled onRejected capability).1, q, none,
          capability.map Capability.promise) := by
  intro h
  simp [performPromiseThen, h]

/-- Step 10, the fulfilled branch: a reaction job enters the queue carrying the
minted record, no list is appended to (Q3b finding F2, WS-PROM-CE-024), and
step 12 marks the promise handled. Mask M2. -/
theorem performPromiseThen_fulfilled {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (v : value) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some (State.fulfilled v) →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (Table.markHandled t promise,
          (Reactions.mint rs promise ReactionType.fulfill onFulfilled capability).1,
          Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.ok v)),
          some (Reactions.mint rs promise ReactionType.fulfill onFulfilled capability).2,
          capability.map Capability.promise) := by
  intro h
  simp [performPromiseThen, h]

/-- Step 11, the rejected branch, for the same reason. Step 11's third
sub-step, `HostPromiseRejectionTracker`, is `G-02` and stays out: no component
here observes it. Mask M2. -/
theorem performPromiseThen_rejected {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (r : reason) (onFulfilled onRejected : Option body)
    (capability : Option Capability) :
    Table.get t promise = some (State.rejected r) →
      performPromiseThen t rs q promise onFulfilled onRejected capability =
        some (Table.markHandled t promise,
          (Reactions.mint rs promise ReactionType.reject onRejected capability).1,
          Jobs.Queue.enqueue q (Jobs.ReactionJob.mk rs.next (Except.error r)),
          some (Reactions.mint rs promise ReactionType.reject onRejected capability).2,
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

/-! ## The Q3b fidelity addendum's laws

`test/contracts/promise-first-packet-q3b.contract.md` §7.1, answering findings
F1 to F4 and F6 of ruling R-P20 and the minors it lists. Attacks:
`test/counterexamples/promise/ATTACKS.md`, WS-PROM-CE-023..038. Masks are
DB-04's under §7 of the base packet: a law whose statement observes the order
in which settlements happen or in which reaction jobs enter the queue is M2;
one that observes a cell value, a branch, a table shape or a terminal result is
M1. -/

/-! ### F1 — `op.performpromisethen` step 12 is unconditional

Anchors: THEN, 2740635..2743669; `slot.PromiseIsHandled`, 2746322..2746637.
`E-21` (generalize); `G-02` records that nothing reads the bit in this lane and
that `HostPromiseRejectionTracker` stays out. WS-PROM-CE-023. -/

/-- Marking an allocated promise handled is observable at its cell. Mask M1.
`E-21` (generalize), `G-02`. -/
theorem Table.markHandled_marked {value reason : Type} (t : Table value reason) (id : Nat) :
    (Table.getCell t id).isSome = true →
      (Table.getCell (Table.markHandled t id) id).map Cell.handled = some true := by
  intro hsome
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
  simp only [Table.getCell, Table.markHandled] at hsome ⊢
  rw [key (fun c => Cell.mk c.state true) t.entries]
  cases hf : List.find? (fun (e : Nat × Cell value reason) => e.1 == id) t.entries with
  | none => rw [hf] at hsome; simp at hsome
  | some _ => rfl

/-- Step 12 through every branch: whenever `PerformPromiseThen` returns at all,
the promise is left handled, the pending branch included. Mask M1. `G-11`. -/
theorem performPromiseThen_handled {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (promise : Nat) (onFulfilled onRejected : Option body)
    (capability : Option Capability)
    (res : Table value reason × Reactions body ×
      Jobs.Queue (Jobs.ReactionJob (Except reason value)) ×
      Option (Reaction body) × Option Nat) :
    performPromiseThen t rs q promise onFulfilled onRejected capability = some res →
      (Table.getCell res.1 promise).map Cell.handled = some true := by
  intro h
  cases hc : Table.getCell t promise with
  | none =>
      exact absurd h (by simp [performPromiseThen, Table.get, hc])
  | some cell =>
      have hsome : (Table.getCell t promise).isSome = true := by rw [hc]; rfl
      have hres : res.1 = Table.markHandled t promise := by
        have hg : Table.get t promise = some cell.state := by
          simp [Table.get, hc]
        cases hstate : cell.state with
        | pending =>
            rw [hstate] at hg
            rw [performPromiseThen_pending t rs q promise onFulfilled onRejected
              capability hg] at h
            simp only [Option.some.injEq] at h
            rw [← h]
        | fulfilled v =>
            rw [hstate] at hg
            rw [performPromiseThen_fulfilled t rs q promise v onFulfilled onRejected
              capability hg] at h
            simp only [Option.some.injEq] at h
            rw [← h]
        | rejected r =>
            rw [hstate] at hg
            rw [performPromiseThen_rejected t rs q promise r onFulfilled onRejected
              capability hg] at h
            simp only [Option.some.injEq] at h
            rw [← h]
      rw [hres]
      exact Table.markHandled_marked t promise hsome

/-! ### F2 — the settled branches append to no list

THEN steps 10 and 11 build a job out of one of the records created at steps 7
and 8 and enqueue it; neither list is touched. `G-01`; `E-29`, `E-31`, `E-37`
(generalize). WS-PROM-CE-024. -/

/-- The defining equation of the unappended record. Mask M1. -/
theorem Reactions.mint_eq {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    Reactions.mint rs promise kind handler capability =
      (Reactions.mk rs.fulfill rs.reject (rs.next + 1),
        Reaction.mk rs.next promise kind handler capability
          (ReactionPhase.queued rs.next)) := rfl

/-- The fulfil list is not appended to. Mask M1. -/
theorem Reactions.mint_fulfill {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    (Reactions.mint rs promise kind handler capability).1.fulfill = rs.fulfill := rfl

/-- The reject list is not appended to. Mask M1. -/
theorem Reactions.mint_reject {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    (Reactions.mint rs promise kind handler capability).1.reject = rs.reject := rfl

/-- The shared registration cursor is still consumed, so the job the settled
branch enqueues carries an identity no registered reaction can reuse. Mask M1. -/
theorem Reactions.mint_next {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    (Reactions.mint rs promise kind handler capability).1.next = rs.next + 1 := rfl

/-- The record THEN steps 7 and 8 create, at the settled promise's `[[Type]]`,
already queued because step 10 or 11 enqueued its job. Mask M1. -/
theorem Reactions.mint_reaction {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    (Reactions.mint rs promise kind handler capability).2 =
      Reaction.mk rs.next promise kind handler capability
        (ReactionPhase.queued rs.next) := rfl

/-- F4 at the settled branch: the unappended record carries `[[Capability]]`
too, which is what `op.newpromisereactionjob` reads. Mask M1. CAPFIELD. -/
theorem Reactions.mint_capability {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability) :
    (Reactions.mint rs promise kind handler capability).2.capability = capability := rfl

/-- The whole of F2: minting leaves the waiting set of **every** promise and
**both** lists exactly as it was, so a settled branch can never leave an entry
waiting on a promise that has already settled. Mask M1. -/
theorem Reactions.mint_no_waiting {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) (handler : Option body) (capability : Option Capability)
    (other : Nat) (otherKind : ReactionType) :
    Reactions.waitingOn (Reactions.mint rs promise kind handler capability).1 other otherKind =
      Reactions.waitingOn rs other otherKind := by
  cases otherKind <;> rfl

/-! ### F3 — `FulfillPromise` and `RejectPromise` clear both lists

FULFILL steps 4 and 5 and REJECT steps 4 and 5 set both
`[[PromiseFulfillReactions]]` and `[[PromiseRejectReactions]]` to *undefined*,
after step 2 has captured the one list that will be triggered. `G-01`; `E-33`
(generalize). WS-PROM-CE-025. -/

/-- The defining equation. Mask M1. -/
theorem Reactions.clear_eq {body : Type} (rs : Reactions body) (promise : Nat) :
    Reactions.clear rs promise =
      Reactions.mk
        (rs.fulfill.map (fun r =>
          if r.promise == promise && r.phase == ReactionPhase.waiting then
            { r with phase := ReactionPhase.done }
          else r))
        (rs.reject.map (fun r =>
          if r.promise == promise && r.phase == ReactionPhase.waiting then
            { r with phase := ReactionPhase.done }
          else r))
        rs.next := rfl

/-- "Set to *undefined*" for **both** lists, quantified over the kind so
neither side is exempt. Mask M1. -/
theorem Reactions.clear_waiting {body : Type} (rs : Reactions body) (promise : Nat)
    (kind : ReactionType) :
    Reactions.waitingOn (Reactions.clear rs promise) promise kind = [] := by
  have key : ∀ (l : List (Reaction body)),
      (l.map (fun r =>
        if r.promise == promise && r.phase == ReactionPhase.waiting then
          { r with phase := ReactionPhase.done }
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

/-- Clearing one promise's registrations leaves every other promise's alone, in
both lists. Mask M1. -/
theorem Reactions.clear_other_promise {body : Type} (rs : Reactions body) (promise other : Nat)
    (kind : ReactionType) :
    other ≠ promise →
      Reactions.waitingOn (Reactions.clear rs promise) other kind =
        Reactions.waitingOn rs other kind := by
  intro hne
  have key : ∀ (l : List (Reaction body)),
      (l.map (fun r =>
        if r.promise == promise && r.phase == ReactionPhase.waiting then
          { r with phase := ReactionPhase.done }
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

/-- Clearing consumes no registration cursor. Mask M1. -/
theorem Reactions.clear_next {body : Type} (rs : Reactions body) (promise : Nat) :
    (Reactions.clear rs promise).next = rs.next := rfl

/-- The F3 law at the caller: after `FulfillPromise` or `RejectPromise` no
registration on the settled promise is waiting, in either list. Mask M1. -/
theorem Table.settleAndTrigger_cleared {value reason body : Type} (t : Table value reason)
    (rs : Reactions body) (q : Jobs.Queue (Jobs.ReactionJob (Except reason value)))
    (id : Nat) (result : Except reason value) (kind : ReactionType) :
    Table.get t id = some State.pending →
      Reactions.waitingOn (Table.settleAndTrigger t rs q id result).2.1 id kind = [] := by
  intro h
  rw [Table.settleAndTrigger_pending t rs q id result h]
  exact Reactions.clear_waiting _ id kind

/-! ### F4 — the reaction job, its capability and the handler as a decision

REACTJOB inner steps 4 to 9. DB-02: the handler is a first-order descriptor and
the model never runs it, so its completion arrives as a decision on the tape.
JOBS4 is why the step is total. `G-07`, `G-03`; `E-51` (generalize).
WS-PROM-CE-026, WS-PROM-CE-027. -/

/-- Inner steps 4a and 4b: with an empty handler the result is the argument,
which already carries the `~fulfill~`/`~reject~` tag `triggerReactions` put on
it. Mask M1. -/
theorem reactionHandlerResult_empty {value reason body : Type} (reaction : Reaction body)
    (argument decision : Except reason value) :
    reaction.handler = none →
      reactionHandlerResult reaction argument decision = argument := by
  intro h
  simp [reactionHandlerResult, h]

/-- Inner step 5: with a handler the result is the host's decision, returned
unexamined; nothing here models a body (DB-02). Mask M1. -/
theorem reactionHandlerResult_handler {value reason body : Type} (reaction : Reaction body)
    (argument decision : Except reason value) (h : body) :
    reaction.handler = some h →
      reactionHandlerResult reaction argument decision = decision := by
  intro hh
  simp [reactionHandlerResult, hh]

/-- A normal completion calls `[[Resolve]]`. Mask M1. `G-03`, RESOLVING. -/
theorem ResolvingFunctions.callSettle_ok {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (v : value) :
    ResolvingFunctions.callSettle f t (Except.ok v) =
      ResolvingFunctions.callResolve f t v := rfl

/-- An abrupt completion calls `[[Reject]]`. Mask M1. `G-03`, RESOLVING. -/
theorem ResolvingFunctions.callSettle_error {value reason : Type} (f : ResolvingFunctions)
    (t : Table value reason) (r : reason) :
    ResolvingFunctions.callSettle f t (Except.error r) =
      ResolvingFunctions.callReject f t r := rfl

/-- Inner step 6: with `[[Capability]]` *undefined* the job returns `~empty~`
and settles nothing. Mask M1. -/
theorem runReactionJob_no_capability {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) :
    reaction.capability = none →
      runReactionJob t f reaction argument decision = (f, t) := by
  intro h
  simp [runReactionJob, h]

/-- An empty handler settles the capability with the argument. Mask M1. -/
theorem runReactionJob_empty_handler {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) (cap : Capability) :
    reaction.capability = some cap → reaction.handler = none →
      runReactionJob t f reaction argument decision =
        ResolvingFunctions.callSettle f t argument := by
  intro hcap hh
  simp [runReactionJob, reactionHandlerResult, hcap, hh]

/-- Inner step 9: `G-03`'s resolving functions are wired to something at last —
a normal handler result resolves the capability's promise. Mask M1. -/
theorem runReactionJob_resolve {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) (cap : Capability) (h : body) (v : value) :
    reaction.capability = some cap → reaction.handler = some h →
    f.alreadyResolved = false → decision = Except.ok v →
      runReactionJob t f reaction argument decision =
        ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.ok v)) := by
  intro hcap hh hres hdec
  simp [runReactionJob, reactionHandlerResult, hcap, hh, hdec,
    ResolvingFunctions.callSettle, ResolvingFunctions.callResolve, hres]

/-- Inner step 8: an abrupt handler result rejects it. Mask M1. -/
theorem runReactionJob_reject {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) (cap : Capability) (h : body) (r : reason) :
    reaction.capability = some cap → reaction.handler = some h →
    f.alreadyResolved = false → decision = Except.error r →
      runReactionJob t f reaction argument decision =
        ({ f with alreadyResolved := true }, Table.settle t f.promise (Except.error r)) := by
  intro hcap hh hres hdec
  simp [runReactionJob, reactionHandlerResult, hcap, hh, hdec,
    ResolvingFunctions.callSettle, ResolvingFunctions.callReject, hres]

/-- The one-shot marker survives the job: a second reaction job that reaches
the same already-resolved functions settles nothing. Mask M1. -/
theorem runReactionJob_once {value reason body : Type} (t : Table value reason)
    (f : ResolvingFunctions) (reaction : Reaction body)
    (argument decision : Except reason value) (cap : Capability) :
    reaction.capability = some cap → f.alreadyResolved = true →
      runReactionJob t f reaction argument decision = (f, t) := by
  intro hcap hres
  have inert : ∀ x : Except reason value, ResolvingFunctions.callSettle f t x = (f, t) := by
    intro x
    cases x with
    | ok v => simp [ResolvingFunctions.callSettle, ResolvingFunctions.callResolve, hres]
    | error r => simp [ResolvingFunctions.callSettle, ResolvingFunctions.callReject, hres]
  simp [runReactionJob, hcap, inert]

/-! ### Minor — the one-shot marker is shared, not per function

At this pin RESOLVING has no `[[AlreadyResolved]]` record: step 1 creates one
Record `{ [[Value]]: toResolve }` that both `_resolveSteps_` (step 2) and
`_rejectSteps_` (step 4) capture, and each closure's own step 3 sets that
shared `[[Value]]` to `~empty~` after its step 1 has tested it, so calling
either function disables both. The field keeps the name `alreadyResolved` —
renaming it would break four frozen ascriptions for a citation defect — and the
citation is corrected here. `G-03`. WS-PROM-CE-032. -/

/-- Calling `[[Resolve]]` disables `[[Reject]]`. Mask M1. -/
theorem ResolvingFunctions.callResolve_disables_reject {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (v : value) (r : reason) :
    f.alreadyResolved = false →
      ResolvingFunctions.callReject
          (ResolvingFunctions.callResolve f t v).1
          (ResolvingFunctions.callResolve f t v).2 r =
        ((ResolvingFunctions.callResolve f t v).1,
          (ResolvingFunctions.callResolve f t v).2) := by
  intro h
  simp [ResolvingFunctions.callResolve, ResolvingFunctions.callReject, h]

/-- Calling `[[Reject]]` disables `[[Resolve]]`. Mask M1. -/
theorem ResolvingFunctions.callReject_disables_resolve {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (r : reason) (v : value) :
    f.alreadyResolved = false →
      ResolvingFunctions.callResolve
          (ResolvingFunctions.callReject f t r).1
          (ResolvingFunctions.callReject f t r).2 v =
        ((ResolvingFunctions.callReject f t r).1,
          (ResolvingFunctions.callReject f t r).2) := by
  intro h
  simp [ResolvingFunctions.callResolve, ResolvingFunctions.callReject, h]

/-! ### Minor — the self-resolution branch

RESOLVING resolve steps step 4, with the `G-04` value universe and the `G-05`
adoption branch still out. `G-03`. WS-PROM-CE-033. -/

/-- Resolving a promise with itself rejects it, with the reason the host
allocated for the *TypeError* the step creates. Mask M1. -/
theorem ResolvingFunctions.callResolveSelf_self {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (selfError : reason) :
    f.alreadyResolved = false →
      ResolvingFunctions.callResolveSelf f t f.promise selfError =
        some ({ f with alreadyResolved := true },
          Table.settle t f.promise (Except.error selfError)) := by
  intro h
  simp [ResolvingFunctions.callResolveSelf, ResolvingFunctions.callReject, h]

/-- Off the self branch the operation answers `none` — the `G-04` and `G-05`
frontier — rather than guessing at a resolution it cannot inspect. Mask M1. -/
theorem ResolvingFunctions.callResolveSelf_other {value reason : Type}
    (f : ResolvingFunctions) (t : Table value reason) (resolution : Nat) (selfError : reason) :
    resolution ≠ f.promise →
      ResolvingFunctions.callResolveSelf f t resolution selfError = none := by
  intro h
  simp [ResolvingFunctions.callResolveSelf, h]

/-! ### F6 — the settlement trace

DB-04's M2 order, as first-order data over the one table. `E-20` (generalize),
`G-06`; FULFILL, REJECT, WAITALL. WS-PROM-CE-030, WS-PROM-CE-031. -/

/-- **The no-second-table receipt** (R-P12): the table `settleTraced` returns is
`Table.settle`'s table, unchanged. Mask M1. -/
theorem Table.settleTraced_table {value reason : Type} (t : Table value reason)
    (tr : SettlementTrace value reason) (id : Nat) (result : Except reason value) :
    (Table.settleTraced t tr id result).1 = Table.settle t id result := by
  by_cases hp : Table.isPending t id = true
  · simp [Table.settleTraced, hp]
  · simp [Table.settleTraced, Table.settle, hp]

/-- A settling settle appends exactly one entry, at the tail. Mask M2: the
statement observes the order in which settlements happen. -/
theorem Table.settleTraced_pending {value reason : Type} (t : Table value reason)
    (tr : SettlementTrace value reason) (id : Nat) (result : Except reason value) :
    Table.get t id = some State.pending →
      (Table.settleTraced t tr id result).2 = tr ++ [(id, result)] := by
  intro h
  simp [Table.settleTraced, (Table.isPending_iff t id).mpr h]

/-- Decision 7's guard propagates to the trace: a non-pending settle is the
identity on both components, so no identity is recorded twice. Mask M1. -/
theorem Table.settleTraced_other {value reason : Type} (t : Table value reason)
    (tr : SettlementTrace value reason) (id : Nat) (result : Except reason value) :
    Table.get t id ≠ some State.pending →
      Table.settleTraced t tr id result = (t, tr) := by
  intro h
  have hfalse : Table.isPending t id = false := by
    cases hp : Table.isPending t id with
    | false => rfl
    | true => exact absurd ((Table.isPending_iff t id).mp hp) h
  simp [Table.settleTraced, hfalse]

/-- The defining equation. Mask M1. -/
theorem SettlementTrace.firstRejection_eq {value reason : Type}
    (tr : SettlementTrace value reason) (ids : List Nat) :
    SettlementTrace.firstRejection tr ids =
      List.findSome? (fun e =>
        if List.contains ids e.1 then
          match e.2 with
          | Except.error r => some r
          | Except.ok _ => none
        else none) tr := rfl

/-- The answer is the reason of the earliest *trace* entry that is a rejection
of an argument identity, which is `op.wait-for-all`'s "first rejection to
settle" and not the first rejection in argument order. Mask M2: the statement
observes the settlement order and nothing else. -/
theorem SettlementTrace.firstRejection_hit {value reason : Type}
    (before after : SettlementTrace value reason) (id : Nat) (r : reason) (ids : List Nat) :
    List.contains ids id = true →
    (∀ e ∈ before, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
      SettlementTrace.firstRejection (before ++ (id, Except.error r) :: after) ids = some r := by
  intro hid hbefore
  have key : ∀ (l : SettlementTrace value reason),
      (∀ e ∈ l, List.contains ids e.1 = false ∨ ∃ v : value, e.2 = Except.ok v) →
        SettlementTrace.firstRejection (l ++ (id, Except.error r) :: after) ids = some r := by
    intro l
    induction l with
    | nil =>
        intro _
        simp only [List.nil_append, SettlementTrace.firstRejection, List.findSome?_cons]
        rw [if_pos hid]
    | cons e rest ih =>
        intro h
        have hrest := ih (fun x hx => h x (List.mem_cons_of_mem e hx))
        have hnone :
            (if List.contains ids e.1 then
                match e.2 with
                | Except.error r' => some r'
                | Except.ok _ => none
              else none) = (none : Option reason) := by
          rcases h e (List.mem_cons_self ..) with hc | ⟨v, hv⟩
          · rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
          · rw [hv]
            split <;> rfl
        simp only [SettlementTrace.firstRejection] at hrest ⊢
        rw [List.cons_append, List.findSome?_cons, hnone]
        exact hrest
  exact key before hbefore

end Whatwg.Ecma262.Promise
