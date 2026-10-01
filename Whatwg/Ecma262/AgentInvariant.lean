import Whatwg.Ecma262.AgentLaws

/-!
# The stronger invariant and the second adequacy judgment of the agent

Owner: promise slice Q5, addendum Q5b (rulings R-W16, R-W20, R-W1(b), R-W9), graph
`PROMISE-PG-AGENT` (`docs/PROMISE-AGENT-DAG.md`), at the surface
`test/contracts/promise-agent-q5.contract.md`, section "Addendum Q5b", freezes.
This module is builder slice B5; its battery is
`WhatwgTest/Ecma262/AgentInvariantContract.lean`.

What `WF` and the Q5 posts leave unsaid (debts D62 and D65), stated beside them
and changing none of them: the stronger invariant `Coherent`, which extends
`WF` with seven clauses; the stronger order `Extends`, which extends `Le` with
two; the two-state post `postFrom` and the second adequacy judgment
`ImplementsFrom` over the unchanged `pre`, one theorem per operation; the
reaction job's two completions (`callFunctions_resolve_reject`,
`finishJob_abrupt`, `finishJob_normal`) and the named departure
`finishJob_abrupt_dropped`; and the reachability corollary
`Coherent.reachable`.

`Coherent` is inductive: it holds at `Agent.empty` and every operation keeps it
from every agent it holds of (`Coherent.step`), so a consumer carries it through
its own proofs; it is not a characterization of the reachable agents.

Masks are DB-04's, written "DB-04 M1" and "DB-04 M2"; no declaration here spells
a mask. A law that concludes `Extends` is DB-04 M2, through `Le.trace` and
`heldGrows`, and so is a law that observes the queue's or the trace's order.

Not modelled, as in `Whatwg/Ecma262/Agent.lean`: thenable adoption (`G-05`),
under which a fired function leaves its promise pending and the posts of
`resolve` and `finishJob` here must weaken; the rejection tracker (the `G-02`
remainder), so the result `finishJob_abrupt_dropped` drops is reported nowhere;
job callbacks (the `G-07` remainder).

Layering (DB-11): this module imports `Whatwg.Ecma262.AgentLaws` and nothing
else, so no `Effects` module and no `Whatwg.Infra` module. The proofs here
use the lemmas of `Whatwg/Ecma262/AgentLaws.lean` about the table, the reaction
lists and the uniqueness of a stored function record that ruling R-W20(c) made
public; this module copies no proof. Every other lemma here is private.
-/

namespace Whatwg.Ecma262.Agent

/-! ## 1. Definitions -/

/-- The agent's stronger invariant: `WF` and seven clauses by which the stores
cohere with one another as the specification's algorithms leave them. Gaps A to
F of the Q5b addendum; each clause is frozen by its projection. Invariant; no
census row. -/
structure Coherent {value reason body : Type} (a : Agent value reason body) : Prop
    extends WF a where
  /-- No two stored function records name one promise (NEWCAP with RESOLVING:
  one pair of resolving functions per promise). Keeps `unfiredPending`
  inductive. -/
  functionPromisesNodup : (a.functions.map Promise.ResolvingFunctions.promise).Nodup
  /-- An unfired function's promise is pending (gap A): only a promise's own
  functions settle it, after setting their shared marker (RESOLVING). True only
  while thenable adoption (`G-05`) is out. -/
  unfiredPending : ∀ f ∈ a.functions, f.alreadyResolved = false →
    Promise.Table.isPending a.table f.promise = true
  /-- Every settled cell is in the settlement trace with its result (gap B, the
  other half of debt D20). -/
  settledTraced :
    (∀ (p : Nat) (v : value), Promise.Table.get a.table p = some (Promise.State.fulfilled v) →
        (p, Except.ok v) ∈ a.settlements) ∧
      (∀ (p : Nat) (r : reason), Promise.Table.get a.table p = some (Promise.State.rejected r) →
        (p, Except.error r) ∈ a.settlements)
  /-- A waiting reaction waits on a pending promise (gap C; FULFILL and REJECT
  steps 2 to 5). -/
  waitingPending : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject,
    r.phase = Promise.ReactionPhase.waiting →
      Promise.Table.get a.table r.promise = some Promise.State.pending
  /-- Every registered or held reaction names an allocated promise (gap E;
  `builtin.promise-executor`: a new promise's reaction lists are empty). -/
  reactionsAllocated : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
    (a.table.getCell r.promise).isSome = true
  /-- The fulfil list holds `~fulfill~` records and the reject list `~reject~`
  records (`field.promisereaction-records.Type`). Keeps `jobsTyped`
  inductive. -/
  listKinds :
    (∀ r ∈ a.reactions.fulfill, r.kind = Promise.ReactionType.fulfill) ∧
      (∀ r ∈ a.reactions.reject, r.kind = Promise.ReactionType.reject)
  /-- Every queued job and the running job name a record whose `[[Type]]` is the
  argument's tag and whose promise is settled with the argument (gaps D and F;
  REACTJOB step 1, TRIGGER). -/
  jobsTyped : ∀ j : Job value reason, (j ∈ a.queue.pending ∨ a.running = some j) →
    ∃ r : Promise.Reaction body, reactionOf a j = some r ∧
      (∀ v : value, j.argument = Except.ok v →
        r.kind = Promise.ReactionType.fulfill ∧
          Promise.Table.get a.table r.promise = some (Promise.State.fulfilled v)) ∧
      (∀ e : reason, j.argument = Except.error e →
        r.kind = Promise.ReactionType.reject ∧
          Promise.Table.get a.table r.promise = some (Promise.State.rejected e))

/-- The stronger world order: `Le` and two clauses (gap J). Adequacy definition;
its clauses are frozen by their projections. -/
structure Extends {value reason body : Type} (a a' : Agent value reason body) : Prop
    extends Le a a' where
  /-- A fired function record survives as it is, so its one-shot marker never
  clears (RESOLVING). -/
  markerKept : ∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ a'.functions
  /-- `held` only grows, at its end. -/
  heldGrows : a.held <+: a'.held

/-- The post of the second judgment: the Q5 post at the answering agent `a'`,
and what the step did relative to the agent `a` it started from (gaps A, D, E,
I). Adequacy definition; the nine `postFrom_*` equations fix it. -/
def postFrom {value reason body : Type} (a a' : Agent value reason body) :
    (op : Op value reason body) → Cert op → op.Answer → Prop
  | .newPromise, c, cap => post a' Op.newPromise c cap ∧
      ∀ r ∈ a'.reactions.fulfill ++ a'.reactions.reject ++ a'.held, r.promise ≠ cap.promise
  | .resolve cap v, c, ans => post a' (Op.resolve cap v) c ans ∧
      ∀ f ∈ a.functions, f.resolve = cap.resolve → f.alreadyResolved = false →
        Promise.Table.get a'.table cap.promise = some (Promise.State.fulfilled v)
  | .reject cap r, c, ans => post a' (Op.reject cap r) c ans ∧
      ∀ f ∈ a.functions, f.reject = cap.reject → f.alreadyResolved = false →
        Promise.Table.get a'.table cap.promise = some (Promise.State.rejected r)
  | .perform p onF onR d, c, ans => post a' (Op.perform p onF onR d) c ans
  | .markHandled p, c, ans => post a' (Op.markHandled p) c ans
  | .startJob, c, ans => post a' Op.startJob c ans ∧
      ∃ (j : Job value reason) (rest : List (Job value reason)),
        a.queue.pending = j :: rest ∧ a'.queue.pending = rest ∧ ans.map Prod.fst = some j
  | .finishJob d, c, ans => post a' (Op.finishJob d) c ans ∧
      ∃ (j : Job value reason) (r : Promise.Reaction body),
        a.running = some j ∧ reactionOf a j = some r ∧
        (r.capability = none →
          a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
        ∀ cap : Promise.Capability, r.capability = some cap →
          ∀ f ∈ a.functions, f.resolve = cap.resolve →
            (f.alreadyResolved = true →
              a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
            (f.alreadyResolved = false →
              (∀ v : value, Promise.reactionHandlerResult r j.argument d = Except.ok v →
                Promise.Table.get a'.table cap.promise = some (Promise.State.fulfilled v)) ∧
              (∀ e : reason, Promise.reactionHandlerResult r j.argument d = Except.error e →
                Promise.Table.get a'.table cap.promise = some (Promise.State.rejected e)))
  | .enterScript, c, ans => post a' Op.enterScript c ans
  | .leaveScript, c, ans => post a' Op.leaveScript c ans

/-- The second adequacy judgment of one operation: from an agent `Coherent`
holds of and a request the Q5 `pre` admits, the stepped agent is later in
`Extends`, `Coherent` again, and holds the answer in `postFrom`. Adequacy
definition; `ImplementsFrom_iff` fixes it. -/
def ImplementsFrom {value reason body : Type} (op : Op value reason body) : Prop :=
  ∀ (a : Agent value reason body) (c : Cert op), Coherent a → pre a op c →
    Extends a (step a op).1 ∧ Coherent (step a op).1 ∧
      postFrom a (step a op).1 op c (step a op).2

/-! ## Helpers about the table -/

/-- A settle changes no pending flag at another identity. -/
private theorem isPending_settle_other {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) (result : Except reason value) (hne : q ≠ p) :
    Promise.Table.isPending (Promise.Table.settle t p result) q =
      Promise.Table.isPending t q := by
  unfold Promise.Table.isPending
  rw [settle_get_other t p q result hne]

/-- A settle keeps whether a cell is allocated. -/
private theorem settle_isSome {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) (result : Except reason value) :
    (Promise.Table.getCell (Promise.Table.settle t p result) q).isSome =
      (Promise.Table.getCell t q).isSome :=
  (getCell_settle t p q result).1

/-- A pending identity is not a settled one. -/
private theorem ne_of_pending_settled {value reason : Type} (t : Promise.Table value reason)
    (p q : Nat) (s : Promise.State value reason)
    (hp : Promise.Table.get t p = some Promise.State.pending)
    (hq : Promise.Table.get t q = some s) (hs : s ≠ Promise.State.pending) : q ≠ p := by
  intro e
  rw [e, hp] at hq
  cases hq
  exact hs rfl

/-- After a settle at a pending `p`, `p` holds the result. -/
private theorem get_settle_self {value reason : Type} (t : Promise.Table value reason)
    (p : Nat) (result : Except reason value)
    (hp : Promise.Table.get t p = some Promise.State.pending) :
    (∀ v, result = Except.ok v →
        Promise.Table.get (Promise.Table.settle t p result) p =
          some (Promise.State.fulfilled v)) ∧
      (∀ e, result = Except.error e →
        Promise.Table.get (Promise.Table.settle t p result) p =
          some (Promise.State.rejected e)) := by
  refine ⟨fun v hv => ?_, fun e he => ?_⟩
  · subst hv; exact Promise.Table.settle_assert t p (Except.ok v) hp
  · subst he; exact Promise.Table.settle_assert t p (Except.error e) hp

/-- What `get` reads after an allocation, at any identity, under `WF`: the old
state below the cursor and the new one at it. -/
private theorem get_fresh_cases {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (o : Promise.State value reason) (p : Nat) :
    (p = a.table.next ∧ Promise.Table.get (Promise.Table.fresh a.table o).1 p = some o) ∨
      (p ≠ a.table.next ∧
        Promise.Table.get (Promise.Table.fresh a.table o).1 p = Promise.Table.get a.table p) := by
  cases hq : decide (p = a.table.next) with
  | true =>
      have e : p = a.table.next := of_decide_eq_true hq
      subst e
      exact Or.inl ⟨rfl, Promise.Table.fresh_get a.table o hw.getCell_next⟩
  | false =>
      have hne : p ≠ a.table.next := of_decide_eq_false hq
      refine Or.inr ⟨hne, ?_⟩
      unfold Promise.Table.get
      rw [Promise.Table.fresh_old a.table o p hne]


/-! ## Helpers about reactions and `reactionOf` -/

/-- A lookup by identity commutes with a map that keeps identities. -/
private theorem find_id_map {body : Type} (l : List (Promise.Reaction body))
    (g : Promise.Reaction body → Promise.Reaction body) (hg : ∀ r, (g r).id = r.id) (n : Nat) :
    (l.map g).find? (fun x => x.id == n) = (l.find? (fun x => x.id == n)).map g := by
  rw [List.find?_map]
  have : ((fun (x : Promise.Reaction body) => x.id == n) ∘ g) = (fun x => x.id == n) := by
    funext x
    show ((g x).id == n) = (x.id == n)
    rw [hg x]
  rw [this]

/-- A lookup by identity on a list with no repeated identity finds the member
of that identity. -/
private theorem find_id_of_mem {body : Type} (l : List (Promise.Reaction body))
    (hnd : (l.map Promise.Reaction.id).Nodup) (r : Promise.Reaction body) (hr : r ∈ l) :
    l.find? (fun x => x.id == r.id) = some r :=
  find?_unique l _ (fun g hg g' hg' h1 h2 =>
    eq_of_nodup_key Promise.Reaction.id l hnd g hg g' hg'
      ((beq_iff_eq.mp h1).trans (beq_iff_eq.mp h2).symm)) r hr (beq_iff_eq.mpr rfl)

/-- A lookup by identity finds nothing when every listed identity differs. -/
private theorem find_id_none {body : Type} (l : List (Promise.Reaction body)) (n : Nat)
    (h : ∀ x ∈ l, x.id ≠ n) : l.find? (fun x => x.id == n) = none :=
  List.find?_eq_none.mpr (fun x hx hb => h x hx (beq_iff_eq.mp hb))

/-- Maps that keep identities on the two lists: a record `reactionOf` found is
found again, mapped or not. -/
private theorem reactionOf_map {value reason body : Type} {a a' : Agent value reason body}
    (g g' : Promise.Reaction body → Promise.Reaction body)
    (hh : a'.held = a.held) (hf : a'.reactions.fulfill = a.reactions.fulfill.map g)
    (hr : a'.reactions.reject = a.reactions.reject.map g')
    (hg : ∀ r, (g r).id = r.id) (hg' : ∀ r, (g' r).id = r.id)
    (j : Job value reason) (r : Promise.Reaction body) (h : reactionOf a j = some r) :
    reactionOf a' j = some r ∨ reactionOf a' j = some (g r) ∨ reactionOf a' j = some (g' r) := by
  cases hfind : a.held.find? (fun x => x.id == j.reaction) with
  | some x =>
      rw [reactionOf_held a j x hfind] at h
      refine Or.inl ?_
      rw [reactionOf_held a' j x (by rw [hh]; exact hfind), h]
  | none =>
      have hfind' : a'.held.find? (fun x => x.id == j.reaction) = none := by
        rw [hh]; exact hfind
      cases harg : j.argument with
      | ok v =>
          rw [reactionOf_ok a j v hfind harg] at h
          rw [reactionOf_ok a' j v hfind' harg]
          refine Or.inr (Or.inl ?_)
          show a'.reactions.fulfill.find? (fun x => x.id == j.reaction) = some (g r)
          have h' : a.reactions.fulfill.find? (fun x => x.id == j.reaction) = some r := h
          rw [hf, find_id_map _ g hg, h']
          rfl
      | error e =>
          rw [reactionOf_error a j e hfind harg] at h
          rw [reactionOf_error a' j e hfind' harg]
          refine Or.inr (Or.inr ?_)
          show a'.reactions.reject.find? (fun x => x.id == j.reaction) = some (g' r)
          have h' : a.reactions.reject.find? (fun x => x.id == j.reaction) = some r := h
          rw [hr, find_id_map _ g' hg', h']
          rfl

/-- Appending to the two lists keeps every record `reactionOf` found. -/
private theorem reactionOf_append {value reason body : Type} {a a' : Agent value reason body}
    (xs ys : List (Promise.Reaction body))
    (hh : a'.held = a.held) (hf : a'.reactions.fulfill = a.reactions.fulfill ++ xs)
    (hr : a'.reactions.reject = a.reactions.reject ++ ys)
    (j : Job value reason) (r : Promise.Reaction body) (h : reactionOf a j = some r) :
    reactionOf a' j = some r := by
  cases hfind : a.held.find? (fun x => x.id == j.reaction) with
  | some x =>
      rw [reactionOf_held a j x hfind] at h
      rw [reactionOf_held a' j x (by rw [hh]; exact hfind), h]
  | none =>
      have hfind' : a'.held.find? (fun x => x.id == j.reaction) = none := by
        rw [hh]; exact hfind
      cases harg : j.argument with
      | ok v =>
          rw [reactionOf_ok a j v hfind harg] at h
          rw [reactionOf_ok a' j v hfind' harg]
          show a'.reactions.fulfill.find? (fun x => x.id == j.reaction) = some r
          have h' : a.reactions.fulfill.find? (fun x => x.id == j.reaction) = some r := h
          rw [hf, List.find?_append, h']
          rfl
      | error e =>
          rw [reactionOf_error a j e hfind harg] at h
          rw [reactionOf_error a' j e hfind' harg]
          show a'.reactions.reject.find? (fun x => x.id == j.reaction) = some r
          have h' : a.reactions.reject.find? (fun x => x.id == j.reaction) = some r := h
          rw [hr, List.find?_append, h']
          rfl

/-- Appending a record of another identity to `held` keeps every record
`reactionOf` found. -/
private theorem reactionOf_held_append {value reason body : Type} {a a' : Agent value reason body}
    (m : Promise.Reaction body) (hh : a'.held = a.held ++ [m])
    (hf : a'.reactions.fulfill = a.reactions.fulfill)
    (hrj : a'.reactions.reject = a.reactions.reject)
    (j : Job value reason) (hm : m.id ≠ j.reaction) (r : Promise.Reaction body)
    (h : reactionOf a j = some r) : reactionOf a' j = some r := by
  cases hfind : a.held.find? (fun x => x.id == j.reaction) with
  | some x =>
      rw [reactionOf_held a j x hfind] at h
      rw [reactionOf_held a' j x (by rw [hh, List.find?_append, hfind]; rfl), h]
  | none =>
      have hfind' : a'.held.find? (fun x => x.id == j.reaction) = none := by
        rw [hh, List.find?_append, hfind]
        show (List.find? (fun x => x.id == j.reaction) [m]) = none
        exact find_id_none [m] j.reaction (fun x hx => by
          rw [List.mem_singleton.mp hx]; exact hm)
      cases harg : j.argument with
      | ok v =>
          rw [reactionOf_ok a j v hfind harg] at h
          rw [reactionOf_ok a' j v hfind' harg]
          show a'.reactions.fulfill.find? (fun x => x.id == j.reaction) = some r
          rw [hf]
          exact h
      | error e =>
          rw [reactionOf_error a j e hfind harg] at h
          rw [reactionOf_error a' j e hfind' harg]
          show a'.reactions.reject.find? (fun x => x.id == j.reaction) = some r
          rw [hrj]
          exact h

/-- A record appended to `held` with an identity no held record has is what
`reactionOf` finds for a job of that identity. -/
private theorem reactionOf_held_new {value reason body : Type} {a a' : Agent value reason body}
    (m : Promise.Reaction body) (hh : a'.held = a.held ++ [m])
    (hfresh : ∀ x ∈ a.held, x.id ≠ m.id) (j : Job value reason) (hj : j.reaction = m.id) :
    reactionOf a' j = some m := by
  apply reactionOf_held
  rw [hh, List.find?_append, hj, find_id_none a.held m.id hfresh]
  show (List.find? (fun x => x.id == m.id) [m]) = some m
  rw [List.find?_cons_of_pos (p := fun (x : Promise.Reaction body) => x.id == m.id)
    (beq_iff_eq.mpr rfl)]

/-- A registered record that no held record shares an identity with, and whose
identity is unique in its list, is what `reactionOf` finds for a job of its
identity whose tag selects its list. -/
private theorem reactionOf_listed {value reason body : Type} (a : Agent value reason body)
    (hw : WF a) (r : Promise.Reaction body) (j : Job value reason) (hj : j.reaction = r.id) :
    ((∃ v, j.argument = Except.ok v) → r ∈ a.reactions.fulfill → reactionOf a j = some r) ∧
      ((∃ e, j.argument = Except.error e) → r ∈ a.reactions.reject → reactionOf a j = some r) := by
  have hnd := List.nodup_append.mp hw.heldDistinct
  have hfnd : (a.reactions.fulfill.map Promise.Reaction.id).Nodup := hnd.2.1
  have hrnd : (a.reactions.reject.map Promise.Reaction.id).Nodup := hw.paired ▸ hfnd
  have hheld : ∀ (x : Promise.Reaction body), r.id ∈ a.reactions.fulfill.map Promise.Reaction.id →
      x ∈ a.held → x.id ≠ r.id := fun x hrf hx e =>
    hnd.2.2 x.id (List.mem_map_of_mem hx) r.id hrf e
  refine ⟨fun ⟨v, hv⟩ hr => ?_, fun ⟨e, he⟩ hr => ?_⟩
  · have hnone : a.held.find? (fun x => x.id == j.reaction) = none := by
      rw [hj]
      exact find_id_none a.held r.id (fun x hx => hheld x (List.mem_map_of_mem hr) hx)
    rw [reactionOf_ok a j v hnone hv, hj]
    exact find_id_of_mem a.reactions.fulfill hfnd r hr
  · have hrf : r.id ∈ a.reactions.fulfill.map Promise.Reaction.id := by
      rw [hw.paired]; exact List.mem_map_of_mem hr
    have hnone : a.held.find? (fun x => x.id == j.reaction) = none := by
      rw [hj]
      exact find_id_none a.held r.id (fun x hx => hheld x hrf hx)
    rw [reactionOf_error a j e hnone he, hj]
    exact find_id_of_mem a.reactions.reject hrnd r hr

/-- `reactionOf` finds a record of the job's identity, held or registered. -/
private theorem reactionOf_mem {value reason body : Type} (a : Agent value reason body)
    (j : Job value reason) (r : Promise.Reaction body) (h : reactionOf a j = some r) :
    r.id = j.reaction ∧ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held := by
  cases hfind : a.held.find? (fun x => x.id == j.reaction) with
  | some x =>
      rw [reactionOf_held a j x hfind] at h
      cases h
      have hb : (r.id == j.reaction) = true :=
        List.find?_some (p := fun (y : Promise.Reaction body) => y.id == j.reaction) hfind
      exact ⟨beq_iff_eq.mp hb, List.mem_append_right _ (List.mem_of_find?_eq_some hfind)⟩
  | none =>
      cases harg : j.argument with
      | ok v =>
          rw [reactionOf_ok a j v hfind harg] at h
          have h' : a.reactions.fulfill.find? (fun x => x.id == j.reaction) = some r := h
          have hb : (r.id == j.reaction) = true :=
            List.find?_some (p := fun (y : Promise.Reaction body) => y.id == j.reaction) h'
          exact ⟨beq_iff_eq.mp hb,
            List.mem_append_left _ (List.mem_append_left _ (List.mem_of_find?_eq_some h'))⟩
      | error e =>
          rw [reactionOf_error a j e hfind harg] at h
          have h' : a.reactions.reject.find? (fun x => x.id == j.reaction) = some r := h
          have hb : (r.id == j.reaction) = true :=
            List.find?_some (p := fun (y : Promise.Reaction body) => y.id == j.reaction) h'
          exact ⟨beq_iff_eq.mp hb,
            List.mem_append_left _ (List.mem_append_right _ (List.mem_of_find?_eq_some h'))⟩

/-! ## The maps trigger-then-clear applies -/

/-- What a map does to a record: identity, promise, kind, capability and
handler kept, and a record left waiting was left alone and waits on another
promise. -/
private def Tame {body : Type} (p : Nat) (g : Promise.Reaction body → Promise.Reaction body) :
    Prop :=
  ∀ r, (g r).id = r.id ∧ (g r).promise = r.promise ∧ (g r).kind = r.kind ∧
    (g r).capability = r.capability ∧
    ((g r).phase = Promise.ReactionPhase.waiting → g r = r ∧ r.promise ≠ p)

/-- The guard both maps test. -/
private theorem guard_true {body : Type} (r : Promise.Reaction body) (p : Nat)
    (hp : r.promise = p) (hph : r.phase = Promise.ReactionPhase.waiting) :
    (r.promise == p && r.phase == Promise.ReactionPhase.waiting) = true := by
  rw [Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr hp, beq_iff_eq.mpr hph⟩

private theorem clear_tame {body : Type} (p : Nat) :
    Tame p (fun (r : Promise.Reaction body) =>
      if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
        { r with phase := Promise.ReactionPhase.done }
      else r) := by
  intro r
  show (if _ then _ else r).id = r.id ∧ (if _ then _ else r).promise = r.promise ∧
    (if _ then _ else r).kind = r.kind ∧ (if _ then _ else r).capability = r.capability ∧
    ((if _ then _ else r).phase = Promise.ReactionPhase.waiting → (if _ then _ else r) = r ∧
      r.promise ≠ p)
  split
  · exact ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩
  · next hc =>
      exact ⟨rfl, rfl, rfl, rfl, fun hph => ⟨rfl, fun hp => hc (guard_true r p hp hph)⟩⟩

private theorem advance_tame {body : Type} (p : Nat) :
    Tame p (fun (r : Promise.Reaction body) =>
      if r.promise == p && r.phase == Promise.ReactionPhase.waiting then
        { r with phase := Promise.ReactionPhase.queued r.id }
      else r) := by
  intro r
  show (if _ then _ else r).id = r.id ∧ (if _ then _ else r).promise = r.promise ∧
    (if _ then _ else r).kind = r.kind ∧ (if _ then _ else r).capability = r.capability ∧
    ((if _ then _ else r).phase = Promise.ReactionPhase.waiting → (if _ then _ else r) = r ∧
      r.promise ≠ p)
  split
  · exact ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩
  · next hc =>
      exact ⟨rfl, rfl, rfl, rfl, fun hph => ⟨rfl, fun hp => hc (guard_true r p hp hph)⟩⟩

/-- Tame maps compose. -/
private theorem tame_comp {body : Type} {p : Nat}
    {g g' : Promise.Reaction body → Promise.Reaction body}
    (hg : Tame p g) (hg' : Tame p g') : Tame p (fun r => g (g' r)) := by
  intro r
  obtain ⟨i1, p1, k1, c1, w1⟩ := hg (g' r)
  obtain ⟨i2, p2, k2, c2, w2⟩ := hg' r
  refine ⟨i1.trans i2, p1.trans p2, k1.trans k2, c1.trans c2, fun hw => ?_⟩
  obtain ⟨e1, _⟩ := w1 hw
  obtain ⟨e2, hne⟩ := w2 ((congrArg Promise.Reaction.phase e1).symm.trans hw)
  exact ⟨e1.trans e2, hne⟩
/-- Trigger-then-clear at either kind is a tame map on each list. -/
private theorem trigger_clear_tame {value reason body : Type} (rs : Promise.Reactions body)
    (p : Nat) (k : Promise.ReactionType) (argument : Except reason value)
    (q : Jobs.Queue (Jobs.ReactionJob (Except reason value))) :
    ∃ g g' : Promise.Reaction body → Promise.Reaction body,
      (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).fulfill =
          rs.fulfill.map g ∧
        (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).reject =
          rs.reject.map g' ∧
        (Promise.Reactions.clear (Promise.triggerReactions rs p k argument q).1 p).next =
          rs.next ∧
        Tame p g ∧ Tame p g' := by
  cases k with
  | fulfill =>
      refine ⟨_, _, ?_, rfl, rfl, tame_comp (clear_tame p) (advance_tame p), clear_tame p⟩
      show List.map _ (List.map _ rs.fulfill) = _
      rw [List.map_map]
      rfl
  | reject =>
      refine ⟨_, _, rfl, ?_, rfl, clear_tame p, tame_comp (clear_tame p) (advance_tame p)⟩
      show List.map _ (List.map _ rs.reject) = _
      rw [List.map_map]
      rfl

/-- A member of a tame image is an old member with the same identity, promise,
kind and capability. -/
private theorem mem_tame {body : Type} (p : Nat) (g : Promise.Reaction body → Promise.Reaction body)
    (hg : Tame p g) (l : List (Promise.Reaction body)) (r' : Promise.Reaction body)
    (h : r' ∈ l.map g) :
    ∃ r ∈ l, r'.id = r.id ∧ r'.promise = r.promise ∧ r'.kind = r.kind ∧
      r'.capability = r.capability ∧
      (r'.phase = Promise.ReactionPhase.waiting → r' = r ∧ r.promise ≠ p) := by
  obtain ⟨r, hr, e⟩ := List.mem_map.mp h
  subst e
  exact ⟨r, hr, hg r⟩

/-- A member of the waiting set names the promise and is on its kind's list:
the list half is `mem_waitingOn` with the kind made explicit. -/
private theorem waitingOn_cases {body : Type} (rs : Promise.Reactions body) (p : Nat)
    (k : Promise.ReactionType) (r : Promise.Reaction body)
    (h : r ∈ Promise.Reactions.waitingOn rs p k) :
    r.promise = p ∧
      ((k = Promise.ReactionType.fulfill ∧ r ∈ rs.fulfill) ∨
        (k = Promise.ReactionType.reject ∧ r ∈ rs.reject)) := by
  have hpred := (List.mem_filter.mp h).2
  rw [Bool.and_eq_true] at hpred
  refine ⟨beq_iff_eq.mp hpred.1, ?_⟩
  have hm := mem_waitingOn rs p k r h
  cases k with
  | fulfill => exact Or.inl ⟨rfl, hm⟩
  | reject => exact Or.inr ⟨rfl, hm⟩


/-! ## The clauses in two groups

`Coherent a` is `WF a`, the two function clauses `FunClauses a`, and the five
clauses over the table, the trace, the reactions and the jobs, `RestR a`. The
preservation proofs treat the groups apart, because marking a function record
touches only the first and settling only the second, except at the settled
promise. -/

/-- The two clauses over the stored function records. -/
private def FunClauses {value reason body : Type} (a : Agent value reason body) : Prop :=
  (a.functions.map Promise.ResolvingFunctions.promise).Nodup ∧
    ∀ f ∈ a.functions, f.alreadyResolved = false →
      Promise.Table.isPending a.table f.promise = true

/-- The five clauses over the table, the trace, the reactions and the jobs. -/
private structure RestR {value reason body : Type} (a : Agent value reason body) : Prop where
  settledTraced :
    (∀ (p : Nat) (v : value), Promise.Table.get a.table p = some (Promise.State.fulfilled v) →
        (p, Except.ok v) ∈ a.settlements) ∧
      (∀ (p : Nat) (r : reason), Promise.Table.get a.table p = some (Promise.State.rejected r) →
        (p, Except.error r) ∈ a.settlements)
  waitingPending : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject,
    r.phase = Promise.ReactionPhase.waiting →
      Promise.Table.get a.table r.promise = some Promise.State.pending
  reactionsAllocated : ∀ r ∈ a.reactions.fulfill ++ a.reactions.reject ++ a.held,
    (a.table.getCell r.promise).isSome = true
  listKinds :
    (∀ r ∈ a.reactions.fulfill, r.kind = Promise.ReactionType.fulfill) ∧
      (∀ r ∈ a.reactions.reject, r.kind = Promise.ReactionType.reject)
  jobsTyped : ∀ j : Job value reason, (j ∈ a.queue.pending ∨ a.running = some j) →
    ∃ r : Promise.Reaction body, reactionOf a j = some r ∧
      (∀ v : value, j.argument = Except.ok v →
        r.kind = Promise.ReactionType.fulfill ∧
          Promise.Table.get a.table r.promise = some (Promise.State.fulfilled v)) ∧
      (∀ e : reason, j.argument = Except.error e →
        r.kind = Promise.ReactionType.reject ∧
          Promise.Table.get a.table r.promise = some (Promise.State.rejected e))

private theorem Coherent.funClauses {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : FunClauses a :=
  ⟨h.functionPromisesNodup, h.unfiredPending⟩

private theorem Coherent.restR {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : RestR a :=
  ⟨h.settledTraced, h.waitingPending, h.reactionsAllocated, h.listKinds, h.jobsTyped⟩

private theorem Coherent.ofParts {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (hf : FunClauses a) (hr : RestR a) : Coherent a :=
  { toWF := hw
    functionPromisesNodup := hf.1
    unfiredPending := hf.2
    settledTraced := hr.settledTraced
    waitingPending := hr.waitingPending
    reactionsAllocated := hr.reactionsAllocated
    listKinds := hr.listKinds
    jobsTyped := hr.jobsTyped }

/-! ## `settle` on a pending promise -/

/-- What `settle` leaves on a pending promise, at the reaction kind `k` of the
result. -/
private def settledWith {value reason body : Type} (a : Agent value reason body) (p : Nat)
    (k : Promise.ReactionType) (result : Except reason value) : Agent value reason body :=
  { a with
    table := Promise.Table.settle a.table p result
    reactions := Promise.Reactions.clear
      (Promise.triggerReactions a.reactions p k result a.queue).1 p
    queue := (Promise.triggerReactions a.reactions p k result a.queue).2
    settlements := a.settlements ++ [(p, result)] }

private theorem settle_settledWith {value reason body : Type} (a : Agent value reason body)
    (p : Nat) (result : Except reason value) (hp : Promise.Table.isPending a.table p = true) :
    ∃ k : Promise.ReactionType,
      (∀ v, result = Except.ok v → k = Promise.ReactionType.fulfill) ∧
      (∀ e, result = Except.error e → k = Promise.ReactionType.reject) ∧
      settle a p result = settledWith a p k result := by
  cases result with
  | ok v =>
      refine ⟨Promise.ReactionType.fulfill, fun _ _ => rfl, fun _ h => (by cases h), ?_⟩
      unfold settle Promise.Table.settleAndTrigger Promise.Table.settleTraced
      rw [hp]
      rfl
  | error e =>
      refine ⟨Promise.ReactionType.reject, fun _ h => (by cases h), fun _ _ => rfl, ?_⟩
      unfold settle Promise.Table.settleAndTrigger Promise.Table.settleTraced
      rw [hp]
      rfl

/-- The five clauses survive a settle of a pending promise. -/
private theorem RestR.settled {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (p : Nat) (k : Promise.ReactionType) (result : Except reason value)
    (hp : Promise.Table.get a.table p = some Promise.State.pending)
    (hk1 : ∀ v, result = Except.ok v → k = Promise.ReactionType.fulfill)
    (hk2 : ∀ e, result = Except.error e → k = Promise.ReactionType.reject) :
    RestR (settledWith a p k result) := by
  obtain ⟨g, g', hF, hR, _, hg, hg'⟩ :=
    trigger_clear_tame a.reactions p k result a.queue
  have hself := get_settle_self a.table p result hp
  -- An old settled state survives.
  have hkeep : ∀ (q : Nat) (s : Promise.State value reason), Promise.Table.get a.table q = some s →
      s ≠ Promise.State.pending →
        Promise.Table.get (Promise.Table.settle a.table p result) q = some s := by
    intro q s hq hs
    rw [settle_get_other a.table p q result (ne_of_pending_settled a.table p q s hp hq hs)]
    exact hq
  refine ⟨⟨fun q v hq => ?_, fun q x hq => ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- settledTraced, fulfilled
    show (q, Except.ok v) ∈ a.settlements ++ [(p, result)]
    have hq' : Promise.Table.get (Promise.Table.settle a.table p result) q =
        some (Promise.State.fulfilled v) := hq
    cases hqp : decide (q = p) with
    | true =>
        have e : q = p := of_decide_eq_true hqp
        subst e
        cases result with
        | ok w =>
            rw [hself.1 w rfl] at hq'
            cases hq'
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        | error w =>
            rw [hself.2 w rfl] at hq'
            cases hq'
    | false =>
        have hne : q ≠ p := of_decide_eq_false hqp
        rw [settle_get_other a.table p q result hne] at hq'
        exact List.mem_append_left _ (h.settledTraced.1 q v hq')
  · -- settledTraced, rejected
    show (q, Except.error x) ∈ a.settlements ++ [(p, result)]
    have hq' : Promise.Table.get (Promise.Table.settle a.table p result) q =
        some (Promise.State.rejected x) := hq
    cases hqp : decide (q = p) with
    | true =>
        have e : q = p := of_decide_eq_true hqp
        subst e
        cases result with
        | ok w =>
            rw [hself.1 w rfl] at hq'
            cases hq'
        | error w =>
            rw [hself.2 w rfl] at hq'
            cases hq'
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    | false =>
        have hne : q ≠ p := of_decide_eq_false hqp
        rw [settle_get_other a.table p q result hne] at hq'
        exact List.mem_append_left _ (h.settledTraced.2 q x hq')
  · -- waitingPending
    intro r' hr' hw'
    show Promise.Table.get (Promise.Table.settle a.table p result) r'.promise =
      some Promise.State.pending
    have hmem : r' ∈ (a.reactions.fulfill.map g) ++ (a.reactions.reject.map g') := by
      rw [← hF, ← hR]; exact hr'
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨r, hr, _, _, _, _, hwait⟩ := mem_tame p g hg _ r' hm
      obtain ⟨e, hne⟩ := hwait hw'
      subst e
      rw [settle_get_other a.table p r'.promise result hne]
      exact h.waitingPending r' (List.mem_append_left _ hr) hw'
    · obtain ⟨r, hr, _, _, _, _, hwait⟩ := mem_tame p g' hg' _ r' hm
      obtain ⟨e, hne⟩ := hwait hw'
      subst e
      rw [settle_get_other a.table p r'.promise result hne]
      exact h.waitingPending r' (List.mem_append_right _ hr) hw'
  · -- reactionsAllocated
    intro r' hr'
    show (Promise.Table.getCell (Promise.Table.settle a.table p result) r'.promise).isSome = true
    rw [settle_isSome]
    have hmem : r' ∈ (a.reactions.fulfill.map g) ++ (a.reactions.reject.map g') ++ a.held := by
      rw [← hF, ← hR]; exact hr'
    rcases List.mem_append.mp hmem with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨r, hr, _, hpr, _⟩ := mem_tame p g hg _ r' hm
        rw [hpr]
        exact h.reactionsAllocated r (List.mem_append_left _ (List.mem_append_left _ hr))
      · obtain ⟨r, hr, _, hpr, _⟩ := mem_tame p g' hg' _ r' hm
        rw [hpr]
        exact h.reactionsAllocated r (List.mem_append_left _ (List.mem_append_right _ hr))
    · exact h.reactionsAllocated r' (List.mem_append_right _ hm)
  · -- listKinds, fulfil
    intro r' hr'
    have hm : r' ∈ a.reactions.fulfill.map g := by rw [← hF]; exact hr'
    obtain ⟨r, hr, _, _, hk, _⟩ := mem_tame p g hg _ r' hm
    rw [hk]
    exact h.listKinds.1 r hr
  · -- listKinds, reject
    intro r' hr'
    have hm : r' ∈ a.reactions.reject.map g' := by rw [← hR]; exact hr'
    obtain ⟨r, hr, _, _, hk, _⟩ := mem_tame p g' hg' _ r' hm
    rw [hk]
    exact h.listKinds.2 r hr
  · -- jobsTyped
    have hmapped : ∀ (j : Job value reason) (r : Promise.Reaction body),
        reactionOf a j = some r →
          ∃ r' : Promise.Reaction body, reactionOf (settledWith a p k result) j = some r' ∧
            r'.kind = r.kind ∧ r'.promise = r.promise := by
      intro j r hj
      rcases reactionOf_map (a := a) (a' := settledWith a p k result) g g' rfl hF hR
          (fun r => (hg r).1) (fun r => (hg' r).1) j r hj with e | e | e
      · exact ⟨r, e, rfl, rfl⟩
      · exact ⟨g r, e, (hg r).2.2.1, (hg r).2.1⟩
      · exact ⟨g' r, e, (hg' r).2.2.1, (hg' r).2.1⟩
    -- An old job: its record is found again, and its settled state survives.
    have hold : ∀ (j : Job value reason), (j ∈ a.queue.pending ∨ a.running = some j) →
        ∃ r : Promise.Reaction body, reactionOf (settledWith a p k result) j = some r ∧
          (∀ v : value, j.argument = Except.ok v →
            r.kind = Promise.ReactionType.fulfill ∧
              Promise.Table.get (settledWith a p k result).table r.promise =
                some (Promise.State.fulfilled v)) ∧
          (∀ e : reason, j.argument = Except.error e →
            r.kind = Promise.ReactionType.reject ∧
              Promise.Table.get (settledWith a p k result).table r.promise =
                some (Promise.State.rejected e)) := by
      intro j hj
      obtain ⟨r, hr, hok, herr⟩ := h.jobsTyped j hj
      obtain ⟨r', hr', hk', hp'⟩ := hmapped j r hr
      refine ⟨r', hr', fun v hv => ?_, fun e he => ?_⟩
      · obtain ⟨k1, s1⟩ := hok v hv
        exact ⟨hk'.trans k1, hp' ▸ hkeep r.promise _ s1 (fun x => by cases x)⟩
      · obtain ⟨k1, s1⟩ := herr e he
        exact ⟨hk'.trans k1, hp' ▸ hkeep r.promise _ s1 (fun x => by cases x)⟩
    intro j hj
    rcases hj with hq | hrun
    · have hq' : j ∈ a.queue.pending ++ (Promise.Reactions.waitingOn a.reactions p k).map
          (fun r => Jobs.ReactionJob.mk r.id result) := by
        rw [← Promise.triggerReactions_order]; exact hq
      rcases List.mem_append.mp hq' with hq0 | hnew
      · exact hold j (Or.inl hq0)
      · obtain ⟨r, hr, e⟩ := List.mem_map.mp hnew
        subst e
        obtain ⟨hrp, hlist⟩ := waitingOn_cases a.reactions p k r hr
        -- The record of the new job is `r`, found again after the maps.
        have hfound : reactionOf a (Jobs.ReactionJob.mk r.id result) = some r := by
          have hl := reactionOf_listed a h.toWF r (Jobs.ReactionJob.mk r.id result) rfl
          rcases hlist with ⟨hkf, hrf⟩ | ⟨hkr, hrr⟩
          · cases result with
            | ok v => exact hl.1 ⟨v, rfl⟩ hrf
            | error e => exact absurd ((hk2 e rfl).symm.trans hkf) (by intro x; cases x)
          · cases result with
            | ok v => exact absurd ((hk1 v rfl).symm.trans hkr) (by intro x; cases x)
            | error e => exact hl.2 ⟨e, rfl⟩ hrr
        obtain ⟨r', hr', hk', hp'⟩ := hmapped _ r hfound
        refine ⟨r', hr', fun v hv => ?_, fun e he => ?_⟩
        · have hres : result = Except.ok v := hv
          have hkind : r.kind = Promise.ReactionType.fulfill := by
            rcases hlist with ⟨_, hrf⟩ | ⟨hkr, _⟩
            · exact h.listKinds.1 r hrf
            · exact absurd ((hk1 v hres).symm.trans hkr) (by intro x; cases x)
          refine ⟨hk'.trans hkind, ?_⟩
          show Promise.Table.get (Promise.Table.settle a.table p result) r'.promise = _
          rw [hp', hrp]
          exact hself.1 v hres
        · have hres : result = Except.error e := he
          have hkind : r.kind = Promise.ReactionType.reject := by
            rcases hlist with ⟨hkf, _⟩ | ⟨_, hrr⟩
            · exact absurd ((hk2 e hres).symm.trans hkf) (by intro x; cases x)
            · exact h.listKinds.2 r hrr
          refine ⟨hk'.trans hkind, ?_⟩
          show Promise.Table.get (Promise.Table.settle a.table p result) r'.promise = _
          rw [hp', hrp]
          exact hself.2 e hres
    · exact hold j (Or.inr hrun)

/-- The five clauses read no function record. -/
private theorem RestR.withFunctions {value reason body : Type} {b : Agent value reason body}
    (h : RestR b) (fs : List Promise.ResolvingFunctions) : RestR { b with functions := fs } :=
  ⟨h.settledTraced, h.waitingPending, h.reactionsAllocated, h.listKinds, h.jobsTyped⟩

/-! ## `callFunctions` -/

/-- After `callFunctions`, with any pick, the two function clauses and the five
others hold: a record the pick selects is marked, and every other record names
another promise than the settled one (`functionPromisesNodup`). -/
private theorem parts_callFunctions {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value) :
    FunClauses (callFunctions a pick result) ∧ RestR (callFunctions a pick result) := by
  cases hf : a.functions.find? pick with
  | none =>
      rw [callFunctions_none a pick result hf]; exact ⟨h.funClauses, h.restR⟩
  | some f =>
      cases hfr : f.alreadyResolved with
      | true => rw [callFunctions_fired a pick result f hf hfr]; exact ⟨h.funClauses, h.restR⟩
      | false =>
          rw [callFunctions_fresh a pick result f hf hfr]
          have hfm : f ∈ a.functions := List.mem_of_find?_eq_some hf
          have hfp : pick f = true := List.find?_some hf
          have hpb : Promise.Table.isPending a.table f.promise = true :=
            h.unfiredPending f hfm hfr
          have hpend : Promise.Table.get a.table f.promise = some Promise.State.pending :=
            (Promise.Table.isPending_iff a.table f.promise).mp hpb
          obtain ⟨k, hk1, hk2, he⟩ := settle_settledWith a f.promise result hpb
          rw [he]
          have hrest := RestR.settled h f.promise k result hpend hk1 hk2
          refine ⟨⟨?_, ?_⟩, RestR.withFunctions hrest _⟩
          · show ((a.functions.map _).map Promise.ResolvingFunctions.promise).Nodup
            rw [List.map_map]
            have : (Promise.ResolvingFunctions.promise ∘ (fun g =>
                if pick g then { g with alreadyResolved := true } else g)) =
                Promise.ResolvingFunctions.promise := by
              funext g
              exact (mark_fields pick g).2.2
            rw [this]
            exact h.functionPromisesNodup
          · intro g' hg'
            obtain ⟨g, hg, e⟩ := List.mem_map.mp hg'
            subst e
            cases hpg : pick g with
            | true => intro hgr; cases hgr
            | false =>
                intro hgr
                show Promise.Table.isPending (Promise.Table.settle a.table f.promise result)
                  g.promise = true
                have hne : g.promise ≠ f.promise := fun e => by
                  have hgf := eq_of_nodup_key Promise.ResolvingFunctions.promise a.functions
                    h.functionPromisesNodup g hg f hfm e
                  rw [hgf] at hpg
                  rw [hpg] at hfp
                  exact Bool.false_ne_true hfp
                rw [isPending_settle_other a.table f.promise g.promise result hne]
                exact h.unfiredPending g hg hgr


/-! ## The other operations -/

/-- A table change that keeps every state and every allocation keeps the
seven clauses. -/
private theorem parts_table {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (t : Promise.Table value reason)
    (hget : ∀ q, Promise.Table.get t q = Promise.Table.get a.table q)
    (hsome : ∀ q, (Promise.Table.getCell t q).isSome = (Promise.Table.getCell a.table q).isSome) :
    FunClauses { a with table := t } ∧ RestR { a with table := t } := by
  have hpend : ∀ q, Promise.Table.isPending t q = Promise.Table.isPending a.table q := by
    intro q; unfold Promise.Table.isPending; rw [hget]
  refine ⟨⟨h.functionPromisesNodup, fun f hf hfr => ?_⟩,
    ⟨⟨fun q v hq => ?_, fun q x hq => ?_⟩, fun r hr hw => ?_, fun r hr => ?_, h.listKinds,
      fun j hj => ?_⟩⟩
  · show Promise.Table.isPending t f.promise = true
    rw [hpend]; exact h.unfiredPending f hf hfr
  · have hq' : Promise.Table.get t q = _ := hq
    rw [hget] at hq'; exact h.settledTraced.1 q v hq'
  · have hq' : Promise.Table.get t q = _ := hq
    rw [hget] at hq'; exact h.settledTraced.2 q x hq'
  · show Promise.Table.get t r.promise = _
    rw [hget]; exact h.waitingPending r hr hw
  · show (Promise.Table.getCell t r.promise).isSome = true
    rw [hsome]; exact h.reactionsAllocated r hr
  · obtain ⟨r, hr, hok, herr⟩ := h.jobsTyped j hj
    refine ⟨r, hr, fun v hv => ?_, fun e he => ?_⟩
    · obtain ⟨k1, s1⟩ := hok v hv
      refine ⟨k1, ?_⟩
      show Promise.Table.get t r.promise = _
      rw [hget]; exact s1
    · obtain ⟨k1, s1⟩ := herr e he
      refine ⟨k1, ?_⟩
      show Promise.Table.get t r.promise = _
      rw [hget]; exact s1

/-- `newPromise` keeps the seven clauses. -/
private theorem parts_newPromise {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : FunClauses (newPromise a).1 ∧ RestR (newPromise a).1 := by
  have hw := h.toWF
  have hlt : ∀ f ∈ a.functions, f.promise < a.table.next := fun f hf =>
    hw.getCell_lt (hw.functionsAllocated f hf)
  -- The state at any identity after allocation.
  have hcases := get_fresh_cases hw (Promise.State.pending : Promise.State value reason)
  have hkeep : ∀ (q : Nat) (s : Promise.State value reason), Promise.Table.get a.table q = some s →
      Promise.Table.get (Promise.Table.fresh a.table Promise.State.pending).1 q = some s :=
    fun q s hq => get_fresh a.table _ q s hq
  have hback : ∀ (q : Nat) (s : Promise.State value reason),
      Promise.Table.get (Promise.Table.fresh a.table Promise.State.pending).1 q = some s →
        s ≠ Promise.State.pending → Promise.Table.get a.table q = some s := by
    intro q s hq hs
    rcases hcases q with ⟨_, e⟩ | ⟨_, e⟩
    · rw [e] at hq; cases hq; exact absurd rfl hs
    · rw [e] at hq; exact hq
  refine ⟨⟨?_, fun f hf hfr => ?_⟩,
    ⟨⟨fun q v hq => ?_, fun q x hq => ?_⟩, fun r hr hwt => ?_, fun r hr => ?_, h.listKinds,
      fun j hj => ?_⟩⟩
  · show ((a.functions ++ [Promise.createResolvingFunctions a.table.next a.nextFunction]).map
      Promise.ResolvingFunctions.promise).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨h.functionPromisesNodup,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy
    obtain ⟨f, hf, e⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy, ← e]
    exact Nat.ne_of_lt (hlt f hf)
  · show Promise.Table.isPending (Promise.Table.fresh a.table Promise.State.pending).1
      f.promise = true
    rcases List.mem_append.mp hf with hold | hnew
    · unfold Promise.Table.isPending
      rcases hcases f.promise with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (Nat.ne_of_lt (hlt f hold))
      · rw [e]
        have := h.unfiredPending f hold hfr
        unfold Promise.Table.isPending at this
        exact this
    · rw [List.mem_singleton.mp hnew]
      show Promise.Table.isPending (Promise.Table.fresh a.table Promise.State.pending).1
        a.table.next = true
      unfold Promise.Table.isPending
      rw [Promise.Table.fresh_get a.table Promise.State.pending hw.getCell_next]
  · exact h.settledTraced.1 q v (hback q _ hq (fun x => by cases x))
  · exact h.settledTraced.2 q x (hback q _ hq (fun x => by cases x))
  · exact hkeep r.promise _ (h.waitingPending r hr hwt)
  · exact getCell_fresh_isSome a.table _ r.promise (h.reactionsAllocated r hr)
  · obtain ⟨r, hr, hok, herr⟩ := h.jobsTyped j hj
    refine ⟨r, hr, fun v hv => ?_, fun e he => ?_⟩
    · obtain ⟨k1, s1⟩ := hok v hv
      exact ⟨k1, hkeep r.promise _ s1⟩
    · obtain ⟨k1, s1⟩ := herr e he
      exact ⟨k1, hkeep r.promise _ s1⟩

/-- `newPromise` keeps `Coherent`. -/
private theorem Coherent.newPromise {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : Coherent (Whatwg.Ecma262.Agent.newPromise a).1 :=
  Coherent.ofParts (WF.step a Op.newPromise h.toWF) (parts_newPromise h).1
    (parts_newPromise h).2

/-- Minting keeps `Coherent`. -/
private theorem Coherent.mintFor {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (d : Bool) : Coherent (Whatwg.Ecma262.Agent.mintFor a d).1 := by
  cases d with
  | false => exact h
  | true => exact Coherent.newPromise h

/-- The pending branch of `perform` keeps the seven clauses. -/
private theorem parts_performPending {value reason body : Type} {b : Agent value reason body}
    (h : Coherent b) (p : Nat) (hp : Promise.Table.get b.table p = some Promise.State.pending)
    (rs : Promise.Reactions body) (hrs : b.reactions = rs)
    (onFulfilled onRejected : Option body) (cap : Option Promise.Capability) :
    FunClauses { b with
        table := Promise.Table.markHandled b.table p,
        reactions := (Promise.Reactions.add rs p onFulfilled onRejected cap).1 } ∧
      RestR { b with
        table := Promise.Table.markHandled b.table p,
        reactions := (Promise.Reactions.add rs p onFulfilled onRejected cap).1 } := by
  subst hrs
  have hm := parts_table h (Promise.Table.markHandled b.table p)
    (fun q => markHandled_get b.table p q) (fun q => markHandled_isSome b.table p q)
  refine ⟨hm.1, ⟨hm.2.settledTraced, fun r hr hw => ?_, fun r hr => ?_, ⟨?_, ?_⟩,
    fun j hj => ?_⟩⟩
  · show Promise.Table.get (Promise.Table.markHandled b.table p) r.promise = _
    rw [markHandled_get]
    have hr' : r ∈ (b.reactions.fulfill ++ [_]) ++ (b.reactions.reject ++ [_]) := hr
    rcases List.mem_append.mp hr' with hf | hrj
    · rcases List.mem_append.mp hf with hold | hnew
      · exact h.waitingPending r (List.mem_append_left _ hold) hw
      · rw [List.mem_singleton.mp hnew]; exact hp
    · rcases List.mem_append.mp hrj with hold | hnew
      · exact h.waitingPending r (List.mem_append_right _ hold) hw
      · rw [List.mem_singleton.mp hnew]; exact hp
  · show (Promise.Table.getCell (Promise.Table.markHandled b.table p) r.promise).isSome = true
    rw [markHandled_isSome]
    have hr' : r ∈ (b.reactions.fulfill ++ [_]) ++ (b.reactions.reject ++ [_]) ++ b.held := hr
    rcases List.mem_append.mp hr' with hl | hh
    · rcases List.mem_append.mp hl with hf | hrj
      · rcases List.mem_append.mp hf with hold | hnew
        · exact h.reactionsAllocated r (List.mem_append_left _ (List.mem_append_left _ hold))
        · rw [List.mem_singleton.mp hnew]; exact getCell_isSome_of_get _ _ _ hp
      · rcases List.mem_append.mp hrj with hold | hnew
        · exact h.reactionsAllocated r (List.mem_append_left _ (List.mem_append_right _ hold))
        · rw [List.mem_singleton.mp hnew]; exact getCell_isSome_of_get _ _ _ hp
    · exact h.reactionsAllocated r (List.mem_append_right _ hh)
  · intro r hr
    have hr' : r ∈ b.reactions.fulfill ++ [_] := hr
    rcases List.mem_append.mp hr' with hold | hnew
    · exact h.listKinds.1 r hold
    · rw [List.mem_singleton.mp hnew]
  · intro r hr
    have hr' : r ∈ b.reactions.reject ++ [_] := hr
    rcases List.mem_append.mp hr' with hold | hnew
    · exact h.listKinds.2 r hold
    · rw [List.mem_singleton.mp hnew]
  · obtain ⟨r, hr, hok, herr⟩ := hm.2.jobsTyped j hj
    have hr' := reactionOf_append (a := { b with table := Promise.Table.markHandled b.table p })
      (a' := { b with
        table := Promise.Table.markHandled b.table p,
        reactions := (Promise.Reactions.add b.reactions p onFulfilled onRejected cap).1 })
      _ _ rfl rfl rfl j r hr
    exact ⟨r, hr', hok, herr⟩

/-- A settled branch of `perform` keeps the seven clauses. -/
private theorem parts_performSettled {value reason body : Type} {b : Agent value reason body}
    (h : Coherent b) (p : Nat) (kind : Promise.ReactionType) (handler : Option body)
    (cap : Option Promise.Capability) (arg : Except reason value)
    (hst : (∀ v, arg = Except.ok v → kind = Promise.ReactionType.fulfill ∧
        Promise.Table.get b.table p = some (Promise.State.fulfilled v)) ∧
      (∀ e, arg = Except.error e → kind = Promise.ReactionType.reject ∧
        Promise.Table.get b.table p = some (Promise.State.rejected e))) :
    FunClauses { b with
        table := Promise.Table.markHandled b.table p,
        reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
        queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
        held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] } ∧
      RestR { b with
        table := Promise.Table.markHandled b.table p,
        reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
        queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
        held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] } := by
  have hw := h.toWF
  have hm := parts_table h (Promise.Table.markHandled b.table p)
    (fun q => markHandled_get b.table p q) (fun q => markHandled_isSome b.table p q)
  have hpalloc : (Promise.Table.getCell b.table p).isSome = true := by
    cases arg with
    | ok v => exact getCell_isSome_of_get _ _ _ (hst.1 v rfl).2
    | error e => exact getCell_isSome_of_get _ _ _ (hst.2 e rfl).2
  have hheldlt : ∀ x ∈ b.held, x.id ≠ b.reactions.next := fun x hx =>
    Nat.ne_of_lt (hw.reactionsBelow x (List.mem_append_right _ hx))
  refine ⟨hm.1, ⟨hm.2.settledTraced, hm.2.waitingPending, fun r hr => ?_, h.listKinds,
    fun j hj => ?_⟩⟩
  · show (Promise.Table.getCell (Promise.Table.markHandled b.table p) r.promise).isSome = true
    rw [markHandled_isSome]
    have hr' : r ∈ b.reactions.fulfill ++ b.reactions.reject ++
        (b.held ++ [Promise.Reaction.mk b.reactions.next p kind handler cap
          (Promise.ReactionPhase.queued b.reactions.next)]) := hr
    rcases List.mem_append.mp hr' with hl | hh
    · exact h.reactionsAllocated r (List.mem_append_left _ hl)
    · rcases List.mem_append.mp hh with hold | hnew
      · exact h.reactionsAllocated r (List.mem_append_right _ hold)
      · rw [List.mem_singleton.mp hnew]; exact hpalloc
  · have hj' : j ∈ b.queue.pending ++ [Jobs.ReactionJob.mk b.reactions.next arg] ∨
        b.running = some j := hj
    rcases hj' with hq | hrun
    · rcases List.mem_append.mp hq with hold | hnew
      · obtain ⟨r, hr, hok, herr⟩ := hm.2.jobsTyped j (Or.inl hold)
        have hr' := reactionOf_held_append (a := { b with
            table := Promise.Table.markHandled b.table p })
          (a' := { b with
            table := Promise.Table.markHandled b.table p,
            reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
            queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
            held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] })
          _ rfl rfl rfl j (Nat.ne_of_lt (hw.queueBelow j hold)).symm r hr
        exact ⟨r, hr', hok, herr⟩
      · rw [List.mem_singleton.mp hnew]
        refine ⟨_, reactionOf_held_new (a := b) (a' := { b with
            table := Promise.Table.markHandled b.table p,
            reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
            queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
            held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] })
          _ rfl hheldlt _ rfl,
          fun v hv => ?_, fun e he => ?_⟩
        · obtain ⟨k1, s1⟩ := hst.1 v hv
          exact ⟨k1, (markHandled_get b.table p p).trans s1⟩
        · obtain ⟨k1, s1⟩ := hst.2 e he
          exact ⟨k1, (markHandled_get b.table p p).trans s1⟩
    · obtain ⟨r, hr, hok, herr⟩ := hm.2.jobsTyped j (Or.inr hrun)
      have hlt : j.reaction < b.reactions.next := by
        obtain ⟨hid, hmem⟩ := reactionOf_mem b j r hr
        rw [← hid]
        exact hw.reactionsBelow r hmem
      have hr' := reactionOf_held_append (a := { b with
          table := Promise.Table.markHandled b.table p })
        (a' := { b with
            table := Promise.Table.markHandled b.table p,
            reactions := (Promise.Reactions.mint b.reactions p kind handler cap).1,
            queue := Jobs.Queue.enqueue b.queue (Jobs.ReactionJob.mk b.reactions.next arg),
            held := b.held ++ [(Promise.Reactions.mint b.reactions p kind handler cap).2] })
        _ rfl rfl rfl j (Nat.ne_of_lt hlt).symm r hr
      exact ⟨r, hr', hok, herr⟩

/-- `perform` keeps the seven clauses, on every branch. -/
private theorem parts_perform {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (p : Nat) (onFulfilled onRejected : Option body) (d : Bool) :
    FunClauses (perform a p onFulfilled onRejected d).1 ∧
      RestR (perform a p onFulfilled onRejected d).1 := by
  have hb := Coherent.mintFor h d
  have hrs : (Whatwg.Ecma262.Agent.mintFor a d).1.reactions = a.reactions := by
    cases d <;> rfl
  have hq : (Whatwg.Ecma262.Agent.mintFor a d).1.queue = a.queue := by cases d <;> rfl
  have hhe : (Whatwg.Ecma262.Agent.mintFor a d).1.held = a.held := by cases d <;> rfl
  have hget : ∀ (s : Promise.State value reason), Promise.Table.get a.table p = some s →
      Promise.Table.get (Whatwg.Ecma262.Agent.mintFor a d).1.table p = some s := by
    intro s hs
    cases d with
    | false => exact hs
    | true => exact get_fresh a.table _ p s hs
  cases hg : a.table.get p with
  | none => rw [perform_missing a p onFulfilled onRejected d hg]; exact ⟨h.funClauses, h.restR⟩
  | some s =>
      cases s with
      | pending =>
          rw [perform_pending a p onFulfilled onRejected d hg]
          exact parts_performPending hb p (hget _ hg) a.reactions hrs onFulfilled onRejected _
      | fulfilled v =>
          rw [perform_fulfilled a p v onFulfilled onRejected d hg]
          have := parts_performSettled hb p Promise.ReactionType.fulfill onFulfilled
            (Whatwg.Ecma262.Agent.mintFor a d).2 (Except.ok v)
            ⟨fun w hw => (by cases hw; exact ⟨rfl, hget _ hg⟩), fun e he => (by cases he)⟩
          rw [hrs, hq, hhe] at this
          exact this
      | rejected x =>
          rw [perform_rejected a p x onFulfilled onRejected d hg]
          have := parts_performSettled hb p Promise.ReactionType.reject onRejected
            (Whatwg.Ecma262.Agent.mintFor a d).2 (Except.error x)
            ⟨fun w hw => (by cases hw), fun e he => (by cases he; exact ⟨rfl, hget _ hg⟩)⟩
          rw [hrs, hq, hhe] at this
          exact this

/-- Returning to a checkpoint with nothing running keeps the seven clauses. -/
private theorem parts_idle {value reason body : Type} {b : Agent value reason body}
    (hf : FunClauses b) (hr : RestR b) (act : Jobs.Active) :
    FunClauses { b with active := act, running := none } ∧
      RestR { b with active := act, running := none } :=
  ⟨hf, ⟨hr.settledTraced, hr.waitingPending, hr.reactionsAllocated, hr.listKinds,
    fun j hj => by
      rcases hj with hq | hrun
      · exact hr.jobsTyped j (Or.inl hq)
      · cases hrun⟩⟩

/-- A change of the activation alone keeps the seven clauses. -/
private theorem parts_active {value reason body : Type} {b : Agent value reason body}
    (h : Coherent b) (act : Jobs.Active) :
    FunClauses { b with active := act } ∧ RestR { b with active := act } :=
  ⟨h.funClauses, ⟨h.settledTraced, h.waitingPending, h.reactionsAllocated, h.listKinds,
    h.jobsTyped⟩⟩

/-- `startJob` keeps the seven clauses. -/
private theorem parts_startJob {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : FunClauses (startJob a).1 ∧ RestR (startJob a).1 := by
  cases ha : a.active with
  | checkpoint =>
      cases hq : a.queue.pending with
      | nil => rw [startJob_empty a hq]; exact ⟨h.funClauses, h.restR⟩
      | cons job rest =>
          rw [startJob_checkpoint a job rest ha hq]
          refine ⟨h.funClauses, ⟨h.settledTraced, h.waitingPending, h.reactionsAllocated,
            h.listKinds, fun j hj => ?_⟩⟩
          rcases hj with hj | hj
          · exact h.jobsTyped j (Or.inl (by rw [hq]; exact List.mem_cons_of_mem job hj))
          · have e : job = j := Option.some.inj hj
            subst e
            exact h.jobsTyped job (Or.inl (by rw [hq]; exact List.mem_cons_self))
  | script =>
      rw [startJob_blocked a (by rw [ha]; exact fun x => by cases x)]
      exact ⟨h.funClauses, h.restR⟩
  | intrinsic _ =>
      rw [startJob_blocked a (by rw [ha]; exact fun x => by cases x)]
      exact ⟨h.funClauses, h.restR⟩
  | job _ =>
      rw [startJob_blocked a (by rw [ha]; exact fun x => by cases x)]
      exact ⟨h.funClauses, h.restR⟩

/-- `finishJob` keeps the seven clauses. -/
private theorem parts_finishJob {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (decision : Except reason value) :
    FunClauses (finishJob a decision) ∧ RestR (finishJob a decision) := by
  cases hrun : a.running with
  | none => rw [finishJob_idle a decision hrun]; exact ⟨h.funClauses, h.restR⟩
  | some job =>
      cases ha : a.active with
      | job s =>
          cases hr : reactionOf a job with
          | none =>
              rw [finishJob_unknown a decision s job ha hrun hr]
              exact parts_idle h.funClauses h.restR _
          | some r =>
              cases hc : r.capability with
              | none =>
                  rw [finishJob_no_capability a decision s job r ha hrun hr hc]
                  exact parts_idle h.funClauses h.restR _
              | some cap =>
                  rw [finishJob_capability a decision s job r cap ha hrun hr hc]
                  have hp := parts_callFunctions h
                    (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
                    (Promise.reactionHandlerResult r job.argument decision)
                  exact parts_idle hp.1 hp.2 _
      | checkpoint =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ x => by cases x)]
          exact ⟨h.funClauses, h.restR⟩
      | script =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ x => by cases x)]
          exact ⟨h.funClauses, h.restR⟩
      | intrinsic _ =>
          rw [finishJob_not_job a decision (by rw [ha]; exact fun _ x => by cases x)]
          exact ⟨h.funClauses, h.restR⟩

/-- `enterScript` keeps the seven clauses. -/
private theorem parts_enterScript {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : FunClauses (enterScript a) ∧ RestR (enterScript a) := by
  unfold Whatwg.Ecma262.Agent.enterScript
  cases a.active with
  | checkpoint => exact parts_active h _
  | script => exact ⟨h.funClauses, h.restR⟩
  | intrinsic _ => exact ⟨h.funClauses, h.restR⟩
  | job _ => exact ⟨h.funClauses, h.restR⟩

/-- `leaveScript` keeps the seven clauses. -/
private theorem parts_leaveScript {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) : FunClauses (leaveScript a) ∧ RestR (leaveScript a) := by
  unfold Whatwg.Ecma262.Agent.leaveScript
  cases a.active with
  | script => exact parts_active h _
  | checkpoint => exact ⟨h.funClauses, h.restR⟩
  | intrinsic _ => exact ⟨h.funClauses, h.restR⟩
  | job _ => exact ⟨h.funClauses, h.restR⟩

/-- Every operation keeps the seven clauses. -/
private theorem parts_step {value reason body : Type} {a : Agent value reason body}
    (h : Coherent a) (op : Op value reason body) :
    FunClauses (step a op).1 ∧ RestR (step a op).1 := by
  cases op with
  | newPromise => exact parts_newPromise h
  | resolve cap v =>
      exact parts_callFunctions h (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
        (Except.ok v)
  | reject cap r =>
      exact parts_callFunctions h (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject)
        (Except.error r)
  | perform p f r d => exact parts_perform h p f r d
  | markHandled p =>
      exact parts_table h (Promise.Table.markHandled a.table p)
        (fun q => markHandled_get a.table p q) (fun q => markHandled_isSome a.table p q)
  | startJob => exact parts_startJob h
  | finishJob d => exact parts_finishJob h d
  | enterScript => exact parts_enterScript h
  | leaveScript => exact parts_leaveScript h

/-! ## The invariant laws -/

/-- The agent before any promise satisfies the stronger invariant: every store
is empty. Invariant law; DB-04 M1. -/
theorem Coherent.empty :
    ∀ {value reason body : Type},
      Agent.Coherent (Agent.empty : Agent.Agent value reason body) := by
  intro value reason body
  exact {
    toWF := WF.empty
    functionPromisesNodup := List.nodup_nil
    unfiredPending := fun _ h => absurd h List.not_mem_nil
    settledTraced := ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
    waitingPending := fun _ h => absurd h List.not_mem_nil
    reactionsAllocated := fun _ h => absurd h List.not_mem_nil
    listKinds := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
    jobsTyped := fun _ h => by
      rcases h with h | h
      · exact absurd h List.not_mem_nil
      · cases h }

/-- Every operation keeps the stronger invariant, enabled or disabled, from
every agent it holds of: it is inductive, not a reachability statement.
Invariant law; DB-04 M1. -/
theorem Coherent.step :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (op : Agent.Op value reason body),
      Agent.Coherent a → Agent.Coherent (Agent.step a op).1 := by
  intro value reason body a op h
  exact Coherent.ofParts (WF.step a op h.toWF) (parts_step h op).1 (parts_step h op).2

/-- Every agent a run reaches from an agent the stronger invariant holds of
satisfies it. Invariant law; DB-04 M1. -/
theorem Coherent.runOps :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (ops : List (Agent.Op value reason body)),
      Agent.Coherent a → Agent.Coherent (Agent.runOps a ops).1 := by
  intro value reason body a ops
  induction ops generalizing a with
  | nil => exact id
  | cons op ops ih =>
      exact fun h => ih (Whatwg.Ecma262.Agent.step a op).1
        (Whatwg.Ecma262.Agent.Coherent.step a op h)

/-- The reachability corollary: every agent `runOps` reaches from `Agent.empty`
satisfies the stronger invariant. Invariant law; DB-04 M1. -/
theorem Coherent.reachable :
    ∀ {value reason body : Type} (ops : List (Agent.Op value reason body)),
      Agent.Coherent (Agent.runOps (Agent.empty : Agent.Agent value reason body) ops).1 := by
  intro value reason body ops
  exact Whatwg.Ecma262.Agent.Coherent.runOps Agent.empty ops Whatwg.Ecma262.Agent.Coherent.empty


/-! ## The stronger order -/

/-- Setting the marker of a fired record returns the record. -/
private theorem mark_fired_self (pick : Promise.ResolvingFunctions → Bool)
    (f : Promise.ResolvingFunctions) (hf : f.alreadyResolved = true) :
    (if pick f then { f with alreadyResolved := true } else f) = f := by
  cases hp : pick f with
  | false => rfl
  | true =>
      obtain ⟨p, r, j, m⟩ := f
      cases hf
      rfl

/-- `callFunctions` keeps every fired record and `held`. -/
private theorem callFunctions_keeps {value reason body : Type} (a : Agent value reason body)
    (pick : Promise.ResolvingFunctions → Bool) (result : Except reason value) :
    (∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ (callFunctions a pick result).functions) ∧
      (callFunctions a pick result).held = a.held := by
  cases hf : a.functions.find? pick with
  | none => rw [callFunctions_none a pick result hf]; exact ⟨fun f hf _ => hf, rfl⟩
  | some g =>
      cases hgr : g.alreadyResolved with
      | true =>
          rw [callFunctions_fired a pick result g hf hgr]; exact ⟨fun f hf _ => hf, rfl⟩
      | false =>
          rw [callFunctions_fresh a pick result g hf hgr]
          refine ⟨fun f hfm hfr => ?_, rfl⟩
          show f ∈ a.functions.map _
          exact List.mem_map.mpr ⟨f, hfm, mark_fired_self pick f hfr⟩

/-- Every operation keeps every fired record and grows `held` at its end. -/
private theorem step_keeps {value reason body : Type} (a : Agent value reason body)
    (op : Op value reason body) :
    (∀ f ∈ a.functions, f.alreadyResolved = true → f ∈ (step a op).1.functions) ∧
      a.held <+: (step a op).1.held := by
  cases op with
  | newPromise =>
      exact ⟨fun f hf _ => List.mem_append_left _ hf, List.prefix_refl _⟩
  | resolve cap v =>
      obtain ⟨h1, h2⟩ := callFunctions_keeps a
        (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) (Except.ok v)
      exact ⟨h1, h2 ▸ List.prefix_refl _⟩
  | reject cap r =>
      obtain ⟨h1, h2⟩ := callFunctions_keeps a
        (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) (Except.error r)
      exact ⟨h1, h2 ▸ List.prefix_refl _⟩
  | perform p f r d =>
      have hmint : ∀ g ∈ a.functions, g ∈ (Whatwg.Ecma262.Agent.mintFor a d).1.functions := by
        intro g hg
        cases d with
        | false => exact hg
        | true => exact List.mem_append_left _ hg
      have hheld : (Whatwg.Ecma262.Agent.mintFor a d).1.held = a.held := by cases d <;> rfl
      show (∀ g ∈ a.functions, g.alreadyResolved = true →
          g ∈ (Whatwg.Ecma262.Agent.perform a p f r d).1.functions) ∧
        a.held <+: (Whatwg.Ecma262.Agent.perform a p f r d).1.held
      cases hg : a.table.get p with
      | none =>
          rw [perform_missing a p f r d hg]
          exact ⟨fun g hg _ => hg, List.prefix_refl _⟩
      | some s =>
          cases s with
          | pending =>
              rw [perform_pending a p f r d hg]
              exact ⟨fun g hg _ => hmint g hg, hheld ▸ List.prefix_refl _⟩
          | fulfilled v =>
              rw [perform_fulfilled a p v f r d hg]
              exact ⟨fun g hg _ => hmint g hg, List.prefix_append _ _⟩
          | rejected x =>
              rw [perform_rejected a p x f r d hg]
              exact ⟨fun g hg _ => hmint g hg, List.prefix_append _ _⟩
  | markHandled p => exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
  | startJob =>
      show (∀ f ∈ a.functions, f.alreadyResolved = true →
          f ∈ (Whatwg.Ecma262.Agent.startJob a).1.functions) ∧
        a.held <+: (Whatwg.Ecma262.Agent.startJob a).1.held
      unfold Whatwg.Ecma262.Agent.startJob
      split <;> exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
  | finishJob d =>
      show (∀ f ∈ a.functions, f.alreadyResolved = true →
          f ∈ (Whatwg.Ecma262.Agent.finishJob a d).functions) ∧
        a.held <+: (Whatwg.Ecma262.Agent.finishJob a d).held
      cases hrun : a.running with
      | none =>
          rw [finishJob_idle a d hrun]; exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
      | some job =>
          cases ha : a.active with
          | job s =>
              cases hr : reactionOf a job with
              | none =>
                  rw [finishJob_unknown a d s job ha hrun hr]
                  exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
              | some r =>
                  cases hc : r.capability with
                  | none =>
                      rw [finishJob_no_capability a d s job r ha hrun hr hc]
                      exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
                  | some cap =>
                      rw [finishJob_capability a d s job r cap ha hrun hr hc]
                      obtain ⟨h1, h2⟩ := callFunctions_keeps a
                        (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve)
                        (Promise.reactionHandlerResult r job.argument d)
                      exact ⟨h1, h2 ▸ List.prefix_refl _⟩
          | checkpoint =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ x => by cases x)]
              exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
          | script =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ x => by cases x)]
              exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
          | intrinsic _ =>
              rw [finishJob_not_job a d (by rw [ha]; exact fun _ x => by cases x)]
              exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
  | enterScript =>
      show (∀ f ∈ a.functions, f.alreadyResolved = true →
          f ∈ (Whatwg.Ecma262.Agent.enterScript a).functions) ∧
        a.held <+: (Whatwg.Ecma262.Agent.enterScript a).held
      unfold Whatwg.Ecma262.Agent.enterScript
      split <;> exact ⟨fun f hf _ => hf, List.prefix_refl _⟩
  | leaveScript =>
      show (∀ f ∈ a.functions, f.alreadyResolved = true →
          f ∈ (Whatwg.Ecma262.Agent.leaveScript a).functions) ∧
        a.held <+: (Whatwg.Ecma262.Agent.leaveScript a).held
      unfold Whatwg.Ecma262.Agent.leaveScript
      split <;> exact ⟨fun f hf _ => hf, List.prefix_refl _⟩

/-- Every agent extends itself. Adequacy law; DB-04 M2, through `Le.trace` and
`heldGrows`. -/
theorem Extends.refl :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body), Agent.Extends a a := by
  intro value reason body a
  exact ⟨Le.refl a, fun _ hf _ => hf, List.prefix_refl _⟩

/-- Extension is transitive. Adequacy law; DB-04 M2. -/
theorem Extends.trans :
    ∀ {value reason body : Type} {a b c : Agent.Agent value reason body},
      Agent.Extends a b → Agent.Extends b c → Agent.Extends a c := by
  intro value reason body a b c h₁ h₂
  exact ⟨Le.trans h₁.toLe h₂.toLe,
    fun f hf hfr => h₂.markerKept f (h₁.markerKept f hf hfr) hfr,
    List.IsPrefix.trans h₁.heldGrows h₂.heldGrows⟩

/-- Every operation moves a well-formed agent up the stronger order, enabled or
not: a fired record survives and `held` grows at its end (gap J). Adequacy law;
DB-04 M2. -/
theorem Extends.step :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (op : Agent.Op value reason body),
      Agent.WF a → Agent.Extends a (Agent.step a op).1 := by
  intro value reason body a op hw
  exact ⟨Le.step a op hw, (step_keeps a op).1, (step_keeps a op).2⟩

/-! ## The two-state post -/

/-- After `newPromise`, the Q5 post holds and no reaction names the new promise,
whose reaction lists are new and empty (`builtin.promise-executor`; gap E).
Defining equation; DB-04 M1. -/
theorem postFrom_newPromise :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.newPromise : Agent.Op value reason body))
      (cap : Promise.Capability),
      Agent.postFrom a a' Agent.Op.newPromise c cap ↔
        Agent.post a' Agent.Op.newPromise c cap ∧
          ∀ r ∈ a'.reactions.fulfill ++ a'.reactions.reject ++ a'.held,
            r.promise ≠ cap.promise := by
  intros; exact Iff.rfl

/-- After `resolve`, the Q5 post holds, and through an unfired stored function
the promise is fulfilled with the value (RESOLVING, FULFILL; gap A). Defining
equation; DB-04 M1. -/
theorem postFrom_resolve :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (cap : Promise.Capability) (v : value)
      (c : Agent.Cert (Agent.Op.resolve cap v : Agent.Op value reason body)) (ans : Unit),
      Agent.postFrom a a' (Agent.Op.resolve cap v) c ans ↔
        Agent.post a' (Agent.Op.resolve cap v) c ans ∧
          ∀ f ∈ a.functions, f.resolve = cap.resolve → f.alreadyResolved = false →
            Promise.Table.get a'.table cap.promise = some (Promise.State.fulfilled v) := by
  intros; exact Iff.rfl

/-- After `reject`, the Q5 post holds, and through an unfired stored function
the promise is rejected with the reason (RESOLVING, REJECT; gap A). Defining
equation; DB-04 M1. -/
theorem postFrom_reject :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (cap : Promise.Capability) (r : reason)
      (c : Agent.Cert (Agent.Op.reject cap r : Agent.Op value reason body)) (ans : Unit),
      Agent.postFrom a a' (Agent.Op.reject cap r) c ans ↔
        Agent.post a' (Agent.Op.reject cap r) c ans ∧
          ∀ f ∈ a.functions, f.reject = cap.reject → f.alreadyResolved = false →
            Promise.Table.get a'.table cap.promise = some (Promise.State.rejected r) := by
  intros; exact Iff.rfl

/-- The post of `perform` is the Q5 post (THEN). Defining equation; DB-04 M1. -/
theorem postFrom_perform :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
      (onFulfilled onRejected : Option body) (derive : Bool)
      (c : Agent.Cert (Agent.Op.perform promise onFulfilled onRejected derive :
        Agent.Op value reason body))
      (ans : Option (Option Promise.Capability)),
      Agent.postFrom a a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans ↔
        Agent.post a' (Agent.Op.perform promise onFulfilled onRejected derive) c ans := by
  intros; exact Iff.rfl

/-- The post of `markHandled` is the Q5 post (HANDLEDOP). Defining equation;
DB-04 M1. -/
theorem postFrom_markHandled :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body) (promise : Nat)
      (c : Agent.Cert (Agent.Op.markHandled promise : Agent.Op value reason body))
      (ans : Unit),
      Agent.postFrom a a' (Agent.Op.markHandled promise) c ans ↔
        Agent.post a' (Agent.Op.markHandled promise) c ans := by
  intros; exact Iff.rfl

/-- After `startJob`, the Q5 post holds, the answered job was the head of the
queue, and the queue is the rest (`requirement.jobs.1`,
`requirement.hostenqueuepromisejob.3`; gap I). Defining equation; DB-04 M2,
since it observes the queue's order. -/
theorem postFrom_startJob :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.startJob : Agent.Op value reason body))
      (ans : Option (Agent.Job value reason × Option body)),
      Agent.postFrom a a' Agent.Op.startJob c ans ↔
        Agent.post a' Agent.Op.startJob c ans ∧
          ∃ (j : Agent.Job value reason) (rest : List (Agent.Job value reason)),
            a.queue.pending = j :: rest ∧ a'.queue.pending = rest ∧
              ans.map Prod.fst = some j := by
  intros; exact Iff.rfl

/-- After `finishJob`, the Q5 post holds, the running job named its record, and
in each case the model has: with `[[Capability]]` *undefined* or a fired
function nothing settles, and with an unfired function the capability's promise
is settled with the handler's result (`op.newpromisereactionjob` inner steps 6
to 9; gap D). Defining equation; DB-04 M1. -/
theorem postFrom_finishJob :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (decision : Except reason value)
      (c : Agent.Cert (Agent.Op.finishJob decision : Agent.Op value reason body)) (ans : Unit),
      Agent.postFrom a a' (Agent.Op.finishJob decision) c ans ↔
        Agent.post a' (Agent.Op.finishJob decision) c ans ∧
          ∃ (j : Agent.Job value reason) (r : Promise.Reaction body),
            a.running = some j ∧ Agent.reactionOf a j = some r ∧
            (r.capability = none →
              a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
            ∀ cap : Promise.Capability, r.capability = some cap →
              ∀ f ∈ a.functions, f.resolve = cap.resolve →
                (f.alreadyResolved = true →
                  a' = { a with active := Jobs.Active.checkpoint, running := none }) ∧
                (f.alreadyResolved = false →
                  (∀ v : value,
                    Promise.reactionHandlerResult r j.argument decision = Except.ok v →
                      Promise.Table.get a'.table cap.promise =
                        some (Promise.State.fulfilled v)) ∧
                  (∀ e : reason,
                    Promise.reactionHandlerResult r j.argument decision = Except.error e →
                      Promise.Table.get a'.table cap.promise =
                        some (Promise.State.rejected e))) := by
  intros; exact Iff.rfl

/-- The post of `enterScript` is the Q5 post (RUNCOND). Defining equation; DB-04
M1. -/
theorem postFrom_enterScript :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.enterScript : Agent.Op value reason body)) (ans : Unit),
      Agent.postFrom a a' Agent.Op.enterScript c ans ↔
        Agent.post a' Agent.Op.enterScript c ans := by
  intros; exact Iff.rfl

/-- The post of `leaveScript` is the Q5 post (RUNCOND). Defining equation; DB-04
M1. -/
theorem postFrom_leaveScript :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (c : Agent.Cert (Agent.Op.leaveScript : Agent.Op value reason body)) (ans : Unit),
      Agent.postFrom a a' Agent.Op.leaveScript c ans ↔
        Agent.post a' Agent.Op.leaveScript c ans := by
  intros; exact Iff.rfl

/-- The stronger post implies the Q5 post, for every operation. Adequacy law;
DB-04 M1. -/
theorem postFrom_post :
    ∀ {value reason body : Type} (a a' : Agent.Agent value reason body)
      (op : Agent.Op value reason body) (c : Agent.Cert op) (ans : Agent.Op.Answer op),
      Agent.postFrom a a' op c ans → Agent.post a' op c ans := by
  intro value reason body a a' op c ans h
  cases op with
  | newPromise => exact ((postFrom_newPromise a a' c ans).mp h).1
  | resolve cap v => exact ((postFrom_resolve a a' cap v c ans).mp h).1
  | reject cap r => exact ((postFrom_reject a a' cap r c ans).mp h).1
  | perform p f r d => exact (postFrom_perform a a' p f r d c ans).mp h
  | markHandled p => exact (postFrom_markHandled a a' p c ans).mp h
  | startJob => exact ((postFrom_startJob a a' c ans).mp h).1
  | finishJob d => exact ((postFrom_finishJob a a' d c ans).mp h).1
  | enterScript => exact (postFrom_enterScript a a' c ans).mp h
  | leaveScript => exact (postFrom_leaveScript a a' c ans).mp h

/-! ## The second judgment -/

/-- The second judgment, spelled out. Defining equation; DB-04 M2, through
`Extends`. -/
theorem ImplementsFrom_iff :
    ∀ {value reason body : Type} (op : Agent.Op value reason body),
      Agent.ImplementsFrom op ↔
        ∀ (a : Agent.Agent value reason body) (c : Agent.Cert op), Agent.Coherent a →
          Agent.pre a op c →
          Agent.Extends a (Agent.step a op).1 ∧ Agent.Coherent (Agent.step a op).1 ∧
            Agent.postFrom a (Agent.step a op).1 op c (Agent.step a op).2 := by
  intros; exact Iff.rfl

/-- `newPromise` fulfils its row of the second judgment:
`op.newpromisecapability` (NEWCAP, 2696238..2698770) with
`builtin.promise-executor` (2708413..2711495). Adequacy law; DB-04 M2. -/
theorem newPromise_implementsFrom :
    ∀ {value reason body : Type},
      Agent.ImplementsFrom (Agent.Op.newPromise : Agent.Op value reason body) := by
  intro value reason body a c h hpre
  refine ⟨Extends.step a _ h.toWF, Coherent.step a _ h, ?_⟩
  refine (postFrom_newPromise a _ c _).mpr
    ⟨(newPromise_implements a c h.toWF hpre).2.2, fun r hr => ?_⟩
  show r.promise ≠ a.table.next
  exact Nat.ne_of_lt (h.toWF.getCell_lt (h.reactionsAllocated r hr))

/-- Under `WF`, the record a stored function's `[[Resolve]]` identity names is
the one `find?` returns. -/
private theorem find_resolve {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (cap : Promise.Capability) (f : Promise.ResolvingFunctions)
    (hf : f ∈ a.functions) (h1 : f.resolve = cap.resolve) :
    a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve) = some f :=
  find?_unique a.functions _ (resolve_unique hw cap) f hf (beq_iff_eq.mpr h1)

/-- Under `WF`, the record a stored function's `[[Reject]]` identity names is
the one `find?` returns. -/
private theorem find_reject {value reason body : Type} {a : Agent value reason body}
    (hw : WF a) (cap : Promise.Capability) (f : Promise.ResolvingFunctions)
    (hf : f ∈ a.functions) (h2 : f.reject = cap.reject) :
    a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) = some f :=
  find?_unique a.functions _ (reject_unique hw cap) f hf (beq_iff_eq.mpr h2)

/-- An unfired function settles its own pending promise with the result. -/
private theorem callFunctions_unfired_get {value reason body : Type}
    {a : Agent value reason body} (h : Coherent a) (pick : Promise.ResolvingFunctions → Bool)
    (result : Except reason value) (f : Promise.ResolvingFunctions) (hf : f ∈ a.functions)
    (hfind : a.functions.find? pick = some f) (hfr : f.alreadyResolved = false) :
    (∀ v, result = Except.ok v →
        Promise.Table.get (callFunctions a pick result).table f.promise =
          some (Promise.State.fulfilled v)) ∧
      (∀ e, result = Except.error e →
        Promise.Table.get (callFunctions a pick result).table f.promise =
          some (Promise.State.rejected e)) := by
  rw [callFunctions_fresh a pick result f hfind hfr]
  show (∀ v, result = Except.ok v →
      Promise.Table.get (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise
        result).1 f.promise = some (Promise.State.fulfilled v)) ∧
    (∀ e, result = Except.error e →
      Promise.Table.get (Promise.Table.settleAndTrigger a.table a.reactions a.queue f.promise
        result).1 f.promise = some (Promise.State.rejected e))
  rw [settleAndTrigger_table]
  exact get_settle_self a.table f.promise result
    ((Promise.Table.isPending_iff a.table f.promise).mp (h.unfiredPending f hf hfr))

/-- `resolve` fulfils its row of the second judgment:
`op.createresolvingfunctions` (RESOLVING, 2692679..2695411) with
`op.fulfillpromise` (FULFILL). Adequacy law; DB-04 M2. -/
theorem resolve_implementsFrom :
    ∀ {value reason body : Type} (cap : Promise.Capability) (v : value),
      Agent.ImplementsFrom (Agent.Op.resolve cap v : Agent.Op value reason body) := by
  intro value reason body cap v a c h hpre
  refine ⟨Extends.step a _ h.toWF, Coherent.step a _ h, ?_⟩
  refine (postFrom_resolve a _ cap v c _).mpr
    ⟨(resolve_implements cap v a c h.toWF hpre).2.2, fun f hf h1 hfr => ?_⟩
  obtain ⟨g, hg, g1, _, g3⟩ := hpre
  have hfg : f = g := resolve_unique h.toWF cap f hf g hg (beq_iff_eq.mpr h1) (beq_iff_eq.mpr g1)
  subst hfg
  rw [← g3]
  exact (callFunctions_unfired_get h _ (Except.ok v) f hf (find_resolve h.toWF cap f hf h1)
    hfr).1 v rfl

/-- `reject` fulfils its row of the second judgment: RESOLVING with
`op.rejectpromise` (REJECT, 2699323..2700252). Adequacy law; DB-04 M2. -/
theorem reject_implementsFrom :
    ∀ {value reason body : Type} (cap : Promise.Capability) (r : reason),
      Agent.ImplementsFrom (Agent.Op.reject cap r : Agent.Op value reason body) := by
  intro value reason body cap r a c h hpre
  refine ⟨Extends.step a _ h.toWF, Coherent.step a _ h, ?_⟩
  refine (postFrom_reject a _ cap r c _).mpr
    ⟨(reject_implements cap r a c h.toWF hpre).2.2, fun f hf h2 hfr => ?_⟩
  obtain ⟨g, hg, _, g2, g3⟩ := hpre
  have hfg : f = g := reject_unique h.toWF cap f hf g hg (beq_iff_eq.mpr h2) (beq_iff_eq.mpr g2)
  subst hfg
  rw [← g3]
  exact (callFunctions_unfired_get h _ (Except.error r) f hf (find_reject h.toWF cap f hf h2)
    hfr).2 r rfl

/-- `perform` fulfils its row of the second judgment: `op.performpromisethen`
(THEN, 2740635..2743669). Adequacy law; DB-04 M2. -/
theorem perform_implementsFrom :
    ∀ {value reason body : Type} (promise : Nat) (onFulfilled onRejected : Option body)
      (derive : Bool),
      Agent.ImplementsFrom (Agent.Op.perform promise onFulfilled onRejected derive :
        Agent.Op value reason body) := by
  intro value reason body promise onFulfilled onRejected derive a c h hpre
  exact ⟨Extends.step a _ h.toWF, Coherent.step a _ h,
    (postFrom_perform a _ promise onFulfilled onRejected derive c _).mpr
      (perform_implements promise onFulfilled onRejected derive a c h.toWF hpre).2.2⟩

/-- `markHandled` fulfils its row of the second judgment: Web IDL
`op.mark-a-promise-as-handled` (HANDLEDOP). Adequacy law; DB-04 M2. -/
theorem markHandled_implementsFrom :
    ∀ {value reason body : Type} (promise : Nat),
      Agent.ImplementsFrom (Agent.Op.markHandled promise : Agent.Op value reason body) := by
  intro value reason body promise a c h hpre
  exact ⟨Extends.step a _ h.toWF, Coherent.step a _ h,
    (postFrom_markHandled a _ promise c _).mpr
      (markHandled_implements promise a c h.toWF hpre).2.2⟩

/-- `startJob` fulfils its row of the second judgment: `requirement.jobs.1`
(RUNCOND), `requirement.jobs.2` (ONEJOB), `requirement.hostenqueuepromisejob.3`
(ORDER, 634739..634841). Adequacy law; DB-04 M2. -/
theorem startJob_implementsFrom :
    ∀ {value reason body : Type},
      Agent.ImplementsFrom (Agent.Op.startJob : Agent.Op value reason body) := by
  intro value reason body a c h hpre
  refine ⟨Extends.step a _ h.toWF, Coherent.step a _ h, ?_⟩
  refine (postFrom_startJob a _ c _).mpr ⟨(startJob_implements a c h.toWF hpre).2.2, ?_⟩
  obtain ⟨ha, hne⟩ := hpre
  cases hq : a.queue.pending with
  | nil => exact absurd hq hne
  | cons job rest =>
      refine ⟨job, rest, rfl, ?_, ?_⟩
      · show (Whatwg.Ecma262.Agent.startJob a).1.queue.pending = rest
        rw [startJob_checkpoint a job rest ha hq]
      · show (Whatwg.Ecma262.Agent.startJob a).2.map Prod.fst = some job
        rw [startJob_checkpoint a job rest ha hq]
        rfl

/-- `finishJob` fulfils its row of the second judgment:
`op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner steps 4 to 9 and
`requirement.jobs.3` (COMPLETE). Adequacy law; DB-04 M2. -/
theorem finishJob_implementsFrom :
    ∀ {value reason body : Type} (decision : Except reason value),
      Agent.ImplementsFrom (Agent.Op.finishJob decision : Agent.Op value reason body) := by
  intro value reason body decision a c h hpre
  refine ⟨Extends.step a _ h.toWF, Coherent.step a _ h, ?_⟩
  refine (postFrom_finishJob a _ decision c _).mpr
    ⟨(finishJob_implements decision a c h.toWF hpre).2.2, ?_⟩
  obtain ⟨s, ha⟩ := hpre
  cases hrun : a.running with
  | none =>
      have := h.toWF.runningActive.2 s ha
      rw [hrun] at this
      cases this
  | some job =>
      obtain ⟨r, hr, _, _⟩ := h.jobsTyped job (Or.inr hrun)
      refine ⟨job, r, rfl, hr, fun hc => ?_, fun cap hc f hf h1 => ⟨fun hfr => ?_, fun hfr => ?_⟩⟩
      · exact finishJob_no_capability a decision s job r ha hrun hr hc
      · show Whatwg.Ecma262.Agent.finishJob a decision = _
        rw [finishJob_capability a decision s job r cap ha hrun hr hc,
          callFunctions_fired a _ _ f (find_resolve h.toWF cap f hf h1) hfr]
      · have hmint : Agent.Minted a cap :=
          h.toWF.capabilityStored r (reactionOf_mem a job r hr).2 cap hc
        obtain ⟨g, hg, g1, _, g3⟩ := hmint
        have hfg : f = g :=
          resolve_unique h.toWF cap f hf g hg (beq_iff_eq.mpr h1) (beq_iff_eq.mpr g1)
        subst hfg
        have hget := callFunctions_unfired_get h _
          (Promise.reactionHandlerResult r job.argument decision) f hf
          (find_resolve h.toWF cap f hf h1) hfr
        show (∀ v, _ → Promise.Table.get (Whatwg.Ecma262.Agent.finishJob a decision).table
            cap.promise = _) ∧
          (∀ e, _ → Promise.Table.get (Whatwg.Ecma262.Agent.finishJob a decision).table
            cap.promise = _)
        rw [finishJob_capability a decision s job r cap ha hrun hr hc, ← g3]
        exact hget

/-- `enterScript` fulfils its row of the second judgment: `requirement.jobs.1`
(RUNCOND). Adequacy law; DB-04 M2. -/
theorem enterScript_implementsFrom :
    ∀ {value reason body : Type},
      Agent.ImplementsFrom (Agent.Op.enterScript : Agent.Op value reason body) := by
  intro value reason body a c h hpre
  exact ⟨Extends.step a _ h.toWF, Coherent.step a _ h,
    (postFrom_enterScript a _ c _).mpr (enterScript_implements a c h.toWF hpre).2.2⟩

/-- `leaveScript` fulfils its row of the second judgment: `requirement.jobs.1`
(RUNCOND). Adequacy law; DB-04 M2. -/
theorem leaveScript_implementsFrom :
    ∀ {value reason body : Type},
      Agent.ImplementsFrom (Agent.Op.leaveScript : Agent.Op value reason body) := by
  intro value reason body a c h hpre
  exact ⟨Extends.step a _ h.toWF, Coherent.step a _ h,
    (postFrom_leaveScript a _ c _).mpr (leaveScript_implements a c h.toWF hpre).2.2⟩

/-- The handler fulfils every row of the second judgment. Adequacy law; DB-04
M2. -/
theorem implementsFrom :
    ∀ {value reason body : Type} (op : Agent.Op value reason body), Agent.ImplementsFrom op := by
  intro value reason body op
  cases op with
  | newPromise => exact newPromise_implementsFrom
  | resolve cap v => exact resolve_implementsFrom cap v
  | reject cap r => exact reject_implementsFrom cap r
  | perform p f r d => exact perform_implementsFrom p f r d
  | markHandled p => exact markHandled_implementsFrom p
  | startJob => exact startJob_implementsFrom
  | finishJob d => exact finishJob_implementsFrom d
  | enterScript => exact enterScript_implementsFrom
  | leaveScript => exact leaveScript_implementsFrom

/-! ## The reaction job's two completions -/

/-- Two picks that agree on every member find and mark alike. -/
private theorem find?_congr_mem {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
      rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
        find?_congr_mem p q l (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- For a capability this agent minted, under `WF`, the record its `[[Resolve]]`
identity finds is the one its `[[Reject]]` identity finds, so calling either
settles and marks alike: one record holds both functions and their shared marker
(`op.createresolvingfunctions`, `record.promisecapability-records`; gap G). Law;
DB-04 M2. -/
theorem callFunctions_resolve_reject :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (cap : Promise.Capability) (result : Except reason value),
      Agent.WF a → Agent.Minted a cap →
        Agent.callFunctions a
            (fun (f : Promise.ResolvingFunctions) => f.resolve == cap.resolve) result =
          Agent.callFunctions a
            (fun (f : Promise.ResolvingFunctions) => f.reject == cap.reject) result := by
  intro value reason body a cap result hw hm
  obtain ⟨f0, hf0, e1, e2, _⟩ := hm
  have hcap : cap.reject = cap.resolve + 1 := by
    rw [← e1, ← e2]; exact (hw.functionsBelow f0 hf0).1
  have hagree : ∀ g ∈ a.functions, (g.resolve == cap.resolve) = (g.reject == cap.reject) := by
    intro g hg
    have hg1 := (hw.functionsBelow g hg).1
    cases h1 : (g.resolve == cap.resolve) <;> cases h2 : (g.reject == cap.reject)
    · rfl
    · have e : g.reject = cap.reject := beq_iff_eq.mp h2
      rw [hg1, hcap] at e
      rw [beq_iff_eq.mpr (Nat.succ.inj e)] at h1
      cases h1
    · have e : g.resolve = cap.resolve := beq_iff_eq.mp h1
      have e' : g.reject = cap.reject := by rw [hg1, hcap, e]
      rw [beq_iff_eq.mpr e'] at h2
      cases h2
    · rfl
  have hfind := find?_congr_mem (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve)
    (fun (g : Promise.ResolvingFunctions) => g.reject == cap.reject) a.functions hagree
  have hmap : a.functions.map (fun (g : Promise.ResolvingFunctions) =>
        if g.resolve == cap.resolve then { g with alreadyResolved := true } else g) =
      a.functions.map (fun (g : Promise.ResolvingFunctions) =>
        if g.reject == cap.reject then { g with alreadyResolved := true } else g) := by
    apply List.map_congr_left
    intro g hg
    show (if (g.resolve == cap.resolve) = true then _ else g) =
      (if (g.reject == cap.reject) = true then _ else g)
    rw [hagree g hg]
  cases hf : a.functions.find? (fun (g : Promise.ResolvingFunctions) => g.resolve == cap.resolve)
    with
  | none =>
      rw [callFunctions_none a _ result hf, callFunctions_none a _ result (hfind ▸ hf)]
  | some f =>
      cases hfr : f.alreadyResolved with
      | true =>
          rw [callFunctions_fired a _ result f hf hfr,
            callFunctions_fired a _ result f (hfind ▸ hf) hfr]
      | false =>
          rw [callFunctions_fresh a _ result f hf hfr,
            callFunctions_fresh a _ result f (hfind ▸ hf) hfr, hmap]

/-- `op.newpromisereactionjob` (REACTJOB, 2702885..2705591) inner step 8: under
`WF`, an abrupt result of a job with a `[[Capability]]` is `Agent.reject`
through it, then the agent returns to a checkpoint (gap G). Law; DB-04 M2. -/
theorem finishJob_abrupt :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
      (r : Promise.Reaction body) (cap : Promise.Capability) (e : reason),
      Agent.WF a → a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = some cap →
        Promise.reactionHandlerResult r job.argument decision = Except.error e →
        Agent.finishJob a decision =
          { Agent.reject a cap e with active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job r cap e hw ha hrun hr hc hres
  rw [finishJob_capability a decision s job r cap ha hrun hr hc, hres,
    callFunctions_resolve_reject a cap (Except.error e) hw
      (hw.capabilityStored r (reactionOf_mem a job r hr).2 cap hc)]
  rfl

/-- REACTJOB inner step 9: a normal result of a job with a `[[Capability]]` is
`Agent.resolve` through it, then the agent returns to a checkpoint. Law; DB-04
M2. -/
theorem finishJob_normal :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
      (r : Promise.Reaction body) (cap : Promise.Capability) (v : value),
      a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = some cap →
        Promise.reactionHandlerResult r job.argument decision = Except.ok v →
        Agent.finishJob a decision =
          { Agent.resolve a cap v with active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job r cap v ha hrun hr hc hres
  rw [finishJob_capability a decision s job r cap ha hrun hr hc, hres]
  rfl

/-- REACTJOB inner step 6: with `[[Capability]]` *undefined*, the specification
asserts the result is not abrupt; the model takes the host's decision unchecked
(DB-02), and an abrupt result there settles nothing, records nothing and queues
nothing. A named departure (gap H). Law; DB-04 M1. -/
theorem finishJob_abrupt_dropped :
    ∀ {value reason body : Type} (a : Agent.Agent value reason body)
      (decision : Except reason value) (s : Nat) (job : Agent.Job value reason)
      (r : Promise.Reaction body) (e : reason),
      a.active = Jobs.Active.job s → a.running = some job →
        Agent.reactionOf a job = some r → r.capability = none →
        Promise.reactionHandlerResult r job.argument decision = Except.error e →
        Agent.finishJob a decision =
          { a with active := Jobs.Active.checkpoint, running := none } := by
  intro value reason body a decision s job r e ha hrun hr hc _
  exact finishJob_no_capability a decision s job r ha hrun hr hc

end Whatwg.Ecma262.Agent
