import Whatwg.Streams.Semantics.Step

/-!
# Semantics.Invariants.lean

Owner: `CONFIGURATION-PG-ORDERING`, construction edge. `RegistrationsFresh`
says the registration identities of a configuration are duplicate-free and
below the observer cursor `nextObserver`. Duplicate-freedom alone is not
inductive; with the cursor bound it is, so `step_registrationsFresh` carries
no reachability hypothesis, and the closure theorem
`reaches_registrationsFresh` is `Kernel.Path.invariant` through
`reaches_iff_path`.

`reachable_registrations_nodup` discharges, at every configuration reachable
from `initial`, the `Nodup` premise that `notifySettled_reactions_bridge` and
`notifySettled_queued_serial` carry (amendment A4 of the Q4 contract).
Counterexample `WS-KERNEL-CE-006` is the `register` that reuses an identity.

The predicate is the first clause of the held P8a draft's `SerialsWellFormed`.
`CellsWellFormed` is not here; it stays a P8 obligation (CFG-CELLS).

Spec anchors: none; like `Semantics/Step.lean`, this module states a property
of the configuration, not an algorithm of the specification.

Opened by slice W8a.3 (ruling R-W4). Packet:
`test/contracts/transition-kernel.contract.md`, section 5.3, and the W8a
amendment of `test/contracts/configuration-ordering.contract.md`.
-/

namespace Whatwg.Streams.Semantics.Ordering

open Whatwg.Streams

variable {α ε : Type}

/-- The registration identities, in registration order. Class [A]. -/
def registrationIds (c : Config α ε) : List Nat := c.registrations.map (fun r => r.id)

/-- Registration identities are duplicate-free and below the observer cursor.
Class [A]. -/
def RegistrationsFresh (c : Config α ε) : Prop :=
  (registrationIds c).Nodup ∧ ∀ i ∈ registrationIds c, i < c.nextObserver

/-- Two configurations with the same registration identities and cursor. -/
private def SameRegs (c t : Config α ε) : Prop :=
  registrationIds t = registrationIds c ∧ t.nextObserver = c.nextObserver

private theorem sameRegs_trans {a b c : Config α ε} :
    SameRegs a b → SameRegs b c → SameRegs a c :=
  fun h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem fresh_of_same {c t : Config α ε} :
    SameRegs c t → RegistrationsFresh c → RegistrationsFresh t := by
  intro ⟨hids, hnext⟩ ⟨hnd, hlt⟩
  refine ⟨hids ▸ hnd, ?_⟩
  intro i hi
  rw [hnext]
  exact hlt i (hids ▸ hi)

/-! ## Operations that keep the identities and the cursor -/

private theorem setRegistrationPhase_same (c : Config α ε) (id : Nat)
    (phase : Whatwg.Ecma262.Promise.ReactionPhase) :
    SameRegs c (setRegistrationPhase c id phase) := by
  refine ⟨?_, rfl⟩
  simp only [registrationIds, setRegistrationPhase, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply]
  split <;> rfl

private theorem enqueueJob_same (c : Config α ε) (kind : JobKind) :
    SameRegs c (enqueueJob c kind).1 := ⟨rfl, rfl⟩

/-- One step of the fold `notifySettled` runs over the registrations. -/
private theorem notifySettled_fold_same (c : Config α ε) (id : Nat) :
    ∀ (l : List (Whatwg.Ecma262.Promise.Reaction Nat)) (acc : Config α ε),
      SameRegs c acc →
        SameRegs c (l.foldl
          (fun (acc : Config α ε) (r : Whatwg.Ecma262.Promise.Reaction Nat) =>
            match r.phase with
            | .waiting =>
                if r.promise == id then
                  let queued := enqueueJob acc (.observer r.id)
                  setRegistrationPhase queued.1 r.id (.queued queued.2.serial)
                else acc
            | _ => acc) acc)
  | [], _, h => h
  | r :: rest, acc, h => by
      apply notifySettled_fold_same c id rest
      simp only
      split
      · split
        · exact sameRegs_trans h
            (sameRegs_trans (enqueueJob_same _ _) (setRegistrationPhase_same _ _ _))
        · exact h
      · exact h

private theorem notifySettled_same (c : Config α ε) (id : Nat) :
    SameRegs c (notifySettled c id) := by
  fun_cases notifySettled c id
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact notifySettled_fold_same c id _ c ⟨rfl, rfl⟩

private theorem liftWritable_same (c : Config α ε) (w : Writable.State α ε) :
    SameRegs c (liftWritable c w) := by
  unfold liftWritable
  have logged : ∀ (l : List (Writable.Event α ε)) (acc : Config α ε), SameRegs c acc →
      SameRegs c (l.foldl
        (fun (acc : Config α ε) (event : Writable.Event α ε) =>
          let logged : Config α ε := { acc with trace := acc.trace ++ [.writable event] }
          match event with
          | .settled id _ => notifySettled logged id
          | _ => logged) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons e rest ih =>
        intro acc h
        apply ih
        simp only
        split
        · exact sameRegs_trans h (notifySettled_same _ _)
        · exact h
  have scheduled : ∀ (l : List (Writable.SinkJob α ε)) (acc : Config α ε), SameRegs c acc →
      SameRegs c (l.foldl
        (fun (acc : Config α ε) (job : Writable.SinkJob α ε) =>
          (enqueueJob acc (.sink job.kind job.request)).1) acc) := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons j rest ih => intro acc h; exact ih _ h
  exact scheduled _ _ (logged _ _ ⟨rfl, rfl⟩)

private theorem lift_fresh {c t : Config α ε} {w : Option (Writable.State α ε)} :
    RegistrationsFresh c → w.map (liftWritable c) = some t → RegistrationsFresh t := by
  intro hc h
  cases w with
  | none => cases h
  | some w => cases h; exact fresh_of_same (liftWritable_same c w) hc

private theorem takeSinkHead_fresh {c t : Config α ε} {token : Job} :
    RegistrationsFresh c → takeSinkHead c token = some t → RegistrationsFresh t := by
  intro hc
  fun_cases takeSinkHead c token
  all_goals intro h
  all_goals first
    | (cases h; done)
    | (cases h; exact fresh_of_same ⟨rfl, rfl⟩ hc)

/-! ## Registration: one fresh identity, the cursor past it -/

private theorem register_fresh {c t : Config α ε} {p : Whatwg.Ecma262.Promise.Ref}
    {callback : Nat} :
    RegistrationsFresh c → register c p callback = some t → RegistrationsFresh t := by
  intro ⟨hnd, hlt⟩
  have appended : RegistrationsFresh ({ c with
      registrations := c.registrations ++
        [⟨c.nextObserver, p.cell, .fulfill, some callback, none, .waiting⟩],
      nextObserver := c.nextObserver + 1,
      trace := c.trace ++ [.registered c.nextObserver p callback] } : Config α ε) := by
    simp only [RegistrationsFresh, registrationIds, List.map_append, List.map_cons,
      List.map_nil]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact Nat.ne_of_lt (hlt a ha)
    · intro i hi
      rw [List.mem_append, List.mem_singleton] at hi
      cases hi with
      | inl h => exact Nat.lt_succ_of_lt (hlt i h)
      | inr h => subst h; exact Nat.lt_succ_self _
  fun_cases register c p callback
  all_goals intro h
  all_goals first
    | (cases h; done)
    | (rw [← Option.some.inj h]; exact appended)
    | (rw [← Option.some.inj h]
       exact fresh_of_same
         (sameRegs_trans (enqueueJob_same _ _) (setRegistrationPhase_same _ _ _)) appended)

/-! ## The step, closure, initial and reachability theorems -/

/-- Class [A]. Every step keeps registration identities fresh. No reachability
hypothesis: the invariant is inductive. -/
theorem step_registrationsFresh {c t : Config α ε} {d : Option (Decision α ε)} :
    RegistrationsFresh c → Step c d t → RegistrationsFresh t := by
  intro hc
  cases d with
  | none =>
      show tick c = some t → _
      fun_cases tick c
      all_goals intro h
      all_goals first
        | (cases h; done)
        | exact takeSinkHead_fresh hc h
        | exact lift_fresh hc h
        | (cases h; exact fresh_of_same ⟨rfl, rfl⟩ hc)
        | (cases h; exact fresh_of_same (setRegistrationPhase_same _ _ _) hc)
  | some decision =>
      show decide c decision = some t → _
      fun_cases decide c decision
      all_goals intro h
      all_goals first
        | (cases h; done)
        | exact register_fresh hc h
        | exact lift_fresh hc h
        | (cases h; exact fresh_of_same ⟨rfl, rfl⟩ hc)
        | (cases h; exact fresh_of_same (setRegistrationPhase_same _ _ _) hc)

/-- Class [A]. The invariant is carried along every finite derivation:
`Kernel.Path.invariant` through `reaches_iff_path`. -/
theorem reaches_registrationsFresh {c t : Config α ε} {ds : List (Option (Decision α ε))} :
    Reaches c ds t → RegistrationsFresh c → RegistrationsFresh t :=
  fun h => Kernel.Path.invariant (fun _ _ _ hs hst => step_registrationsFresh hs hst)
    (reaches_iff_path.mp h)

/-- Class [A]. The frozen initial configuration has no registration. -/
theorem initial_registrationsFresh (owner : Nat) (hwm : Writable.Size)
    (alg : Writable.Algorithms) (promiseSeed errorSeed : Nat) :
    RegistrationsFresh (initial (α := α) (ε := ε) owner hwm alg promiseSeed errorSeed) :=
  ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- Class [A]. The `Nodup` premise of `notifySettled_reactions_bridge` and
`notifySettled_queued_serial` holds at every configuration reachable from
`initial`. -/
theorem reachable_registrations_nodup {c : Config α ε} {owner : Nat} {hwm : Writable.Size}
    {alg : Writable.Algorithms} {promiseSeed errorSeed : Nat}
    {ds : List (Option (Decision α ε))} :
    Reaches (initial owner hwm alg promiseSeed errorSeed) ds c →
      (c.registrations.map (fun r => r.id)).Nodup :=
  fun h => (reaches_registrationsFresh h (initial_registrationsFresh _ _ _ _ _)).1

end Whatwg.Streams.Semantics.Ordering
