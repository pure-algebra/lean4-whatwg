import Whatwg.Svg.Scene.Join

/-!
# Whatwg.Svg.Scene.Join.Laws

Owner: the laws of the join by key (slice S12 of `docs/SVG-PACKAGE-PLAN.md`; ruling SV-61).

The join of `Whatwg/Svg/Scene/Join.lean` sorts the things of an old list and a new one into
three selections. These laws say that it sorts every thing, and where each thing goes.

- Nothing is lost. A new thing enters or updates (`join_new`). An old thing exits, or a new
  thing has its key (`join_old`). The entering things and the updating pairs together count
  the new list, each new thing once (`length_enter_add_update`).
- Each selection is what its name says. A thing enters exactly when it is new and no old thing
  has its key (`mem_enter`). A thing exits exactly when it is old and no new thing has its key
  (`mem_exit`). An updating pair is an old thing and a new thing with one key (`mem_update`).
- With distinct keys in the old list, every such pair updates (`mem_update_iff`): the old thing
  with a key is the one that the join finds.
- The edges. From an empty list every thing enters, and to an empty list every thing exits
  (`join_nil_left`, `join_nil_right`). A list joined to itself has no thing that enters and no
  thing that exits (`enter_self`, `exit_self`).
- Distinct keys stay distinct among the entering things and among the exiting ones
  (`distinct_enter`, `distinct_exit`). With distinct keys, two things of a list with one key are
  one thing (`eq_of_distinct`).
- Lists. The section "Lists" holds the plain list lemmas of this layer, for the modules above
  it: a list with no member is empty (`eq_nil_of_no_mem`), two lists with no repeat and no
  common member make a list with no repeat (`nodup_append_of`), values with no repeat stay so
  when each is paired with one key (`nodup_pair`), and two `flatMap`s that agree under a
  function member by member agree under it (`map_flatMap_congr`). The last three came from
  `Whatwg/Svg/Scene/Resume.lean` and `Whatwg/Svg/Scene/Stage.lean` in slice S16.

The key is of any type with an equality test. A law that needs the test to be lawful says so,
and the others hold of any test. Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

/-! ## Lists -/

/-- A list with no member is the empty list. -/
theorem eq_nil_of_no_mem {α : Type} : ∀ {l : List α}, (∀ a, a ∉ l) → l = []
  | [], _ => rfl
  | a :: _, h => absurd (List.Mem.head _) (h a)

/-- A search finds nothing exactly where no member passes the test. -/
theorem not_any_iff_find_none {α : Type} (q : α → Bool) (l : List α) :
    (!(l.any q)) = true ↔ l.find? q = none := by
  rw [Bool.not_eq_true', List.any_eq_false, List.find?_eq_none]

/-- A filter and a `filterMap` that take complementary members share the list between them:
each member is counted by one of the two. -/
theorem length_filter_add_filterMap {α β : Type} (p : α → Bool) (f : α → Option β)
    (hn : ∀ a, f a = none → p a = true) (hs : ∀ a b, f a = some b → p a = false) (l : List α) :
    (l.filter p).length + (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases hf : f a with
    | none =>
      rw [List.filter_cons_of_pos (hn a hf), List.filterMap_cons_none hf, List.length_cons,
        List.length_cons, Nat.add_right_comm, ih]
    | some b =>
      have hp : ¬p a = true := fun h => Bool.false_ne_true ((hs a b hf).symm.trans h)
      rw [List.filter_cons_of_neg hp, List.filterMap_cons_some hf, List.length_cons,
        List.length_cons, ← Nat.add_assoc, ih]

/-- A `flatMap` whose every result has `k` members at most gives `k` members at most for each
member of the list. -/
theorem length_flatMap_le {α β : Type} (f : α → List β) (k : Nat) : ∀ l : List α,
    (∀ a ∈ l, (f a).length ≤ k) → (l.flatMap f).length ≤ k * l.length
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    have h1 := length_flatMap_le f k l fun x hx => h x (List.mem_cons_of_mem a hx)
    have h2 := h a List.mem_cons_self
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Two `flatMap`s whose results agree under a function, member by member, agree under it. -/
theorem map_flatMap_congr {α β γ : Type} (f : β → γ) (A B : α → List β)
    (h : ∀ a, (A a).map f = (B a).map f) : ∀ l : List α,
    (l.flatMap A).map f = (l.flatMap B).map f
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append, h a,
      map_flatMap_congr f A B h l]

/-- Two lists with no repeat and no common member make a list with no repeat. -/
theorem nodup_append_of {β : Type} : ∀ {l r : List β}, l.Nodup → r.Nodup →
    (∀ a ∈ l, a ∉ r) → (l ++ r).Nodup
  | [], _, _, hr, _ => hr
  | a :: l, r, hl, hr, h => by
    have hl' : a ∉ l ∧ l.Nodup := List.nodup_cons.mp hl
    refine List.nodup_cons.mpr ⟨fun hm => ?_,
      nodup_append_of hl'.2 hr fun b hb => h b (List.mem_cons_of_mem a hb)⟩
    rcases List.mem_append.mp hm with h1 | h1
    · exact hl'.1 h1
    · exact h a List.mem_cons_self h1

/-- Values with no repeat, each paired with one key, are pairs with no repeat. -/
theorem nodup_pair {β γ δ : Type} (k : γ) (f : β → δ) : ∀ l : List β,
    (l.map f).Nodup → (l.map fun c => (k, f c)).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have h' : f a ∉ l.map f ∧ (l.map f).Nodup := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_pair k f l h'.2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    exact h'.1 (List.mem_map.mpr ⟨b, hb, congrArg Prod.snd e⟩)

/-- The things of a list that pass a test keep distinct keys. -/
theorem distinct_filter {α κ : Type} (key : α → κ) {l : List α} (hd : Distinct key l)
    (p : α → Bool) : Distinct key (l.filter p) :=
  List.Nodup.sublist (List.Sublist.map key List.filter_sublist) hd

/-- No thing of a list has the key `k`: what the test of the join says. -/
theorem none_keyed_iff {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (l : List α) (k : κ) :
    (!(l.any fun a => key a == k)) = true ↔ ∀ a ∈ l, key a ≠ k := by
  rw [Bool.not_eq_true', List.any_eq_false]
  exact ⟨fun h a ha he => h a ha (beq_iff_eq.mpr he),
    fun h a ha he => h a ha (beq_iff_eq.mp he)⟩

/-- With distinct keys, the search for a key finds the one thing that has it. -/
theorem find_of_distinct {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) {l : List α}
    (hd : Distinct key l) {o : α} (ho : o ∈ l) {k : κ} (hk : key o = k) :
    l.find? (fun a => key a == k) = some o := by
  induction l with
  | nil => cases ho
  | cons a rest ih =>
    have hd' : key a ∉ rest.map key ∧ (rest.map key).Nodup := List.nodup_cons.mp hd
    cases hb : key a == k with
    | true =>
      rw [List.find?_cons_of_pos (p := fun a => key a == k) hb]
      rcases List.mem_cons.mp ho with he | hr
      · exact congrArg some he.symm
      · exact absurd (List.mem_map.mpr ⟨o, hr, hk.trans (beq_iff_eq.mp hb).symm⟩) hd'.1
    | false =>
      have hnb : ¬(key a == k) = true := fun h => Bool.false_ne_true (hb.symm.trans h)
      rw [List.find?_cons_of_neg (p := fun a => key a == k) hnb]
      rcases List.mem_cons.mp ho with he | hr
      · exact absurd (beq_iff_eq.mpr ((congrArg key he.symm).trans hk)) hnb
      · exact ih hd'.2 hr

/-! ## The three selections -/

/-- A thing enters exactly when it is new and no old thing has its key. -/
theorem mem_enter {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) {n : α} :
    n ∈ (join key old new).enter ↔ n ∈ new ∧ ∀ o ∈ old, key o ≠ key n :=
  List.mem_filter.trans (and_congr Iff.rfl (none_keyed_iff key old (key n)))

/-- A thing exits exactly when it is old and no new thing has its key. -/
theorem mem_exit {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) {o : α} :
    o ∈ (join key old new).exit ↔ o ∈ old ∧ ∀ n ∈ new, key n ≠ key o :=
  List.mem_filter.trans (and_congr Iff.rfl (none_keyed_iff key new (key o)))

/-- A pair updates exactly when its new thing is new and the search of the old list for its
key finds its old thing. -/
theorem mem_update_find {α κ : Type} [BEq κ] (key : α → κ) (old new : List α) {o n : α} :
    (o, n) ∈ (join key old new).update ↔
      n ∈ new ∧ old.find? (fun a => key a == key n) = some o := by
  constructor
  · intro h
    obtain ⟨m, hm, he⟩ := List.mem_filterMap.mp h
    have he' : (old.find? fun a => key a == key m).map (·, m) = some (o, n) := he
    cases hf : old.find? (fun a => key a == key m) with
    | none =>
      rw [hf] at he'
      cases he'
    | some a =>
      rw [hf] at he'
      have hp : (a, m) = (o, n) := Option.some.inj he'
      have ha : a = o := congrArg Prod.fst hp
      have hmn : m = n := congrArg Prod.snd hp
      subst hmn
      subst ha
      exact ⟨hm, hf⟩
  · intro ⟨hn, hf⟩
    exact List.mem_filterMap.mpr ⟨n, hn, congrArg (Option.map (·, n)) hf⟩

/-- An updating pair is an old thing and a new thing with one key. -/
theorem mem_update {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α)
    {o n : α} (h : (o, n) ∈ (join key old new).update) :
    o ∈ old ∧ n ∈ new ∧ key o = key n := by
  obtain ⟨hn, hf⟩ := (mem_update_find key old new).mp h
  have hk : (key o == key n) = true := List.find?_some (p := fun a => key a == key n) hf
  exact ⟨List.mem_of_find?_eq_some hf, hn, beq_iff_eq.mp hk⟩

/-- **With distinct keys in the old list, every pair with one key updates.** The old thing with
a key is then the one that the join finds. -/
theorem mem_update_iff {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α)
    (hd : Distinct key old) {o n : α} :
    (o, n) ∈ (join key old new).update ↔ o ∈ old ∧ n ∈ new ∧ key o = key n :=
  ⟨mem_update key old new, fun ⟨ho, hn, hk⟩ =>
    (mem_update_find key old new).mpr ⟨hn, find_of_distinct key hd ho hk⟩⟩

/-! ## Nothing is lost -/

/-- **Every new thing enters, or updates from an old thing.** -/
theorem join_new {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (n : α)
    (h : n ∈ new) :
    n ∈ (join key old new).enter ∨ ∃ o, (o, n) ∈ (join key old new).update := by
  cases hf : old.find? (fun o => key o == key n) with
  | none =>
    exact Or.inl ((mem_enter key old new).mpr ⟨h, fun o ho he =>
      List.find?_eq_none.mp hf o ho (beq_iff_eq.mpr he)⟩)
  | some o => exact Or.inr ⟨o, (mem_update_find key old new).mpr ⟨h, hf⟩⟩

/-- **Every old thing exits, or a new thing has its key.** -/
theorem join_old {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (old new : List α) (o : α)
    (h : o ∈ old) : o ∈ (join key old new).exit ∨ ∃ n ∈ new, key n = key o := by
  cases hany : new.any (fun n => key n == key o) with
  | false =>
    exact Or.inl ((mem_exit key old new).mpr ⟨h, fun n hn he =>
      List.any_eq_false.mp hany n hn (beq_iff_eq.mpr he)⟩)
  | true =>
    obtain ⟨n, hn, he⟩ := List.any_eq_true.mp hany
    exact Or.inr ⟨n, hn, beq_iff_eq.mp he⟩

/-- **Every new thing enters or updates, and not both**: the entering things and the updating
pairs together are as many as the new things. -/
theorem length_enter_add_update {α κ : Type} [BEq κ] (key : α → κ) (old new : List α) :
    (join key old new).enter.length + (join key old new).update.length = new.length := by
  refine length_filter_add_filterMap (fun n => !(old.any fun o => key o == key n))
    (fun n => (old.find? fun o => key o == key n).map (·, n)) (fun n hf => ?_)
    (fun n b hf => ?_) new
  · cases hq : old.find? (fun o => key o == key n) with
    | none => exact (not_any_iff_find_none _ old).mpr hq
    | some o =>
      have hf' : (old.find? fun o => key o == key n).map (·, n) = none := hf
      rw [hq] at hf'
      cases hf'
  · cases hq : old.find? (fun o => key o == key n) with
    | none =>
      have hf' : (old.find? fun o => key o == key n).map (·, n) = some b := hf
      rw [hq] at hf'
      cases hf'
    | some o =>
      have hk : (key o == key n) = true := List.find?_some (p := fun o => key o == key n) hq
      exact (Bool.not_eq_false' _).mpr
        (List.any_eq_true.mpr ⟨o, List.mem_of_find?_eq_some hq, hk⟩)

/-! ## The edges -/

/-- From an empty list every new thing enters: no pair updates, and no thing exits. -/
theorem join_nil_left {α κ : Type} [BEq κ] (key : α → κ) (new : List α) :
    (join key [] new).enter = new ∧ (join key [] new).update = [] ∧
      (join key [] new).exit = [] :=
  ⟨List.filter_eq_self.mpr fun _ _ => rfl, List.filterMap_eq_nil_iff.mpr fun _ _ => rfl, rfl⟩

/-- To an empty list every old thing exits: no thing enters, and no pair updates. -/
theorem join_nil_right {α κ : Type} [BEq κ] (key : α → κ) (old : List α) :
    (join key old []).enter = [] ∧ (join key old []).update = [] ∧
      (join key old []).exit = old :=
  ⟨rfl, rfl, List.filter_eq_self.mpr fun _ _ => rfl⟩

/-- A list joined to itself has no thing that enters. -/
theorem enter_self {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (l : List α) :
    (join key l l).enter = [] :=
  eq_nil_of_no_mem fun n hn =>
    ((mem_enter key l l).mp hn).2 n ((mem_enter key l l).mp hn).1 rfl

/-- A list joined to itself has no thing that exits. -/
theorem exit_self {α κ : Type} [BEq κ] [LawfulBEq κ] (key : α → κ) (l : List α) :
    (join key l l).exit = [] :=
  eq_nil_of_no_mem fun o ho =>
    ((mem_exit key l l).mp ho).2 o ((mem_exit key l l).mp ho).1 rfl

/-! ## Distinct keys -/

/-- The entering things of a new list with distinct keys have distinct keys. -/
theorem distinct_enter {α κ : Type} [BEq κ] (key : α → κ) (old new : List α)
    (hd : Distinct key new) : Distinct key (join key old new).enter :=
  distinct_filter key hd _

/-- The exiting things of an old list with distinct keys have distinct keys. -/
theorem distinct_exit {α κ : Type} [BEq κ] (key : α → κ) (old new : List α)
    (hd : Distinct key old) : Distinct key (join key old new).exit :=
  distinct_filter key hd _

/-- **With distinct keys, two things of a list with one key are one thing.** The key of a
thing names it. -/
theorem eq_of_distinct {α κ : Type} (key : α → κ) : ∀ (l : List α), Distinct key l →
    ∀ (a b : α), a ∈ l → b ∈ l → key a = key b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: rest, hd, a, b, ha, hb, hk => by
    have hd' : key x ∉ rest.map key ∧ (rest.map key).Nodup := List.nodup_cons.mp hd
    rcases List.mem_cons.mp ha with ea | ra
    · rcases List.mem_cons.mp hb with eb | rb
      · exact ea.trans eb.symm
      · exact absurd (List.mem_map.mpr ⟨b, rb, hk.symm.trans (congrArg key ea)⟩) hd'.1
    · rcases List.mem_cons.mp hb with eb | rb
      · exact absurd (List.mem_map.mpr ⟨a, ra, hk.trans (congrArg key eb)⟩) hd'.1
      · exact eq_of_distinct key rest hd'.2 a b ra rb hk

end Whatwg.Svg.Scene
