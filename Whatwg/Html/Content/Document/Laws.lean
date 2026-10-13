import Whatwg.Html.Content.Document

/-!
# Whatwg.Html.Content.Document.Laws

Owner: the laws of the check across a document (`Whatwg/Html/Content/Document.lean`).

- **The check decides the plain statement.** `errors_eq_nil_iff`: `errors tree` is empty
  exactly when the tree is `Sound`. The check looks identifiers up in a table; `Sound` speaks of
  lists alone. Each part of the check has its own law (`malformed_eq_nil_iff`,
  `duplicates_eq_nil_iff`, `dangling_eq_nil_iff`, `extraMains_eq_nil_iff`, `skips_eq_nil_iff`),
  and `errors_eq` says that the errors are those five parts and nothing of the advice.
  `ok_iff` is the same law at the Boolean test, `Sound` is decidable by it, and `Page.check?`
  makes a `Page` of a tree that passes both checks.
- **A reported clash is real.** `mem_duplicates`: both paths of a `duplicateId` hold that
  identifier.
- **Parts compose.** `ClosedAll.append`: two lists of nodes, each closed, with no identifier in
  common, are closed together. `Closed.element` carries that through an element that has no
  identifier and no reference of its own, and `closed_element_iff` unfolds any element. This is
  what a builder of pictures discharges with distinct stems: each picture closed, and the
  identifiers of two pictures apart. `sound_iff_closed` says what a whole tree needs besides.
- **The facts of an element are read from its attributes.** `namesAt_element` and
  `linksAt_element`: the identifiers of an element are the `id` values of its attributes and
  those of its children, and so for its references.
- **A path names a node.** `factsAt_path`: the path of every fact is a path of the tree, and
  `problems_path` says the same of every problem.
- **What a writer of references gets back.** `fragmentOf?_hash` and `urlTarget?_url`: `#id` and
  `url(#id)` are read back as `id`, whatever the identifier holds.

How a statement is proved for one tree. `ok tree` runs the check with its tables: a program
calls it, and `Page.check?` keeps its answer as a proof. The kernel cannot run a table of
texts. `Closed` and `ClosedAll` are decided on lists, so `by decide +kernel` proves one for a
closed tree, and `sound_iff_closed` reaches `Sound` from there.

What the laws do not say: that `Sound` is what a browser needs to resolve a link. It is the
statement of the rules as `Document.lean` reads them, with the limits its header lists.
-/

namespace Whatwg.Html.Content.Document

open Whatwg.Html (RawNode Walk)

/-! ## The facts, node by node -/

theorem factsAt_element (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    factsAt ns (.element name attrs children) =
      settle (ns.ofElement name) attrs
        ((ownFacts (ns.ofElement name) name attrs).map (fun fact => ⟨[], fact⟩) ++
          if holdsOtherTree (ns.ofElement name) name then []
          else factsAllAt (ns.step name) 0 children) := by
  simp only [factsAt, factsAllAt, Walk.run_element, factsWalk]

theorem factsAt_text (ns : Ns) (content : String) : factsAt ns (.text content) = [] := by
  simp only [factsAt, Walk.run, factsWalk]

theorem factsAt_entity (ns : Ns) (name : String) : factsAt ns (.entity name) = [] := by
  simp only [factsAt, Walk.run, factsWalk]

theorem factsAt_comment (ns : Ns) (content : String) : factsAt ns (.comment content) = [] := by
  simp only [factsAt, Walk.run, factsWalk]

theorem factsAllAt_nil (ns : Ns) (index : Nat) : factsAllAt ns index [] = [] := by
  simp only [factsAllAt, Walk.runAll_nil, gather]

theorem factsAllAt_cons (ns : Ns) (index : Nat) (node : RawNode) (rest : List RawNode) :
    factsAllAt ns index (node :: rest) =
      (factsAt ns node).map (Placed.under index) ++ factsAllAt ns (index + 1) rest := by
  simp only [factsAllAt, factsAt, Walk.runAll_cons, gather]

/-! ## The parts of some facts -/

theorem Fact.ident?_under (offset : Nat) (reset : Bool) (fact : Fact) :
    (fact.under offset reset).ident? = fact.ident? := by
  cases fact <;> rfl

theorem Fact.ref?_under (offset : Nat) (reset : Bool) (fact : Fact) :
    (fact.under offset reset).ref? = fact.ref? := by
  cases fact <;> rfl

theorem namesOf_append (a b : List (Placed Fact)) : namesOf (a ++ b) = namesOf a ++ namesOf b :=
  List.filterMap_append

theorem linksIn_append (a b : List (Placed Fact)) : linksIn (a ++ b) = linksIn a ++ linksIn b :=
  List.filterMap_append

/-- A path is no part of an identifier: the identifiers of some facts seen from the parent are
the same texts. -/
theorem namesOf_map_under (index : Nat) (facts : List (Placed Fact)) :
    namesOf (facts.map (Placed.under index)) = namesOf facts := by
  rw [namesOf, namesOf, List.filterMap_map]
  rfl

theorem linksIn_map_under (index : Nat) (facts : List (Placed Fact)) :
    linksIn (facts.map (Placed.under index)) = linksIn facts := by
  rw [linksIn, linksIn, List.filterMap_map]
  rfl

/-- An ancestor's heading offset changes no identifier. -/
theorem namesOf_settle (ns : Ns) (attrs : List (String × String)) (facts : List (Placed Fact)) :
    namesOf (settle ns attrs facts) = namesOf facts := by
  cases ns with
  | svg => rfl
  | html =>
    rw [settle, namesOf, namesOf, List.filterMap_map]
    congr 1
    funext p
    exact Fact.ident?_under _ _ p.it

theorem linksIn_settle (ns : Ns) (attrs : List (String × String)) (facts : List (Placed Fact)) :
    linksIn (settle ns attrs facts) = linksIn facts := by
  cases ns with
  | svg => rfl
  | html =>
    rw [settle, linksIn, linksIn, List.filterMap_map]
    congr 1
    funext p
    exact Fact.ref?_under _ _ p.it

/-- The identifiers as texts are the identifiers at their paths, without the paths. -/
theorem namesOf_eq_map (facts : List (Placed Fact)) :
    namesOf facts = (idsOf facts).map (·.it) := by
  rw [namesOf, idsOf, List.map_filterMap]
  congr 1
  funext p
  rw [Placed.pick, Option.map_map]
  cases p.it.ident? <;> rfl

theorem linksIn_eq_map (facts : List (Placed Fact)) :
    linksIn facts = (refsOf facts).map (·.it) := by
  rw [linksIn, refsOf, List.map_filterMap]
  congr 1
  funext p
  rw [Placed.pick, Option.map_map]
  cases p.it.ref? <;> rfl

theorem names_eq_map (tree : RawNode) : names tree = (ids tree).map (·.it) :=
  namesOf_eq_map (facts tree)

/-! ## Each part of the check -/

theorem malformed_eq_nil_iff (ids : List (Placed String)) :
    malformed ids = [] ↔ ∀ d ∈ ids, idOk d.it = true := by
  simp only [malformed, List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
    Bool.not_eq_false]

/-- The pass from any table, where `prior` lists the identifiers the table holds: it reports
nothing exactly when no identifier of the list was met before and none repeats. -/
theorem duplicatesFrom_eq_nil_iff :
    ∀ (ds : List (Placed String)) (seen : Std.HashMap String (List Nat)) (prior : List String),
      (∀ k, k ∈ seen ↔ k ∈ prior) →
        (duplicatesFrom seen ds = [] ↔ (∀ d ∈ ds, d.it ∉ prior) ∧ (ds.map (·.it)).Nodup)
  | [], _, _, _ => by
    rw [duplicatesFrom]
    exact ⟨fun _ => ⟨fun _ h => (nomatch h), List.nodup_nil⟩, fun _ => rfl⟩
  | d :: rest, seen, prior, hseen => by
    rw [duplicatesFrom]
    split
    · next first hget =>
      have hmem : d.it ∈ prior :=
        (hseen d.it).mp (Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [hget]; rfl))
      exact ⟨fun h => (nomatch h), fun h => absurd hmem (h.1 d List.mem_cons_self)⟩
    · next hget =>
      have hnew : d.it ∉ prior := fun h => by
        have hsome := Std.HashMap.mem_iff_isSome_getElem?.mp ((hseen d.it).mpr h)
        rw [hget] at hsome
        exact Bool.noConfusion hsome
      have hseen' : ∀ k, k ∈ seen.insert d.it d.path ↔ k ∈ d.it :: prior := fun k => by
        rw [Std.HashMap.mem_insert, beq_iff_eq, hseen k, List.mem_cons, eq_comm]
      rw [duplicatesFrom_eq_nil_iff rest _ _ hseen', List.map_cons, List.nodup_cons]
      constructor
      · intro ⟨hrest, hnodup⟩
        refine ⟨fun e he => ?_, fun hin => ?_, hnodup⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact hnew
          · exact fun h => hrest e he (List.mem_cons_of_mem _ h)
        · obtain ⟨e, he, heq⟩ := List.mem_map.mp hin
          exact hrest e he (heq ▸ List.mem_cons_self)
      · intro ⟨hall, hfresh, hnodup⟩
        refine ⟨fun e he h => ?_, hnodup⟩
        rcases List.mem_cons.mp h with heq | h
        · exact hfresh (List.mem_map.mpr ⟨e, he, heq⟩)
        · exact hall e (List.mem_cons_of_mem _ he) h

/-- The pass over a list reports nothing exactly when no identifier repeats. -/
theorem duplicates_eq_nil_iff (ids : List (Placed String)) :
    duplicates ids = [] ↔ (ids.map (·.it)).Nodup := by
  rw [duplicates, duplicatesFrom_eq_nil_iff ids ∅ []
    (fun k => ⟨fun h => absurd h Std.HashMap.not_mem_empty, fun h => (nomatch h)⟩)]
  exact ⟨fun h => h.2, fun h => ⟨fun _ _ h => (nomatch h), h⟩⟩

/-- The test of a reference by a test of identifiers is the plain statement, when the test
says which texts are identifiers. -/
theorem Ref.namesBy_iff {known : String → Bool} {names : List String}
    (h : ∀ x, known x = true ↔ x ∈ names) (r : Ref) :
    r.namesBy known = true ↔ r.NamesIn names := by
  unfold Ref.namesBy Ref.NamesIn
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, h]
  cases hdecoded : unescape r.target with
  | none =>
    exact or_congr_right (and_congr_right fun _ => or_congr_right
      ⟨fun hf => Bool.noConfusion hf, fun ⟨_, hsome, _⟩ => nomatch hsome⟩)
  | some decoded =>
    refine or_congr_right (and_congr_right fun _ => or_congr_right ?_)
    show (known decoded || isTop decoded) = true ↔ _
    rw [Bool.or_eq_true, h]
    exact ⟨fun hd => ⟨decoded, rfl, hd⟩, fun ⟨_, hsome, hd⟩ => Option.some.inj hsome ▸ hd⟩

/-- A reference that names an identifier of some list names one of any longer list. -/
theorem Ref.NamesIn.mono {r : Ref} {a b : List String} (hab : ∀ x ∈ a, x ∈ b) :
    r.NamesIn a → r.NamesIn b := by
  rintro (h | ⟨hkind, h | ⟨decoded, hdecoded, h | h⟩⟩)
  · exact Or.inl (hab _ h)
  · exact Or.inr ⟨hkind, Or.inl h⟩
  · exact Or.inr ⟨hkind, Or.inr ⟨decoded, hdecoded, Or.inl (hab _ h)⟩⟩
  · exact Or.inr ⟨hkind, Or.inr ⟨decoded, hdecoded, Or.inr h⟩⟩

theorem dangling_eq_nil_iff (names : List String) (refs : List (Placed Ref)) :
    dangling names refs = [] ↔ ∀ r ∈ refs, r.it.NamesIn names := by
  have hknown : ∀ x, (Std.HashSet.ofList names).contains x = true ↔ x ∈ names := fun x => by
    rw [Std.HashSet.contains_ofList, List.contains_iff_mem]
  simp only [dangling, List.map_eq_nil_iff, List.filter_eq_nil_iff, Bool.not_eq_true',
    Bool.not_eq_false, Ref.namesBy_iff hknown]

theorem extraMains_eq_nil_iff (mains : List (Placed Bool)) :
    extraMains mains = [] ↔ (mains.filter fun m => !m.it).length ≤ 1 := by
  unfold extraMains
  generalize mains.filter (fun m => !m.it) = shown
  cases shown with
  | nil => exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | cons first rest =>
    show rest.map _ = [] ↔ _
    rw [List.map_eq_nil_iff, List.length_cons, ← List.length_eq_zero_iff]
    omega

theorem skips_eq_nil_iff (headings : List (Placed Level)) :
    skips headings = [] ↔
      ∀ p ∈ headings.zip headings.tail, p.2.it.value ≤ p.1.it.value + 1 := by
  simp only [skips, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq, Nat.not_lt]

/-! ## Which problems are errors -/

theorem Ref.isError_basis (r : Ref) : r.basis.isError = true := by
  unfold Ref.basis
  split <;> rfl

theorem isError_of_mem_malformed {ids : List (Placed String)} {p : Problem}
    (h : p ∈ malformed ids) : p.isError = true := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp h
  rfl

theorem isError_of_mem_duplicatesFrom :
    ∀ (ds : List (Placed String)) (seen : Std.HashMap String (List Nat)) {p : Problem},
      p ∈ duplicatesFrom seen ds → p.isError = true
  | [], _, _, h => by rw [duplicatesFrom] at h; exact nomatch h
  | d :: rest, seen, p, h => by
    rw [duplicatesFrom] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact isError_of_mem_duplicatesFrom rest _ h
    · exact isError_of_mem_duplicatesFrom rest _ h

theorem isError_of_mem_duplicates {ids : List (Placed String)} {p : Problem}
    (h : p ∈ duplicates ids) : p.isError = true :=
  isError_of_mem_duplicatesFrom ids ∅ h

theorem isError_of_mem_dangling {names : List String} {refs : List (Placed Ref)} {p : Problem}
    (h : p ∈ dangling names refs) : p.isError = true := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp h
  exact Ref.isError_basis r.it

theorem isError_of_mem_extraMains {mains : List (Placed Bool)} {p : Problem}
    (h : p ∈ extraMains mains) : p.isError = true := by
  unfold extraMains at h
  split at h
  · exact nomatch h
  · obtain ⟨m, _, rfl⟩ := List.mem_map.mp h
    rfl

theorem isError_of_mem_skips {headings : List (Placed Level)} {p : Problem}
    (h : p ∈ skips headings) : p.isError = true := by
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp h
  rfl

theorem not_isError_of_mem_topless {headings : List (Placed Level)} {p : Problem}
    (h : p ∈ topless headings) : p.isError = false := by
  unfold topless at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · rw [List.mem_singleton.mp h]
      rfl

/-! ## The check decides the plain statement -/

/-- The errors of a tree are the five parts of the check that are requirements or conventions,
whole, and nothing of the advice. -/
theorem errors_eq (tree : RawNode) :
    errors tree =
      malformed (ids tree) ++ duplicates (ids tree) ++ dangling (names tree) (refs tree) ++
        extraMains (mains tree) ++ skips (headings tree) := by
  rw [errors, problems, problemsOf, List.filter_append, List.filter_append, List.filter_append,
    List.filter_append, List.filter_append,
    List.filter_eq_self.mpr fun _ h => isError_of_mem_malformed h,
    List.filter_eq_self.mpr fun _ h => isError_of_mem_duplicates h,
    List.filter_eq_self.mpr fun _ h => isError_of_mem_dangling h,
    List.filter_eq_self.mpr fun _ h => isError_of_mem_extraMains h,
    List.filter_eq_self.mpr fun _ h => isError_of_mem_skips h,
    List.filter_eq_nil_iff.mpr fun _ h => by rw [not_isError_of_mem_topless h]; exact nofun,
    List.append_nil]
  rfl

/-- **The check decides the plain statement**: a tree has no error exactly when its `id`
values are well formed and distinct, each of its references names an identifier, at most one
`main` is not hidden, and no heading skips a level. -/
theorem errors_eq_nil_iff (tree : RawNode) : errors tree = [] ↔ Sound tree := by
  rw [errors_eq, List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff,
    List.append_eq_nil_iff, malformed_eq_nil_iff, duplicates_eq_nil_iff, dangling_eq_nil_iff,
    extraMains_eq_nil_iff, skips_eq_nil_iff, ← names_eq_map]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun h => ⟨⟨⟨⟨h.wellFormed, h.distinct⟩, h.closed⟩, h.oneMain⟩, h.steps⟩⟩

/-- The Boolean test decides the plain statement. -/
theorem ok_iff (tree : RawNode) : ok tree = true ↔ Sound tree := by
  rw [ok, List.isEmpty_iff, errors_eq_nil_iff]

/-- `Sound` is decided by the check, with its tables: the instance a program runs. The kernel
cannot run a table of texts, so a proof by evaluation goes through `sound_iff_closed`, whose
right side is decided on lists alone. -/
instance (tree : RawNode) : Decidable (Sound tree) := decidable_of_iff _ (ok_iff tree)

/-- Whether a reference names one of a list of identifiers is decided on the list. -/
instance (r : Ref) (names : List String) : Decidable (r.NamesIn names) :=
  decidable_of_iff (r.namesBy (fun x => decide (x ∈ names)) = true)
    (Ref.namesBy_iff (fun _ => decide_eq_true_iff) r)

instance (ns : Ns) (node : RawNode) : Decidable (Closed ns node) := by
  unfold Closed
  exact inferInstance

instance (ns : Ns) (nodes : List RawNode) : Decidable (ClosedAll ns nodes) := by
  unfold ClosedAll
  exact inferInstance

/-- A tree as a page, when the checker accepts it at the root and it has no error across it;
none otherwise. `Content.explain` and `errors` say why. -/
def Page.check? (tree : RawNode) : Option Page :=
  if h : validIn Ctx.document tree = true ∧ ok tree = true then
    some ⟨tree, h.1, (ok_iff tree).mp h.2⟩
  else none

/-- `Page.check?` answers a page exactly for a tree that passes both checks, and the page
holds that tree. -/
theorem Page.check?_eq_some_iff (tree : RawNode) (page : Page) :
    Page.check? tree = some page ↔
      page.tree = tree ∧ validIn Ctx.document tree = true ∧ ok tree = true := by
  unfold Page.check?
  split
  · next h =>
    constructor
    · intro heq
      exact ⟨by rw [← Option.some.inj heq], h⟩
    · rintro ⟨rfl, _⟩
      rfl
  · next h => exact ⟨fun heq => (nomatch heq), fun ⟨_, hv⟩ => absurd hv h⟩

/-! ## A reported clash is real -/

/-- The pass from any table: the first path of a reported clash is in the table under that
identifier or stands earlier in the list, and the second stands in the list. -/
theorem mem_duplicatesFrom :
    ∀ (ds : List (Placed String)) (seen : Std.HashMap String (List Nat)) {id : String}
      {first second : List Nat},
      Problem.duplicateId id first second ∈ duplicatesFrom seen ds →
        (seen[id]? = some first ∨ (⟨first, id⟩ : Placed String) ∈ ds) ∧
          (⟨second, id⟩ : Placed String) ∈ ds
  | [], _, _, _, _, h => by
    rw [duplicatesFrom] at h
    exact nomatch h
  | d :: rest, seen, id, first, second, h => by
    rw [duplicatesFrom] at h
    split at h
    · next found hget =>
      rcases List.mem_cons.mp h with heq | h
      · injection heq with hid hfirst hsecond
        subst hid hfirst hsecond
        exact ⟨Or.inl hget, List.mem_cons_self⟩
      · have ih := mem_duplicatesFrom rest seen h
        exact ⟨ih.1.imp (fun hseen => hseen) (List.mem_cons_of_mem _), List.mem_cons_of_mem _ ih.2⟩
    · next hget =>
      have ih := mem_duplicatesFrom rest (seen.insert d.it d.path) h
      refine ⟨?_, List.mem_cons_of_mem _ ih.2⟩
      rcases ih.1 with hins | hmem
      · rw [Std.HashMap.getElem?_insert] at hins
        split at hins
        · next hbeq =>
          have hid : d.it = id := eq_of_beq hbeq
          have hpath : d.path = first := Option.some.inj hins
          subst hid hpath
          exact Or.inr List.mem_cons_self
        · exact Or.inl hins
      · exact Or.inr (List.mem_cons_of_mem _ hmem)

/-- **A reported clash is real**: both paths of a `duplicateId` hold that identifier. -/
theorem mem_duplicates {ids : List (Placed String)} {id : String} {first second : List Nat}
    (h : Problem.duplicateId id first second ∈ duplicates ids) :
    (⟨first, id⟩ : Placed String) ∈ ids ∧ (⟨second, id⟩ : Placed String) ∈ ids := by
  have hboth := mem_duplicatesFrom ids ∅ h
  refine ⟨hboth.1.resolve_left ?_, hboth.2⟩
  rw [Std.HashMap.getElem?_empty]
  exact nofun

/-! ## The facts of an element, from its attributes -/

theorem filterMap_ident?_map_ident : ∀ ids : List String,
    (ids.map Fact.ident).filterMap Fact.ident? = ids
  | [] => rfl
  | id :: rest => by
    rw [List.map_cons, List.filterMap_cons_some (rfl : (Fact.ident id).ident? = some id),
      filterMap_ident?_map_ident rest]

theorem filterMap_ident?_map_ref : ∀ links : List Ref,
    (links.map Fact.ref).filterMap Fact.ident? = []
  | [] => rfl
  | r :: rest => by
    rw [List.map_cons, List.filterMap_cons_none (rfl : (Fact.ref r).ident? = none),
      filterMap_ident?_map_ref rest]

theorem filterMap_ref?_map_ref : ∀ links : List Ref,
    (links.map Fact.ref).filterMap Fact.ref? = links
  | [] => rfl
  | r :: rest => by
    rw [List.map_cons, List.filterMap_cons_some (rfl : (Fact.ref r).ref? = some r),
      filterMap_ref?_map_ref rest]

theorem filterMap_ref?_map_ident : ∀ ids : List String,
    (ids.map Fact.ident).filterMap Fact.ref? = []
  | [] => rfl
  | id :: rest => by
    rw [List.map_cons, List.filterMap_cons_none (rfl : (Fact.ident id).ref? = none),
      filterMap_ref?_map_ident rest]

theorem filterMap_ident?_markFacts (element : String) (attrs : List (String × String)) :
    (markFacts element attrs).filterMap Fact.ident? = [] := by
  unfold markFacts
  split <;> split <;> rfl

theorem filterMap_ref?_markFacts (element : String) (attrs : List (String × String)) :
    (markFacts element attrs).filterMap Fact.ref? = [] := by
  unfold markFacts
  split <;> split <;> rfl

/-- The identifiers among an element's own facts are the `id` values of its attributes,
whatever the element is. -/
theorem filterMap_ident?_ownFacts (ns : Ns) (element : String) (attrs : List (String × String)) :
    (ownFacts ns element attrs).filterMap Fact.ident? = attrs.filterMap identOf? := by
  have hattrs : ∀ list : List (String × String),
      (list.flatMap fun attr =>
          (identOf? attr).toList.map Fact.ident ++
            (linksOf ns element attr).map Fact.ref).filterMap Fact.ident? =
        list.filterMap identOf? := by
    intro list
    induction list with
    | nil => rfl
    | cons attr rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, List.filterMap_append,
        filterMap_ident?_map_ident, filterMap_ident?_map_ref, List.append_nil, ih]
      cases h : identOf? attr with
      | none => rw [List.filterMap_cons_none h]; rfl
      | some id => rw [List.filterMap_cons_some h]; rfl
  unfold ownFacts
  rw [List.filterMap_append, hattrs]
  cases ns with
  | html => rw [filterMap_ident?_markFacts, List.append_nil]
  | svg => exact List.append_nil _

/-- The references among an element's own facts are those of its attributes. -/
theorem filterMap_ref?_ownFacts (ns : Ns) (element : String) (attrs : List (String × String)) :
    (ownFacts ns element attrs).filterMap Fact.ref? = attrs.flatMap (linksOf ns element) := by
  have hattrs : ∀ list : List (String × String),
      (list.flatMap fun attr =>
          (identOf? attr).toList.map Fact.ident ++
            (linksOf ns element attr).map Fact.ref).filterMap Fact.ref? =
        list.flatMap (linksOf ns element) := by
    intro list
    induction list with
    | nil => rfl
    | cons attr rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, List.filterMap_append,
        filterMap_ref?_map_ident, filterMap_ref?_map_ref, List.nil_append, ih, List.flatMap_cons]
  unfold ownFacts
  rw [List.filterMap_append, hattrs]
  cases ns with
  | html => rw [filterMap_ref?_markFacts, List.append_nil]
  | svg => exact List.append_nil _

theorem namesOf_here (own : List Fact) :
    namesOf (own.map fun fact => (⟨[], fact⟩ : Placed Fact)) = own.filterMap Fact.ident? := by
  rw [namesOf, List.filterMap_map]
  rfl

theorem linksIn_here (own : List Fact) :
    linksIn (own.map fun fact => (⟨[], fact⟩ : Placed Fact)) = own.filterMap Fact.ref? := by
  rw [linksIn, List.filterMap_map]
  rfl

theorem namesAllAt_cons (ns : Ns) (node : RawNode) (rest : List RawNode) :
    namesAllAt ns (node :: rest) = namesAt ns node ++ namesAllAt ns rest := by
  rw [namesAllAt, List.flatMap_cons]
  rfl

theorem linksAllAt_cons (ns : Ns) (node : RawNode) (rest : List RawNode) :
    linksAllAt ns (node :: rest) = linksAt ns node ++ linksAllAt ns rest := by
  rw [linksAllAt, List.flatMap_cons]
  rfl

theorem namesAllAt_append (ns : Ns) (as bs : List RawNode) :
    namesAllAt ns (as ++ bs) = namesAllAt ns as ++ namesAllAt ns bs := by
  rw [namesAllAt, List.flatMap_append]
  rfl

theorem linksAllAt_append (ns : Ns) (as bs : List RawNode) :
    linksAllAt ns (as ++ bs) = linksAllAt ns as ++ linksAllAt ns bs := by
  rw [linksAllAt, List.flatMap_append]
  rfl

/-- The identifiers of a list of children do not read the index of the first. -/
theorem namesOf_factsAllAt (ns : Ns) : ∀ (index : Nat) (nodes : List RawNode),
    namesOf (factsAllAt ns index nodes) = namesAllAt ns nodes
  | _, [] => by
    rw [factsAllAt_nil]
    rfl
  | index, node :: rest => by
    rw [factsAllAt_cons, namesOf_append, namesOf_map_under, namesOf_factsAllAt ns (index + 1) rest,
      namesAllAt_cons, namesAt]

theorem linksIn_factsAllAt (ns : Ns) : ∀ (index : Nat) (nodes : List RawNode),
    linksIn (factsAllAt ns index nodes) = linksAllAt ns nodes
  | _, [] => by
    rw [factsAllAt_nil]
    rfl
  | index, node :: rest => by
    rw [factsAllAt_cons, linksIn_append, linksIn_map_under, linksIn_factsAllAt ns (index + 1) rest,
      linksAllAt_cons, linksAt]

/-- **The identifiers of an element** are the `id` values of its attributes, then those of its
children, in the namespace the element opens. A `template` gives only its own. -/
theorem namesAt_element (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    namesAt ns (.element name attrs children) =
      attrs.filterMap identOf? ++
        if holdsOtherTree (ns.ofElement name) name then []
        else namesAllAt (ns.step name) children := by
  rw [namesAt, factsAt_element, namesOf_settle, namesOf_append, namesOf_here,
    filterMap_ident?_ownFacts]
  split
  · rfl
  · rw [namesOf_factsAllAt]

/-- **The references of an element** are those of its attributes, read in the element's own
namespace, then those of its children. -/
theorem linksAt_element (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    linksAt ns (.element name attrs children) =
      attrs.flatMap (linksOf (ns.ofElement name) name) ++
        if holdsOtherTree (ns.ofElement name) name then []
        else linksAllAt (ns.step name) children := by
  rw [linksAt, factsAt_element, linksIn_settle, linksIn_append, linksIn_here,
    filterMap_ref?_ownFacts]
  split
  · rfl
  · rw [linksIn_factsAllAt]

theorem namesAt_text (ns : Ns) (content : String) : namesAt ns (.text content) = [] := by
  rw [namesAt, factsAt_text]
  rfl

theorem linksAt_text (ns : Ns) (content : String) : linksAt ns (.text content) = [] := by
  rw [linksAt, factsAt_text]
  rfl

/-- Nothing below an SVG element is another tree. -/
theorem holdsOtherTree_svg (element : String) : holdsOtherTree .svg element = false := rfl

/-! ## Parts compose -/

/-- **Two closed parts with no identifier in common are closed together.** This is the law a
builder of pictures discharges: each picture closed, and the identifiers of two pictures kept
apart by their stems. -/
theorem ClosedAll.append {ns : Ns} {as bs : List RawNode} (ha : ClosedAll ns as)
    (hb : ClosedAll ns bs) (hapart : ∀ x ∈ namesAllAt ns as, x ∉ namesAllAt ns bs) :
    ClosedAll ns (as ++ bs) := by
  refine ⟨?_, fun r hr => ?_⟩
  · rw [namesAllAt_append]
    exact List.nodup_append.mpr ⟨ha.1, hb.1, fun x hx y hy hxy => hapart x hx (hxy ▸ hy)⟩
  · rw [linksAllAt_append] at hr
    rw [namesAllAt_append]
    rcases List.mem_append.mp hr with hr | hr
    · exact (ha.2 r hr).mono fun x hx => List.mem_append_left _ hx
    · exact (hb.2 r hr).mono fun x hx => List.mem_append_right _ hx

/-- A list of one node is closed exactly when the node is. -/
theorem closedAll_singleton (ns : Ns) (node : RawNode) : ClosedAll ns [node] ↔ Closed ns node := by
  rw [ClosedAll, Closed, namesAllAt_cons, linksAllAt_cons]
  show (namesAt ns node ++ []).Nodup ∧ (∀ r ∈ linksAt ns node ++ [], r.NamesIn (namesAt ns node ++ []))
    ↔ _
  rw [List.append_nil, List.append_nil]

theorem closedAll_nil (ns : Ns) : ClosedAll ns [] := ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- A closed node before a closed list that shares no identifier with it. -/
theorem ClosedAll.cons {ns : Ns} {node : RawNode} {rest : List RawNode} (hnode : Closed ns node)
    (hrest : ClosedAll ns rest) (hapart : ∀ x ∈ namesAt ns node, x ∉ namesAllAt ns rest) :
    ClosedAll ns (node :: rest) :=
  ClosedAll.append (as := [node]) ((closedAll_singleton ns node).mpr hnode) hrest (by
    rw [namesAllAt_cons]
    show ∀ x ∈ namesAt ns node ++ [], _
    rw [List.append_nil]
    exact hapart)

/-- What it is for an element to be closed, by its attributes and its children. -/
theorem closed_element_iff (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    Closed ns (.element name attrs children) ↔
      (attrs.filterMap identOf? ++
          if holdsOtherTree (ns.ofElement name) name then []
          else namesAllAt (ns.step name) children).Nodup ∧
        ∀ r ∈ attrs.flatMap (linksOf (ns.ofElement name) name) ++
            (if holdsOtherTree (ns.ofElement name) name then []
            else linksAllAt (ns.step name) children),
          r.NamesIn (attrs.filterMap identOf? ++
            if holdsOtherTree (ns.ofElement name) name then []
            else namesAllAt (ns.step name) children) := by
  rw [Closed, namesAt_element, linksAt_element]

/-- **An element with no identifier and no reference of its own is closed when its children
are**, taken together: a `figure`, a `div`, a `g`, or the `svg` of a picture. -/
theorem Closed.element {ns : Ns} {name : String} {attrs : List (String × String)}
    {children : List RawNode} (hids : attrs.filterMap identOf? = [])
    (hlinks : attrs.flatMap (linksOf (ns.ofElement name) name) = [])
    (hchildren : ClosedAll (ns.step name) children) : Closed ns (.element name attrs children) := by
  rw [closed_element_iff, hids, hlinks, List.nil_append, List.nil_append]
  split
  · exact ⟨List.nodup_nil, fun _ h => nomatch h⟩
  · exact hchildren

/-- A leaf of text is closed: it has no fact. -/
theorem closed_text (ns : Ns) (content : String) : Closed ns (.text content) := by
  rw [Closed, namesAt_text, linksAt_text]
  exact ⟨List.nodup_nil, fun _ h => nomatch h⟩

/-- What a whole tree needs besides being closed: well-formed `id` values, one `main` that
shows at most, and an outline with no skipped level. -/
theorem sound_iff_closed (tree : RawNode) :
    Sound tree ↔
      (∀ d ∈ ids tree, idOk d.it = true) ∧ Closed .html tree ∧
        ((mains tree).filter fun m => !m.it).length ≤ 1 ∧
          ∀ p ∈ (headings tree).zip (headings tree).tail, p.2.it.value ≤ p.1.it.value + 1 := by
  have hlinks : (∀ r ∈ refs tree, r.it.NamesIn (names tree)) ↔
      ∀ r ∈ linksAt .html tree, r.NamesIn (namesAt .html tree) := by
    rw [linksAt, linksIn_eq_map]
    constructor
    · intro h r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      exact h x hx
    · intro h r hr
      exact h r.it (List.mem_map.mpr ⟨r, hr, rfl⟩)
  exact ⟨fun h => ⟨h.wellFormed, ⟨h.distinct, hlinks.mp h.closed⟩, h.oneMain, h.steps⟩,
    fun ⟨h1, ⟨h2, h3⟩, h4, h5⟩ => ⟨h1, h2, hlinks.mpr h3, h4, h5⟩⟩

/-! ## What a writer of references gets back -/

/-- A fragment written as `#` and an identifier is read back as that identifier. -/
theorem fragmentOf?_hash (id : String) : fragmentOf? ("#" ++ id) = some id := by
  rw [fragmentOf?, String.toList_append]
  show some (String.ofList id.toList) = some id
  rw [String.ofList_toList]

/-- `url(#id)` is read back as `id`, whatever the identifier holds. -/
theorem urlTarget?_url (id : String) : urlTarget? ("url(#" ++ id ++ ")") = some id := by
  have htext : ("url(#" ++ id ++ ")").toList =
      'u' :: 'r' :: 'l' :: '(' :: '#' :: (id.toList ++ [')']) := by
    rw [String.toList_append, String.toList_append]
    rfl
  rw [urlTarget?, htext]
  show (match (id.toList ++ [')']).reverse with
    | ')' :: body => some (String.ofList body.reverse)
    | _ => none) = some id
  rw [List.reverse_append]
  show some (String.ofList id.toList.reverse.reverse) = some id
  rw [List.reverse_reverse, String.ofList_toList]

/-! ## A path names a node -/

theorem path_of_mem_settle {ns : Ns} {attrs : List (String × String)}
    {facts : List (Placed Fact)} {f : Placed Fact} (h : f ∈ settle ns attrs facts) :
    ∃ g ∈ facts, g.path = f.path := by
  cases ns with
  | svg => exact ⟨f, h, rfl⟩
  | html =>
    rw [settle] at h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
    exact ⟨g, hg, rfl⟩

/-- A fact gathered from children that each hold only paths of their own names a child and a
path inside it. -/
theorem mem_gather_path {children : List RawNode} {results : List (List (Placed Fact))}
    (h : Walk.Related (fun (n : RawNode) (facts : List (Placed Fact)) =>
      ∀ f ∈ facts, (n.at? f.path).isSome = true) children results) :
    ∀ (index : Nat) (f : Placed Fact), f ∈ gather index results →
      ∃ (offset : Nat) (rest : List Nat) (child : RawNode), f.path = (index + offset) :: rest ∧
        children[offset]? = some child ∧ (child.at? rest).isSome = true := by
  induction h with
  | nil =>
    intro index f hf
    rw [gather] at hf
    exact nomatch hf
  | @cons node result nodes results hnode _ ih =>
    intro index f hf
    rw [gather] at hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact ⟨0, g.path, node, rfl, rfl, hnode g hg⟩
    · obtain ⟨offset, rest, child, hpath, hchild, hat⟩ := ih (index + 1) f hf
      refine ⟨offset + 1, rest, child, ?_, hchild, hat⟩
      rw [hpath, Nat.add_assoc, Nat.add_comm 1 offset]

/-- **The path of every fact names a node of the tree.** -/
theorem factsAt_path (ns : Ns) (node : RawNode) {f : Placed Fact} (h : f ∈ factsAt ns node) :
    (node.at? f.path).isSome = true := by
  refine Walk.relate factsWalk
    (fun (n : RawNode) (facts : List (Placed Fact)) => ∀ f ∈ facts, (n.at? f.path).isSome = true)
    ?_ ?_ ?_ ?_ ns node f h
  · intro s name attrs children results hrel f hf
    simp only [factsWalk] at hf
    obtain ⟨g, hg, hpath⟩ := path_of_mem_settle hf
    rw [← hpath]
    rcases List.mem_append.mp hg with hown | hbelow
    · obtain ⟨fact, _, rfl⟩ := List.mem_map.mp hown
      rfl
    · split at hbelow
      · exact nomatch hbelow
      · obtain ⟨offset, rest, child, hp, hchild, hat⟩ := mem_gather_path hrel 0 g hbelow
        rw [hp, Nat.zero_add, RawNode.at?, hchild]
        exact hat
  · intro s content f hf
    exact nomatch hf
  · intro s name f hf
    exact nomatch hf
  · intro s content f hf
    exact nomatch hf

theorem path_of_mem_pick {α : Type} {pick : Fact → Option α} {facts : List (Placed Fact)}
    {x : Placed α} (h : x ∈ facts.filterMap (Placed.pick pick)) : ∃ f ∈ facts, f.path = x.path := by
  obtain ⟨f, hf, hx⟩ := List.mem_filterMap.mp h
  rw [Placed.pick] at hx
  obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hx
  exact ⟨f, hf, rfl⟩

theorem path_of_mem_duplicatesFrom :
    ∀ (ds : List (Placed String)) (seen : Std.HashMap String (List Nat)) {p : Problem},
      p ∈ duplicatesFrom seen ds → ∃ d ∈ ds, d.path = p.path
  | [], _, _, h => by
    rw [duplicatesFrom] at h
    exact nomatch h
  | d :: rest, seen, p, h => by
    rw [duplicatesFrom] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨d, List.mem_cons_self, rfl⟩
      · obtain ⟨e, he, hpath⟩ := path_of_mem_duplicatesFrom rest _ h
        exact ⟨e, List.mem_cons_of_mem _ he, hpath⟩
    · obtain ⟨e, he, hpath⟩ := path_of_mem_duplicatesFrom rest _ h
      exact ⟨e, List.mem_cons_of_mem _ he, hpath⟩

/-- The path of every problem is the path of a fact. -/
theorem problemsOf_path {facts : List (Placed Fact)} {p : Problem} (h : p ∈ problemsOf facts) :
    ∃ f ∈ facts, f.path = p.path := by
  rw [problemsOf] at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
            exact path_of_mem_pick (List.mem_filter.mp hd).1
          · obtain ⟨d, hd, hpath⟩ := path_of_mem_duplicatesFrom _ _ h
            obtain ⟨f, hf, hfd⟩ := path_of_mem_pick hd
            exact ⟨f, hf, hfd.trans hpath⟩
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
          exact path_of_mem_pick (List.mem_filter.mp hr).1
      · unfold extraMains at h
        split at h
        · exact nomatch h
        · next first rest heq =>
          obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
          have hshown : m ∈ (mainsOf facts).filter fun m => !m.it := by
            rw [heq]
            exact List.mem_cons_of_mem _ hm
          exact path_of_mem_pick (List.mem_filter.mp hshown).1
    · obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
      have hzip := (List.mem_filter.mp hpair).1
      exact path_of_mem_pick (List.mem_of_mem_tail (List.of_mem_zip hzip).2)
  · unfold topless at h
    cases hlist : headingsOf facts with
    | nil =>
      simp only [hlist] at h
      exact nomatch h
    | cons first rest =>
      have hfirst : first ∈ headingsOf facts := by
        rw [hlist]
        exact List.mem_cons_self
      simp only [hlist] at h
      split at h
      · exact nomatch h
      · rw [List.mem_singleton.mp h]
        exact path_of_mem_pick hfirst

/-- **The path of every problem names a node of the tree**, so `trail` writes its names. -/
theorem problems_path (tree : RawNode) {p : Problem} (h : p ∈ problems tree) :
    (tree.at? p.path).isSome = true := by
  obtain ⟨f, hf, hpath⟩ := problemsOf_path h
  rw [← hpath]
  exact factsAt_path .html tree hf

end Whatwg.Html.Content.Document
