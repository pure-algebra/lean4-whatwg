import Whatwg.Svg.Scene.Layers

/-!
# Whatwg.Svg.Scene.Layers.Sorted

Owner: an order for a graph with no cycle (slice S22 of `docs/SVG-PACKAGE-PLAN.md`).

`Whatwg/Svg/Scene/Layers.lean` asks its caller for an order that serves the links, and judges
any order with `serves`. It makes none. lean4-effect4 makes one with Kahn's algorithm
(`Flow.kahn` of its `tools/Tools/View/Flow.lean`), tests it, and keeps a second order for the
case that the test fails, since nothing says that Kahn's order passes. This module makes the
order and says when it passes: whenever any order does.

- `sorted r links things`: **an order of the things by peeling sources.** A source is a thing
  with no link into it from the things that are left. The first source of those left is taken,
  and so on until none is left. Where no thing left is a source, the things left are on a cycle
  or after one, and they follow in the order they had.

What the laws say:

- `mem_sorted`, `sorted_nodup`: the order has the things given, and each once where they were
  given once. This asks nothing of the links.
- `sorted_serves`: **the order serves the links whenever some order does.** The things must
  have no thing twice and hold both ends of each link.
- `serves_sorted_iff`: so the links have an order exactly when `sorted` serves them, and
  `Layers.serves` of it decides whether a graph has a cycle.
- `sorted_of_serves`: **an order that serves is left as it is.** A program whose things are
  already in an order that serves gets that order back, so a picture that needs no change of
  order has none.
- `Serves.no_way_back`: where an order serves the links, no way along them from a thing back to
  itself has a length above zero.

What a caller must supply: the things, with both ends of each link among them.

What this module does not claim: that a graph with no cycle has an order, said of cycles and
not of orders (the law here starts from an order that serves; from "no way back" it would need
a count of the things on a way, which is not here); the order that Kahn's algorithm gives,
which keeps a queue of the things that have become sources, where this one takes the first
source of those left each time (the layers are the same by `Layers.heights_unique`); that it
is fast: it reads the links once for each thing left, at each thing taken.

Every law here depends on `propext` and `Quot.sound` at most.
-/

namespace Whatwg.Svg.Scene

namespace Layers

variable {ε ν : Type}

section

variable [DecidableEq ν]

/-- Whether a thing is a source among some things: no link comes into it from one of them. -/
def source (r : Reading ε ν) (links : List ε) (rest : List ν) (v : ν) : Bool :=
  links.all fun e => !(decide (r.dst e = v) && decide (r.src e ∈ rest))

/-- Sources taken one by one from the things left, at most `fuel` of them. What is left when no
thing is a source follows in its order. -/
def peel (r : Reading ε ν) (links : List ε) : Nat → List ν → List ν
  | 0, rest => rest
  | fuel + 1, rest =>
    match rest.find? (source r links rest) with
    | none => rest
    | some v => v :: peel r links fuel (rest.filter fun w => decide (w ≠ v))

/-- **An order of the things by peeling sources**: the first thing with no link into it from
the things left, and so on. -/
def sorted (r : Reading ε ν) (links : List ε) (things : List ν) : List ν :=
  peel r links things.length things

theorem peel_zero (r : Reading ε ν) (links : List ε) (rest : List ν) :
    peel r links 0 rest = rest := rfl

/-- Where a thing left is a source, the first such is taken. -/
theorem peel_some (r : Reading ε ν) (links : List ε) (fuel : Nat) {rest : List ν} {v : ν}
    (h : rest.find? (source r links rest) = some v) :
    peel r links (fuel + 1) rest =
      v :: peel r links fuel (rest.filter fun w => decide (w ≠ v)) := by
  show (match rest.find? (source r links rest) with
    | none => rest
    | some v => v :: peel r links fuel (rest.filter fun w => decide (w ≠ v))) = _
  rw [h]

/-- Where no thing left is a source, the things left follow as they are. -/
theorem peel_none (r : Reading ε ν) (links : List ε) (fuel : Nat) {rest : List ν}
    (h : rest.find? (source r links rest) = none) : peel r links (fuel + 1) rest = rest := by
  show (match rest.find? (source r links rest) with
    | none => rest
    | some v => v :: peel r links fuel (rest.filter fun w => decide (w ≠ v))) = _
  rw [h]

/-! ## The order has the things given -/

/-- The things after one is taken out are the things other than it. -/
private theorem mem_without {rest : List ν} {v w : ν} :
    w ∈ rest.filter (fun u => decide (u ≠ v)) ↔ w ∈ rest ∧ w ≠ v := by
  rw [List.mem_filter, decide_eq_true_iff]

/-- A list without a thing that it had is shorter. -/
private theorem length_without : ∀ {l : List ν} {v : ν}, v ∈ l →
    (l.filter fun u => decide (u ≠ v)).length < l.length
  | [], _, h => nomatch h
  | a :: l, v, h => by
    by_cases e : a = v
    · rw [List.filter_cons_of_neg (p := fun u => decide (u ≠ v))
        (fun hd => (of_decide_eq_true hd : a ≠ v) e)]
      exact Nat.lt_succ_of_le (List.length_filter_le _ l)
    · rw [List.filter_cons_of_pos (p := fun u => decide (u ≠ v)) (decide_eq_true e)]
      have hv : v ∈ l := (List.mem_cons.mp h).resolve_left fun e' => e e'.symm
      exact Nat.succ_lt_succ (length_without hv)

/-- What is peeled has the things that were left. -/
theorem mem_peel (r : Reading ε ν) (links : List ε) : ∀ (fuel : Nat) (rest : List ν) (v : ν),
    v ∈ peel r links fuel rest ↔ v ∈ rest
  | 0, _, _ => Iff.rfl
  | fuel + 1, rest, v => by
    cases hf : rest.find? (source r links rest) with
    | none => rw [peel_none r links fuel hf]
    | some w =>
      rw [peel_some r links fuel hf, List.mem_cons, mem_peel r links fuel _ v, mem_without]
      constructor
      · intro h
        cases h with
        | inl e =>
          rw [e]
          exact List.mem_of_find?_eq_some hf
        | inr h' => exact h'.1
      · intro h
        by_cases e : v = w
        · exact Or.inl e
        · exact Or.inr ⟨h, e⟩

/-- What is peeled from things with no thing twice has no thing twice. -/
theorem peel_nodup (r : Reading ε ν) (links : List ε) : ∀ (fuel : Nat) (rest : List ν),
    rest.Nodup → (peel r links fuel rest).Nodup
  | 0, _, h => h
  | fuel + 1, rest, h => by
    cases hf : rest.find? (source r links rest) with
    | none =>
      rw [peel_none r links fuel hf]
      exact h
    | some w =>
      rw [peel_some r links fuel hf]
      refine List.nodup_cons.mpr ⟨fun hw => ?_, peel_nodup r links fuel _ (h.filter _)⟩
      exact (mem_without.mp ((mem_peel r links fuel _ w).mp hw)).2 rfl

/-- **The order has the things given.** -/
theorem mem_sorted (r : Reading ε ν) (links : List ε) (things : List ν) (v : ν) :
    v ∈ sorted r links things ↔ v ∈ things := mem_peel r links things.length things v

/-- **The order has each thing once**, where the things were given once. -/
theorem sorted_nodup (r : Reading ε ν) (links : List ε) {things : List ν} (h : things.Nodup) :
    (sorted r links things).Nodup := peel_nodup r links things.length things h

/-! ## Where some order serves, a thing left is a source -/

omit [DecidableEq ν] in
/-- A list that is not empty has a thing that a function to whole numbers makes least. -/
private theorem exists_least (h : ν → Int) : ∀ l : List ν, l ≠ [] →
    ∃ v ∈ l, ∀ w ∈ l, h v ≤ h w
  | [], hn => absurd rfl hn
  | [a], _ => ⟨a, List.mem_cons_self, fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Int.le_refl _⟩
  | a :: b :: l, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_least h (b :: l) (List.cons_ne_nil b l)
    cases Int.le_total (h a) (h m) with
    | inl le =>
      refine ⟨a, List.mem_cons_self, fun w hw => ?_⟩
      cases List.mem_cons.mp hw with
      | inl e =>
        rw [e]
        exact Int.le_refl _
      | inr hw' => exact Int.le_trans le (hmin w hw')
    | inr ge =>
      refine ⟨m, List.mem_cons_of_mem a hm, fun w hw => ?_⟩
      cases List.mem_cons.mp hw with
      | inl e =>
        rw [e]
        exact ge
      | inr hw' => exact hmin w hw'

/-- Where a function to whole numbers rises along each link, some thing of a list that is not
empty is a source among the list: one that the function makes least. -/
private theorem exists_source {r : Reading ε ν} {links : List ε} {h : ν → Int}
    (hp : ∀ e ∈ links, h (r.src e) < h (r.dst e)) {rest : List ν} (hn : rest ≠ []) :
    ∃ v ∈ rest, source r links rest v = true := by
  obtain ⟨v, hv, hmin⟩ := exists_least h rest hn
  refine ⟨v, hv, List.all_eq_true.mpr fun e he => ?_⟩
  by_cases hd : r.dst e = v
  · by_cases hs : r.src e ∈ rest
    · have h1 := hmin _ hs
      have h2 := hp e he
      rw [hd] at h2
      exact absurd h1 (by omega)
    · rw [decide_eq_false hs, Bool.and_false]
      rfl
  · rw [decide_eq_false hd, Bool.false_and]
    rfl

/-- A source has no link into it from the things left. -/
private theorem source_spec {r : Reading ε ν} {links : List ε} {rest : List ν} {v : ν}
    (h : source r links rest v = true) {e : ε} (he : e ∈ links) (hd : r.dst e = v) :
    r.src e ∉ rest := fun hs => by
  have h1 := List.all_eq_true.mp h e he
  rw [decide_eq_true hd, decide_eq_true hs] at h1
  exact nomatch h1

/-! ## The order serves -/

/-- Where a function to whole numbers rises along each link, and the fuel is the count of the
things left at least, the source of each link between two things left is peeled before its
target. -/
private theorem peel_before {r : Reading ε ν} {links : List ε} {h : ν → Int}
    (hp : ∀ e ∈ links, h (r.src e) < h (r.dst e)) : ∀ (fuel : Nat) (rest : List ν),
    rest.length ≤ fuel → ∀ e ∈ links, r.src e ∈ rest → r.dst e ∈ rest →
      ∃ i j : Nat, i < j ∧ (peel r links fuel rest)[i]? = some (r.src e) ∧
        (peel r links fuel rest)[j]? = some (r.dst e)
  | 0, rest, hl, _, _, hs, _ => by
    have e0 : rest = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    rw [e0] at hs
    exact nomatch hs
  | fuel + 1, rest, hl, e, he, hs, hd => by
    have hn : rest ≠ [] := fun e0 => by
      rw [e0] at hs
      exact nomatch hs
    obtain ⟨v0, hv0, hsrc0⟩ := exists_source hp hn
    cases hf : rest.find? (source r links rest) with
    | none => exact absurd hsrc0 (List.find?_eq_none.mp hf v0 hv0)
    | some v =>
      have hv : v ∈ rest := List.mem_of_find?_eq_some hf
      have hsv : source r links rest v = true := List.find?_some hf
      have hlen : (rest.filter fun w => decide (w ≠ v)).length ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (length_without hv) hl)
      rw [peel_some r links fuel hf]
      have hdv : r.dst e ≠ v := fun e1 => source_spec hsv he e1 hs
      have hd' : r.dst e ∈ rest.filter fun w => decide (w ≠ v) := mem_without.mpr ⟨hd, hdv⟩
      by_cases hsv' : r.src e = v
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((mem_peel r links fuel _ _).mpr hd')
        refine ⟨0, j + 1, Nat.succ_pos j, ?_, ?_⟩
        · rw [List.getElem?_cons_zero, hsv']
        · rw [List.getElem?_cons_succ]
          exact hj
      · have hs' : r.src e ∈ rest.filter fun w => decide (w ≠ v) := mem_without.mpr ⟨hs, hsv'⟩
        obtain ⟨i, j, hij, hi, hj⟩ := peel_before hp fuel _ hlen e he hs' hd'
        refine ⟨i + 1, j + 1, Nat.succ_lt_succ hij, ?_, ?_⟩
        · rw [List.getElem?_cons_succ]
          exact hi
        · rw [List.getElem?_cons_succ]
          exact hj

/-- **The order serves the links whenever some order does**, where the things have no thing
twice and hold both ends of each link. -/
theorem sorted_serves {r : Reading ε ν} {links : List ε} {things : List ν} (hn : things.Nodup)
    (hin : ∀ e ∈ links, r.src e ∈ things ∧ r.dst e ∈ things)
    (hex : ∃ order, Serves r links order) : Serves r links (sorted r links things) := by
  obtain ⟨order, hs⟩ := hex
  have hu : Serves (⟨r.src, r.dst, fun _ => 1⟩ : Reading ε ν) links order := hs
  have hp : ∀ e ∈ links,
      heights (⟨r.src, r.dst, fun _ => 1⟩ : Reading ε ν) links 0 order (r.src e) <
        heights (⟨r.src, r.dst, fun _ => 1⟩ : Reading ε ν) links 0 order (r.dst e) := fun e he => by
    have h1 : heights (⟨r.src, r.dst, fun _ => 1⟩ : Reading ε ν) links 0 order (r.src e) + 1 ≤
        heights (⟨r.src, r.dst, fun _ => 1⟩ : Reading ε ν) links 0 order (r.dst e) :=
      heights_meets hu 0 he
    omega
  exact ⟨sorted_nodup r links hn, fun e he =>
    peel_before hp things.length things (Nat.le_refl _) e he (hin e he).1 (hin e he).2⟩

/-- **The links have an order exactly when `sorted` serves them.** With `Layers.serves` this
decides whether a graph has a cycle. -/
theorem serves_sorted_iff {r : Reading ε ν} {links : List ε} {things : List ν} (hn : things.Nodup)
    (hin : ∀ e ∈ links, r.src e ∈ things ∧ r.dst e ∈ things) :
    Serves r links (sorted r links things) ↔ ∃ order, Serves r links order :=
  ⟨fun h => ⟨_, h⟩, sorted_serves hn hin⟩

/-! ## An order that serves is left as it is -/

omit [DecidableEq ν] in
/-- In a list with no thing twice, the first thing stands at the first place only. -/
private theorem head_at {x : ν} {xs : List ν} (hx : x ∉ xs) {j : Nat}
    (hj : (x :: xs)[j]? = some x) : j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [List.getElem?_cons_succ] at hj
    exact absurd (List.mem_of_getElem? hj) hx

/-- Things in an order where the source of each link between two of them stands before its
target are peeled as they stand. -/
private theorem peel_of_before {r : Reading ε ν} {links : List ε} : ∀ (fuel : Nat)
    (rest : List ν), rest.Nodup →
    (∀ e ∈ links, r.src e ∈ rest → r.dst e ∈ rest →
      ∃ i j : Nat, i < j ∧ rest[i]? = some (r.src e) ∧ rest[j]? = some (r.dst e)) →
    peel r links fuel rest = rest
  | 0, _, _, _ => rfl
  | fuel + 1, [], _, _ => rfl
  | fuel + 1, x :: xs, hn, hb => by
    have nd := List.nodup_cons.mp hn
    have hsx : source r links (x :: xs) x = true := List.all_eq_true.mpr fun e he => by
      by_cases hd : r.dst e = x
      · by_cases hs : r.src e ∈ x :: xs
        · obtain ⟨i, j, hij, _, hj⟩ := hb e he hs (hd ▸ List.mem_cons_self)
          rw [hd] at hj
          have j0 := head_at nd.1 hj
          exact absurd hij (by omega)
        · rw [decide_eq_false hs, Bool.and_false]
          rfl
      · rw [decide_eq_false hd, Bool.false_and]
        rfl
    have hf : (x :: xs).find? (source r links (x :: xs)) = some x := List.find?_cons_of_pos hsx
    have hrest : (x :: xs).filter (fun w => decide (w ≠ x)) = xs := by
      rw [List.filter_cons_of_neg (p := fun w => decide (w ≠ x))
        (fun hd => (of_decide_eq_true hd : x ≠ x) rfl)]
      exact List.filter_eq_self.mpr fun a ha => decide_eq_true fun e => nd.1 (e ▸ ha)
    rw [peel_some r links fuel hf, hrest]
    refine congrArg (x :: ·) (peel_of_before fuel xs nd.2 fun e he hs hd => ?_)
    obtain ⟨i, j, hij, hi, hj⟩ := hb e he (List.mem_cons_of_mem x hs) (List.mem_cons_of_mem x hd)
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hi
      exact absurd hs ((Option.some.inj hi) ▸ nd.1)
    | succ i =>
      cases j with
      | zero => exact absurd hij (Nat.not_lt_zero _)
      | succ j =>
        rw [List.getElem?_cons_succ] at hi hj
        exact ⟨i, j, Nat.lt_of_succ_lt_succ hij, hi, hj⟩

/-- **An order that serves is left as it is.** -/
theorem sorted_of_serves {r : Reading ε ν} {links : List ε} {things : List ν}
    (h : Serves r links things) : sorted r links things = things :=
  peel_of_before things.length things h.1 fun e he _ _ => h.2 e he

/-- **No way leads back.** Where an order serves the links, no way along them from a thing back
to itself has a length above zero. -/
theorem Serves.no_way_back {r : Reading ε ν} {links : List ε} {order : List ν}
    (h : Serves r links order) {a : ν} {total : Int} (p : Path r links a a total) : total ≤ 0 := by
  have h1 := heights_path h 0 p
  omega

end

end Layers

end Whatwg.Svg.Scene
