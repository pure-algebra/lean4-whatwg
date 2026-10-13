import Whatwg.Html.Node.SvgDefs

/-!
# Whatwg.Html.Node.SvgDefs.Laws

Owner: what a picture that was built with `Svg.Defs` is owed (slice S17 of
`docs/SVG-PACKAGE-PLAN.md`). `Whatwg/Html/Node/SvgDefs.lean` has the definitions.

**Identifiers.** The checker judges no identifier, so these are laws of this package's own
reading of one (`SvgNode.id?`, `ids`, `refs`).

- `Defs.name_injective`: the identifier of a place is the stem, a hyphen and the place, and
  two of them are equal only for one stem and one place. So the definitions of one run have
  distinct identifiers (`Defs.nodup_ids_named`, for every program: the runner writes them, and
  no program does), and two runs under two stems share none (`Defs.disjoint_ids_named`): two
  pictures of one page take two stems.
- `Defs.bind_add_apply` and `Defs.add_defined`: wherever `Defs.add` stands in a program, what
  follows it is handed the reference to the place it counted, and the whole run holds the
  definition under that reference's identifier. A reference made by `add` does not dangle.
- `urlRef?_urlRef`, and `SvgAttr.ref?_maskBy` with its like: a reference that a helper writes is
  read back by `SvgNode.refs` as the identifier it was given.
- `SvgNode.linkedAll_iff`: what the test `linked` decides. For a picture that holds an
  identifier typed by hand it is the check to run.

**Structure.** `Def.okAt` is the checker's structure test of a definition, under any
identifier: the test reads keys and no value, so the identifier does not matter
(`Def.okAt_node`). `Svg.okAllAt_withDefs` says that the forest of `Svg.withDefs` passes among
the marks when the program's definitions and its marks do. Each definition of the kit passes,
for every argument: `Def.linearGradient_ok` for every list of stops, `Def.mask_ok`,
`Def.marker_ok` and `Def.group_ok` when their children pass among the marks, `Def.clip_ok` when
its clip path does, and `Def.arrowHead_ok`, `Def.blur_ok` and `Def.dropShadow_ok` as they are.
`Defs.Holds` is a law of a program, proved part by part with `Holds.pure`, `Holds.bind`,
`Holds.add` and `Holds.each`, and `Svg.okAllAt_withDefs_of_holds` reads it: a picture of a list
of edges of any length is proved once.

What this module does not claim: that a reference of a program names a definition of its own
kind in the tree, which the type `Svg.Ref kind` says and no law of the tree repeats; or
anything about a definition with further attributes in `more`, whose keys a caller judges with
`SvgAttr.allOk`.
-/

namespace Whatwg.Html

open Whatwg.Svg.Schema (Tag)
open Whatwg.Html.Schema (Exclusions)
open Whatwg.Html.Content (Pos Ctx validIn valuesOk)
open Whatwg.Svg.Value

/-! ## A reference is read back -/

/-- The characters of a reference: `url(#`, the identifier, `)`. -/
theorem toList_urlRef (id : String) :
    (urlRef id).toList = 'u' :: 'r' :: 'l' :: '(' :: '#' :: (id.toList ++ [')']) := by
  rw [urlRef, String.toList_append, String.toList_append]
  rfl

/-- **A reference written by rule reads back as its identifier.** -/
theorem urlRef?_urlRef (id : String) : urlRef? (urlRef id) = some id := by
  unfold urlRef?
  rw [toList_urlRef]
  show (if (id.toList ++ [')']).getLast? = some ')' then
    some (String.ofList (id.toList ++ [')']).dropLast) else none) = some id
  rw [List.getLast?_concat, if_pos rfl, List.dropLast_concat, String.ofList_toList]

/-- A fragment reads back as its identifier. -/
theorem fragment?_append (id : String) : fragment? ("#" ++ id) = some id := by
  unfold fragment?
  rw [String.toList_append]
  show some (String.ofList id.toList) = some id
  rw [String.ofList_toList]

namespace SvgAttr

variable {t : Tag}

/-- `id` declares its value. -/
theorem id?_ident (id : String) : (SvgAttr.ident (t := t) id).id? = some id := rfl

/-- A paint that is a reference refers to it, in `fill`. -/
theorem ref?_fill (paint : Svg.Ref .paint) : (SvgAttr.fill (t := t) paint).ref? = some paint.id :=
  urlRef?_urlRef paint.id

/-- A paint that is a reference refers to it, in `stroke`. -/
theorem ref?_stroke (paint : Svg.Ref .paint) :
    (SvgAttr.stroke (t := t) paint).ref? = some paint.id :=
  urlRef?_urlRef paint.id

theorem ref?_clipBy (clip : Svg.Ref .clip) : (clipBy (t := t) clip).ref? = some clip.id :=
  urlRef?_urlRef clip.id

theorem ref?_maskBy (mask : Svg.Ref .mask) : (maskBy (t := t) mask).ref? = some mask.id :=
  urlRef?_urlRef mask.id

theorem ref?_filterBy (filter : Svg.Ref .filter) :
    (filterBy (t := t) filter).ref? = some filter.id :=
  urlRef?_urlRef filter.id

theorem ref?_markerStart (marker : Svg.Ref .marker) :
    (markerStart (t := t) marker).ref? = some marker.id :=
  urlRef?_urlRef marker.id

theorem ref?_markerMid (marker : Svg.Ref .marker) :
    (markerMid (t := t) marker).ref? = some marker.id :=
  urlRef?_urlRef marker.id

theorem ref?_markerEnd (marker : Svg.Ref .marker) :
    (markerEnd (t := t) marker).ref? = some marker.id :=
  urlRef?_urlRef marker.id

end SvgAttr

/-- The `href` of a `use` refers to the group it draws. -/
theorem Svg.ref?_use (shape : Svg.Ref .shape) :
    (SvgAttr.attr (t := .use) .href ("#" ++ shape.id)).ref? = some shape.id :=
  fragment?_append shape.id

/-! ## The identifier of a place -/

/-- Two lists that agree up to and after one separator, which neither tail holds, agree in
both parts. -/
theorem append_cons_inj {α : Type} {c : α} : ∀ {a b u v : List α}, c ∉ u → c ∉ v →
    a ++ c :: u = b ++ c :: v → a = b ∧ u = v
  | [], [], _, _, _, _, h => ⟨rfl, List.tail_eq_of_cons_eq h⟩
  | [], y :: b, u, v, hu, _, h => by
    have ht : u = b ++ c :: v := List.tail_eq_of_cons_eq h
    exact absurd (ht ▸ List.mem_append_right b List.mem_cons_self) hu
  | x :: a, [], u, v, _, hv, h => by
    have ht : a ++ c :: u = v := List.tail_eq_of_cons_eq h
    exact absurd (ht ▸ List.mem_append_right a List.mem_cons_self) hv
  | x :: a, y :: b, u, v, hu, hv, h => by
    have hh : x = y := List.head_eq_of_cons_eq h
    have ht : a ++ c :: u = b ++ c :: v := List.tail_eq_of_cons_eq h
    have ih := append_cons_inj hu hv ht
    exact ⟨by rw [hh, ih.1], ih.2⟩

namespace Svg

namespace Defs

/-- No digit of a number is a hyphen. -/
theorem hyphen_not_mem_toDigits (n : Nat) : '-' ∉ Nat.toDigits 10 n := fun h =>
  absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h) (by decide)

/-- The characters of an identifier: the stem, a hyphen, the digits of the place. -/
theorem toList_name (stem : String) (i : Nat) :
    (name stem i).toList = stem.toList ++ '-' :: Nat.toDigits 10 i := by
  rw [name, String.toList_append, String.toList_append, List.append_assoc]
  show stem.toList ++ ("-".toList ++ (Nat.repr i).toList) = _
  rw [Nat.toList_repr]
  rfl

/-- **Two identifiers are one only for one stem and one place.** So the places of one run have
distinct identifiers, and so have two runs under two stems. -/
theorem name_injective {stem stem' : String} {i j : Nat} (h : name stem i = name stem' j) :
    stem = stem' ∧ i = j := by
  have hl := congrArg String.toList h
  rw [toList_name, toList_name] at hl
  have hp := append_cons_inj (hyphen_not_mem_toDigits i) (hyphen_not_mem_toDigits j) hl
  refine ⟨String.toList_injective hp.1, ?_⟩
  have hd := congrArg (fun l => Nat.ofDigitChars 10 l 0) hp.2
  simp only [Nat.ofDigitChars_ten_toDigits] at hd
  exact hd

/-! ## What a program is -/

theorem pure_apply {α : Type} (a : α) (stem : String) (n : Nat) :
    (pure a : Defs α) stem n = (a, []) := rfl

theorem bind_apply {α β : Type} (m : Defs α) (f : α → Defs β) (stem : String) (n : Nat) :
    (m >>= f) stem n =
      ((f (m stem n).1 stem (n + (m stem n).2.length)).1,
        (m stem n).2 ++ (f (m stem n).1 stem (n + (m stem n).2.length)).2) := rfl

theorem add_apply (kind : RefKind) (d : Def) (stem : String) (n : Nat) :
    add kind d stem n = (⟨name stem n⟩, [d]) := rfl

/-- **What follows `add` is handed the reference to the place that `add` counted**, and the
definition stands first among those made from there on. -/
theorem bind_add_apply {β : Type} (kind : RefKind) (d : Def) (f : Ref kind → Defs β)
    (stem : String) (n : Nat) :
    (add kind d >>= f) stem n =
      ((f ⟨name stem n⟩ stem (n + 1)).1, d :: (f ⟨name stem n⟩ stem (n + 1)).2) := rfl

/-! ## The definitions under their identifiers -/

theorem namedFrom_nil (stem : String) (i : Nat) : namedFrom stem i [] = [] := rfl

theorem namedFrom_cons (stem : String) (i : Nat) (d : Def) (ds : List Def) :
    namedFrom stem i (d :: ds) = d.node (name stem i) :: namedFrom stem (i + 1) ds := rfl

/-- **A definition keeps its identifier whatever is made after it**: the definitions of a
longer list start with those of the shorter one, as they were. -/
theorem namedFrom_append (stem : String) : ∀ (i : Nat) (a b : List Def),
    namedFrom stem i (a ++ b) = namedFrom stem i a ++ namedFrom stem (i + a.length) b
  | i, [], b => rfl
  | i, d :: a, b => by
    rw [List.cons_append, namedFrom_cons, namedFrom_cons, namedFrom_append stem (i + 1) a b,
      List.length_cons, List.cons_append, Nat.add_right_comm, Nat.add_assoc]

/-- **A reference made by `add` does not dangle.** For any program before `add` and any after
it, the definitions of the whole hold the definition that `add` made, under the identifier of
the place that `add` counted: the identifier of the reference that the rest of the program was
handed (`bind_add_apply`). -/
theorem add_defined {α β : Type} (kind : RefKind) (m : Defs α) (d : α → Def)
    (f : α → Ref kind → Defs β) (stem : String) (n : Nat) :
    (d (m stem n).1).node (name stem (n + (m stem n).2.length)) ∈
      namedFrom stem n ((m >>= fun a => add kind (d a) >>= f a) stem n).2 := by
  rw [bind_apply, bind_add_apply, namedFrom_append, namedFrom_cons]
  exact List.mem_append_right _ List.mem_cons_self

/-- The element of a definition declares the identifier it is put under. -/
theorem _root_.Whatwg.Html.Svg.Def.id?_node (d : Def) (id : String) :
    (d.node id).id? = some id := rfl

/-- The identifiers that the runner writes are those of the places, in order. -/
theorem ids_namedFrom (stem : String) : ∀ (i : Nat) (ds : List Def),
    (namedFrom stem i ds).filterMap SvgNode.id? = (List.range' i ds.length).map (name stem)
  | i, [] => rfl
  | i, d :: ds => by
    rw [namedFrom_cons, List.filterMap_cons_some (Def.id?_node d (name stem i)),
      ids_namedFrom stem (i + 1) ds, List.length_cons, List.range'_succ, List.map_cons]

/-- **The definitions of every program have distinct identifiers**: the runner writes them, one
for each place, and a program writes none. -/
theorem nodup_ids_named (stem : String) (ds : List Def) :
    ((named stem ds).filterMap SvgNode.id?).Nodup := by
  rw [named, ids_namedFrom]
  exact List.pairwise_map.mpr
    (List.Pairwise.imp (fun hne e => hne (name_injective e).2) List.nodup_range')

/-- The same, of what a run hands back. -/
theorem nodup_ids_run {α : Type} (stem : String) (m : Defs α) :
    ((run stem m).2.filterMap SvgNode.id?).Nodup :=
  nodup_ids_named stem _

/-- **Two runs under two stems share no identifier.** -/
theorem disjoint_ids_named {stem stem' : String} (h : stem ≠ stem') (ds ds' : List Def)
    (id : String) (hid : id ∈ (named stem ds).filterMap SvgNode.id?)
    (hid' : id ∈ (named stem' ds').filterMap SvgNode.id?) : False := by
  rw [named, ids_namedFrom, List.mem_map] at hid hid'
  obtain ⟨i, _, hi⟩ := hid
  obtain ⟨j, _, hj⟩ := hid'
  exact h (name_injective (hi.trans hj.symm)).1

end Defs

/-! ## The structure of a definition -/

/-- The checker's structure test of a definition at a position, under any identifier. -/
def Def.okAt (p : Pos) (d : Def) : Bool := (d.node "").okAt p

/-- The test of a definition does not read its identifier. -/
theorem Def.okAt_node (x : Exclusions) (d : Def) (id : String) :
    (d.node id).okAt (Pos.inSvg x) = d.okAt (Pos.inSvg x) := rfl

/-- The test of a definition among the marks, part by part: its element is admitted, its
attributes with an `id` before them are taken, the counts of its model hold, and its children
pass below it. -/
theorem Def.okAt_mk (x : Exclusions) (t : Tag) (attrs : List (SvgAttr t))
    (children : List SvgNode) :
    Def.okAt (Pos.inSvg x) ⟨t, attrs, children⟩ =
      ((Whatwg.Svg.Content.Ctx.outside.child .svg).admits t &&
        SvgAttr.allOk (SvgAttr.ident "" :: attrs) &&
        Whatwg.Svg.Content.boundsOk t (SvgNode.tags children) &&
        SvgNode.okAllAt (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x t)
          children) :=
  SvgNode.okAt_svg_element _ x t _ children

end Svg

namespace Content

/-- What stands in `defs` stands where the marks of a picture stand. -/
theorem Pos.belowElement_defs (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x .defs = Pos.inSvg x := by
  have h : Whatwg.Svg.Content.Ctx.outside.child .defs = Whatwg.Svg.Content.Ctx.outside.child .svg := by
    decide +kernel
  rw [Pos.belowElement_plain rfl rfl (by decide +kernel), h]

/-- What stands in a mask stands where the marks of a picture stand. -/
theorem Pos.belowElement_mask (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x .mask = Pos.inSvg x := by
  have h : Whatwg.Svg.Content.Ctx.outside.child .mask = Whatwg.Svg.Content.Ctx.outside.child .svg := by
    decide +kernel
  rw [Pos.belowElement_plain rfl rfl (by decide +kernel), h]

/-- What stands in a marker stands where the marks of a picture stand. -/
theorem Pos.belowElement_marker (c : Whatwg.Svg.Content.Ctx) (x : Exclusions) :
    Pos.belowElement c x .marker = Pos.inSvg x := by
  have h : Whatwg.Svg.Content.Ctx.outside.child .marker = Whatwg.Svg.Content.Ctx.outside.child .svg := by
    decide +kernel
  rw [Pos.belowElement_plain rfl rfl (by decide +kernel), h]

end Content

namespace Svg

/-- `defs` passes among the marks exactly when its children do. -/
theorem okAt_defs (x : Exclusions) (children : List SvgNode) :
    (Svg.defs children).okAt (Pos.inSvg x) = SvgNode.okAllAt (Pos.inSvg x) children := by
  have hadm : (Whatwg.Svg.Content.Ctx.outside.child .svg).admits .defs = true := by decide +kernel
  rw [Svg.defs, SvgNode.okAt_svg_element, hadm, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl,
    Pos.belowElement_defs]
  rfl

namespace Defs

/-- The definitions under their identifiers pass among the marks when each definition does. -/
theorem okAllAt_namedFrom (x : Exclusions) (stem : String) : ∀ (i : Nat) (ds : List Def),
    (∀ d ∈ ds, d.okAt (Pos.inSvg x) = true) →
      SvgNode.okAllAt (Pos.inSvg x) (namedFrom stem i ds) = true
  | _, [], _ => rfl
  | i, d :: ds, h => by
    rw [namedFrom_cons, SvgNode.okAllAt_cons, Def.okAt_node, h d List.mem_cons_self,
      okAllAt_namedFrom x stem (i + 1) ds fun e he => h e (List.mem_cons_of_mem d he)]
    rfl

/-- The `defs` of a list of definitions passes among the marks when each definition does. -/
theorem okAllAt_block (x : Exclusions) (stem : String) (ds : List Def)
    (h : ∀ d ∈ ds, d.okAt (Pos.inSvg x) = true) :
    SvgNode.okAllAt (Pos.inSvg x) (block stem ds) = true := by
  cases ds with
  | nil => rfl
  | cons d rest =>
    rw [block, SvgNode.okAllAt_cons, okAt_defs, named, okAllAt_namedFrom x stem 0 _ h]
    rfl

end Defs

/-- **A picture with its definitions passes when its parts do**: the forest of `Svg.withDefs`
passes among the marks when every definition of the program passes and the marks that the
program gives pass. -/
theorem okAllAt_withDefs (x : Exclusions) (stem : String) (m : Defs (List SvgNode))
    (hd : ∀ d ∈ (m stem 0).2, d.okAt (Pos.inSvg x) = true)
    (hm : SvgNode.okAllAt (Pos.inSvg x) (m stem 0).1 = true) :
    SvgNode.okAllAt (Pos.inSvg x) (Svg.withDefs stem m) = true := by
  rw [Svg.withDefs, SvgNode.okAllAt_append, Defs.okAllAt_block x stem _ hd, hm]
  rfl

/-! ## A law of every program, part by part -/

namespace Defs

/-- What a program gives satisfies `P`, and every definition it makes satisfies `Q`, wherever
the program stands: under every stem and after any number of definitions. -/
def Holds {α : Type} (P : α → Prop) (Q : Def → Prop) (m : Defs α) : Prop :=
  ∀ (stem : String) (n : Nat), P (m stem n).1 ∧ ∀ d ∈ (m stem n).2, Q d

/-- A program that makes no definition holds what its value holds. -/
theorem Holds.pure {α : Type} {P : α → Prop} {Q : Def → Prop} {a : α} (h : P a) :
    Holds P Q (pure a : Defs α) :=
  fun _ _ => ⟨h, fun _ hd => nomatch hd⟩

/-- One program and then another: the second is proved for every value that the first may
give. -/
theorem Holds.bind {α β : Type} {P : α → Prop} {P' : β → Prop} {Q : Def → Prop} {m : Defs α}
    {f : α → Defs β} (hm : Holds P Q m) (hf : ∀ a, P a → Holds P' Q (f a)) :
    Holds P' Q (m >>= f) := fun stem n => by
  have h1 := hm stem n
  have h2 := hf (m stem n).1 h1.1 stem (n + (m stem n).2.length)
  rw [bind_apply]
  exact ⟨h2.1, fun d hd => (List.mem_append.mp hd).elim (h1.2 d) (h2.2 d)⟩

/-- `add` holds when its definition does, whatever reference it hands back. -/
theorem Holds.add {kind : RefKind} {P : Ref kind → Prop} {Q : Def → Prop} {d : Def} (hd : Q d)
    (hp : ∀ r, P r) : Holds P Q (add kind d) :=
  fun _ _ => ⟨hp _, fun _ he => (List.mem_singleton.mp he) ▸ hd⟩

/-- A program for each item of a list holds when the program of each item does. -/
theorem Holds.each {α β : Type} {P : β → Prop} {Q : Def → Prop} {f : α → Defs β} :
    ∀ items : List α, (∀ a ∈ items, Holds P Q (f a)) →
      Holds (fun bs => ∀ b ∈ bs, P b) Q (each items f)
  | [], _ => Holds.pure fun _ h => nomatch h
  | a :: rest, h =>
    Holds.bind (h a List.mem_cons_self) fun _ hb =>
      Holds.bind (Holds.each rest fun c hc => h c (List.mem_cons_of_mem a hc)) fun _ hbs =>
        Holds.pure (List.forall_mem_cons.mpr ⟨hb, hbs⟩)

end Defs

/-- **A picture that a program builds passes when the program is proved part by part**: its
marks pass among the marks, and so does each of its definitions. `Holds.bind`, `Holds.add` and
`Holds.each` take a program apart, so a picture of a list of any length is proved once. -/
theorem okAllAt_withDefs_of_holds (x : Exclusions) (stem : String) {m : Defs (List SvgNode)}
    (h : Defs.Holds (fun marks => SvgNode.okAllAt (Pos.inSvg x) marks = true)
      (fun d => d.okAt (Pos.inSvg x) = true) m) :
    SvgNode.okAllAt (Pos.inSvg x) (Svg.withDefs stem m) = true :=
  okAllAt_withDefs x stem m (h stem 0).2 (h stem 0).1

/-! ## Each definition of the kit passes -/

/-- A stop passes in a gradient that stands among the marks. -/
theorem Stop.node_ok (x : Exclusions) (t : Tag) (ht : t = .linearGradient ∨ t = .radialGradient)
    (s : Stop) :
    s.node.okAt (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x t) = true := by
  obtain ⟨offset, color, opacity⟩ := s
  cases ht with
  | inl h => subst h; cases opacity <;> conv => lhs; whnf
  | inr h => subst h; cases opacity <;> conv => lhs; whnf

/-- A linear gradient passes among the marks, for every two points and every list of stops. -/
theorem Def.linearGradient_ok (x : Exclusions) (a b : Vec) (stops : List Stop) (units : Units)
    (places : Nat) : (Def.linearGradient a b stops units [] places).okAt (Pos.inSvg x) = true := by
  have hstops : SvgNode.okAllAt
      (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x .linearGradient)
      (stops.map Stop.node) = true := by
    rw [SvgNode.okAllAt_map, List.all_eq_true]
    exact fun s _ => Stop.node_ok x .linearGradient (Or.inl rfl) s
  rw [Def.linearGradient, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, hstops]
  conv => lhs; whnf

/-- A radial gradient passes among the marks, for every centre, radius and list of stops. -/
theorem Def.radialGradient_ok (x : Exclusions) (center : Vec) (r : Rat) (stops : List Stop)
    (units : Units) (places : Nat) :
    (Def.radialGradient center r stops units [] places).okAt (Pos.inSvg x) = true := by
  have hstops : SvgNode.okAllAt
      (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x .radialGradient)
      (stops.map Stop.node) = true := by
    rw [SvgNode.okAllAt_map, List.all_eq_true]
    exact fun s _ => Stop.node_ok x .radialGradient (Or.inr rfl) s
  rw [Def.radialGradient, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, hstops]
  conv => lhs; whnf

/-- A clip passes among the marks when the clip path of its shapes does, under any
identifier: the premise of `Svg.okAllAt_clipped`. -/
theorem Def.clip_ok (x : Exclusions) (id : String) (shapes : List SvgNode)
    (h : (Svg.clipPath id shapes).okAt (Pos.inSvg x) = true) :
    (Def.clip shapes).okAt (Pos.inSvg x) = true := h

/-- A mask passes among the marks when its children do, with a region or with none. -/
theorem Def.mask_ok (x : Exclusions) (children : List SvgNode) (region : Option Box)
    (places : Nat) (h : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    (Def.mask children region [] places).okAt (Pos.inSvg x) = true := by
  cases region with
  | none =>
    rw [Def.mask, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl,
      Pos.belowElement_mask, h]
    conv => lhs; whnf
  | some b =>
    rw [Def.mask, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl,
      Pos.belowElement_mask, h]
    conv => lhs; whnf

/-- A marker passes among the marks when its children do. -/
theorem Def.marker_ok (x : Exclusions) (size anchor : Vec) (children : List SvgNode)
    (orient : Orient) (units : MarkerUnits) (places : Nat)
    (h : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    (Def.marker size anchor children orient units [] places).okAt (Pos.inSvg x) = true := by
  rw [Def.marker, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl,
    Pos.belowElement_marker, h]
  conv => lhs; whnf

/-- An arrow head passes among the marks, for every size and paint. -/
theorem Def.arrowHead_ok (x : Exclusions) (along across : Rat) (paint : Paint) (places : Nat) :
    (Def.arrowHead along across paint places).okAt (Pos.inSvg x) = true :=
  Def.marker_ok x _ _ _ _ _ _ (by conv => lhs; whnf)

/-- A blur passes among the marks, for every deviation. -/
theorem Def.blur_ok (x : Exclusions) (deviation : Rat) (places : Nat) :
    (Def.blur deviation [] places).okAt (Pos.inSvg x) = true := by
  rw [Def.blur, Def.okAt_mk]
  conv => lhs; whnf

/-- A shadow passes among the marks, for every offset, deviation, colour and opacity. -/
theorem Def.dropShadow_ok (x : Exclusions) (offset : Vec) (deviation : Rat) (color : Rgb)
    (opacity : Decimal) (places : Nat) :
    (Def.dropShadow offset deviation color opacity [] places).okAt (Pos.inSvg x) = true := by
  rw [Def.dropShadow, Def.okAt_mk]
  conv => lhs; whnf

/-- A group that is drawn again passes among the marks when its children do. -/
theorem Def.group_ok (x : Exclusions) (children : List SvgNode)
    (h : SvgNode.okAllAt (Pos.inSvg x) children = true) :
    (Def.group children []).okAt (Pos.inSvg x) = true := by
  rw [Def.group, Def.okAt_mk, Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, Pos.belowElement_g, h]
  conv => lhs; whnf

/-- `use` passes among the marks, for every reference and place. -/
theorem okAt_use (x : Exclusions) (shape : Ref .shape) (place : Vec) (places : Nat) :
    (Svg.use shape place [] places).okAt (Pos.inSvg x) = true := by
  conv => lhs; whnf

end Svg

/-! ## What the test of identifiers decides -/

namespace SvgNode

/-- A list has no text twice exactly when `distinct` says so. -/
theorem distinct_iff : ∀ l : List String, distinct l = true ↔ l.Nodup
  | [] => ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | s :: rest => by
    rw [distinct, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem,
      distinct_iff rest, List.nodup_cons]

/-- **What `linkedAll` decides**: no identifier of the forest is declared twice, and every
identifier that an attribute of the forest refers to is declared in it. -/
theorem linkedAll_iff (nodes : List SvgNode) :
    linkedAll nodes = true ↔
      (idsAll nodes).Nodup ∧ ∀ r ∈ refsAll nodes, r ∈ idsAll nodes := by
  rw [linkedAll, Bool.and_eq_true, distinct_iff, List.all_eq_true]
  exact and_congr_right fun _ => forall₂_congr fun r _ => List.contains_iff_mem

theorem idsAll_append : ∀ a b : List SvgNode, idsAll (a ++ b) = idsAll a ++ idsAll b
  | [], _ => rfl
  | node :: rest, b => by
    rw [List.cons_append, idsAll, idsAll, idsAll_append rest b, List.append_assoc]

theorem refsAll_append : ∀ a b : List SvgNode, refsAll (a ++ b) = refsAll a ++ refsAll b
  | [], _ => rfl
  | node :: rest, b => by
    rw [List.cons_append, refsAll, refsAll, refsAll_append rest b, List.append_assoc]

/-- **Two forests that are each in order and share no identifier are in order together.** It is
stated on the lists of identifiers, so a check of a whole page reads it for its pictures: each
alone in order, and no identifier of one declared in another. -/
theorem linkedAll_append {a b : List SvgNode} (ha : linkedAll a = true) (hb : linkedAll b = true)
    (hd : ∀ i ∈ idsAll a, ∀ j ∈ idsAll b, i ≠ j) : linkedAll (a ++ b) = true := by
  rw [linkedAll_iff] at ha hb ⊢
  rw [idsAll_append, refsAll_append]
  refine ⟨List.nodup_append.mpr ⟨ha.1, hb.1, hd⟩, fun r hr => ?_⟩
  rcases List.mem_append.mp hr with h | h
  · exact List.mem_append_left _ (ha.2 r h)
  · exact List.mem_append_right _ (hb.2 r h)

/-- A mark of a numbered list of calls is a mark of the list. -/
theorem Flat.leaf_mem_numbered {α : Type} (node : SvgNode) : ∀ (n : Nat) (calls : List (Flat α)),
    Flat.leaf node ∈ Flat.numbered n calls → Flat.leaf node ∈ calls
  | _, [], h => nomatch h
  | n, .leaf other :: rest, h => by
    rcases List.mem_cons.mp h with e | h'
    · rw [Flat.leaf.inj e]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (leaf_mem_numbered node n rest h')
  | n, .enter label :: rest, h => by
    rcases List.mem_cons.mp h with e | h'
    · exact nomatch e
    · exact List.mem_cons_of_mem _ (leaf_mem_numbered node (n + 1) rest h')
  | n, .leave :: rest, h => by
    rcases List.mem_cons.mp h with e | h'
    · exact nomatch e
    · exact List.mem_cons_of_mem _ (leaf_mem_numbered node n rest h')

end SvgNode

namespace Svg

/-! ## Identifiers under a stem -/

/-- The identifier is one that a picture under the stem writes: the stem, a hyphen, and a tail
with no hyphen. The identifier of a place, of the title and of the description are such. -/
def Stemmed (stem id : String) : Prop :=
  ∃ tail : List Char, '-' ∉ tail ∧ id.toList = stem.toList ++ '-' :: tail

theorem stemmed_name (stem : String) (i : Nat) : Stemmed stem (Defs.name stem i) :=
  ⟨_, Defs.hyphen_not_mem_toDigits i, Defs.toList_name stem i⟩

theorem stemmed_titleId (stem : String) : Stemmed stem (titleId stem) :=
  ⟨['t', 'i', 't', 'l', 'e'], by decide, by rw [titleId, String.toList_append]; rfl⟩

theorem stemmed_descId (stem : String) : Stemmed stem (descId stem) :=
  ⟨['d', 'e', 's', 'c'], by decide, by rw [descId, String.toList_append]; rfl⟩

/-- **Identifiers under two stems are two identifiers**, for any two stems that differ: the last
hyphen of an identifier ends its stem, so no premise on a stem is needed. -/
theorem Stemmed.ne {stem stem' id id' : String} (h : stem ≠ stem') (hs : Stemmed stem id)
    (hs' : Stemmed stem' id') : id ≠ id' := fun e => by
  obtain ⟨u, hu, hl⟩ := hs
  obtain ⟨v, hv, hl'⟩ := hs'
  subst e
  exact h (String.toList_injective (append_cons_inj hu hv (hl.symm.trans hl')).1)

/-- The title of a picture has no identifier of a place, under any stem: a title is not counted
among the definitions. -/
theorem titleId_ne_name (stem stem' : String) (i : Nat) : titleId stem ≠ Defs.name stem' i :=
  fun e => by
    have hl := congrArg String.toList e
    rw [Defs.toList_name, show (titleId stem).toList = stem.toList ++ '-' :: ['t', 'i', 't', 'l', 'e']
      from by rw [titleId, String.toList_append]; rfl] at hl
    have hp := append_cons_inj (by decide) (Defs.hyphen_not_mem_toDigits i) hl
    have ht : 't' ∈ Nat.toDigits 10 i := hp.2 ▸ List.mem_cons_self
    exact absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) ht) (by decide)

/-- **Two pictures under two stems are in order together when each is alone**, where the
identifiers of each are under its stem. This is what a page of several pictures asks of them. -/
theorem linkedAll_append_of_stems {stem stem' : String} (h : stem ≠ stem') {a b : List SvgNode}
    (ha : SvgNode.linkedAll a = true) (hb : SvgNode.linkedAll b = true)
    (hsa : ∀ id ∈ SvgNode.idsAll a, Stemmed stem id)
    (hsb : ∀ id ∈ SvgNode.idsAll b, Stemmed stem' id) : SvgNode.linkedAll (a ++ b) = true :=
  SvgNode.linkedAll_append ha hb fun i hi j hj => Stemmed.ne h (hsa i hi) (hsb j hj)

/-! ## The identifiers of a build -/

/-- The identifiers that a definition declares besides the one the runner writes: those of its
own attributes and of its children. A definition of the kit whose children declare none has
none. -/
def Def.inner (d : Def) : List String :=
  d.attrs.filterMap SvgAttr.id? ++ SvgNode.idsAll d.children

/-- The identifiers of a definition under an identifier: that one, then its own. -/
theorem Def.ids_node (d : Def) (id : String) : (d.node id).ids = id :: d.inner := by
  rw [Def.node, SvgNode.ids, List.filterMap_cons_some (SvgAttr.id?_ident id)]
  rfl

theorem Defs.idsAll_namedFrom (stem : String) : ∀ (i : Nat) (ds : List Def),
    (∀ d ∈ ds, d.inner = []) →
      SvgNode.idsAll (Defs.namedFrom stem i ds) = (List.range' i ds.length).map (Defs.name stem)
  | _, [], _ => rfl
  | i, d :: ds, h => by
    rw [Defs.namedFrom_cons, SvgNode.idsAll, Def.ids_node, h d List.mem_cons_self,
      idsAll_namedFrom stem (i + 1) ds fun e he => h e (List.mem_cons_of_mem d he),
      List.length_cons, List.range'_succ, List.map_cons]
    rfl

theorem Defs.idsAll_block (stem : String) (ds : List Def) :
    SvgNode.idsAll (Defs.block stem ds) = SvgNode.idsAll (Defs.named stem ds) := by
  cases ds with
  | nil => rfl
  | cons d rest =>
    show ([] ++ SvgNode.idsAll (Defs.named stem (d :: rest))) ++ [] = _
    rw [List.append_nil]
    rfl

/-- **The identifiers of a build are those of its places, in order**, when no definition and no
mark declares one of its own. So they are distinct, and each is under the stem. -/
theorem ids_withDefs (stem : String) (m : Defs (List SvgNode))
    (hd : ∀ d ∈ (m stem 0).2, d.inner = []) (hm : SvgNode.idsAll (m stem 0).1 = []) :
    SvgNode.idsAll (Svg.withDefs stem m) =
      (List.range' 0 (m stem 0).2.length).map (Defs.name stem) := by
  rw [Svg.withDefs, SvgNode.idsAll_append, Defs.idsAll_block, Defs.named,
    Defs.idsAll_namedFrom stem 0 _ hd, hm, List.append_nil]

/-- Every identifier of such a build is under its stem: the premise of
`linkedAll_append_of_stems`. -/
theorem stemmed_ids_withDefs (stem : String) (m : Defs (List SvgNode))
    (hd : ∀ d ∈ (m stem 0).2, d.inner = []) (hm : SvgNode.idsAll (m stem 0).1 = []) :
    ∀ id ∈ SvgNode.idsAll (Svg.withDefs stem m), Stemmed stem id := by
  rw [ids_withDefs stem m hd hm]
  intro id hid
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hid
  exact hi ▸ stemmed_name stem i

/-! ## A link -/

end Svg

/-- The position of what stands in a link among the marks of a picture: what may stand among
the marks, and no other link. -/
abbrev Content.Pos.inLink (x : Exclusions) : Pos :=
  .svg ((Whatwg.Svg.Content.Ctx.outside.child .svg).child .a) x

namespace Svg

/-- A link among the marks passes exactly when its children pass in a link. The schema's `a`
takes `href`, and stands wherever a mark stands, in a group at any depth. -/
theorem okAt_link (x : Exclusions) (href : String) (children : List SvgNode) :
    (Svg.link href children).okAt (Pos.inSvg x) = SvgNode.okAllAt (Pos.inLink x) children := by
  have hadm : (Whatwg.Svg.Content.Ctx.outside.child .svg).admits .a = true := by decide +kernel
  have hattr : SvgAttr.allOk [SvgAttr.attr (t := .a) .href href] = true := by conv => lhs; whnf
  rw [Svg.link, SvgNode.okAt_svg_element, hadm, hattr,
    Whatwg.Svg.Content.boundsOk_of_bounds_nil rfl, Pos.belowElement_of_none rfl]
  rfl

/-- **A link passes among the marks when its children pass in a link.** -/
theorem link_ok (x : Exclusions) (href : String) (children : List SvgNode)
    (h : SvgNode.okAllAt (Pos.inLink x) children = true) :
    (Svg.link href children).okAt (Pos.inSvg x) = true := by
  rw [okAt_link, h]

/-! ## A picture that is read by name -/

/-- The title of a picture passes as a child of its `svg`, where the HTML around the picture
does not exclude character data: what stands in a `title` is HTML phrasing content, and its
text is judged under the exclusions that pass through the `svg`. -/
theorem titleNode_ok (x : Exclusions) (hx : Ctx.excluded x .pcdata = false) (stem label : String) :
    (titleNode stem label).okAt (Pos.inSvg x) = true := by
  have ht : SvgNode.okAt (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x .title)
      (.text label) = true := by
    rw [SvgNode.okAt]
    conv => lhs; whnf
    rw [hx]
  rw [titleNode, SvgNode.okAt_svg_element, SvgNode.okAllAt_cons, SvgNode.okAllAt_nil, ht]
  conv => lhs; whnf

/-- The description of a picture passes as a child of its `svg`, under the same premise. -/
theorem descNode_ok (x : Exclusions) (hx : Ctx.excluded x .pcdata = false) (stem text : String) :
    (descNode stem text).okAt (Pos.inSvg x) = true := by
  have ht : SvgNode.okAt (Pos.belowElement (Whatwg.Svg.Content.Ctx.outside.child .svg) x .desc)
      (.text text) = true := by
    rw [SvgNode.okAt]
    conv => lhs; whnf
    rw [hx]
  rw [descNode, SvgNode.okAt_svg_element, SvgNode.okAllAt_cons, SvgNode.okAllAt_nil, ht]
  conv => lhs; whnf

/-- **A picture that is read by name passes when its children do**, with a description or with
none, at every HTML position that admits `svg` and does not exclude character data below it
(`hx`, which flow content gives by one evaluation). `hm` is one evaluation of the keys of its
attributes. -/
theorem okIn_titled (ctx : Ctx) (hctx : ctx.admits .svg = true)
    (hx : Ctx.excluded (ctx.child .svg).excl .pcdata = false) (stem label : String)
    {more : List (SvgAttr .svg)} {children : List SvgNode} (desc : Option String)
    (hm : SvgAttr.allOk (.xmlns :: (titledAttrs stem desc.isSome ++ more)) = true)
    (h : SvgNode.okAllAt (Pos.belowSvg ctx) children = true) :
    (titled stem label more children desc).okIn ctx = true := by
  cases desc with
  | none =>
    show SvgNode.okIn ctx
      (.element .svg (.xmlns :: (titledAttrs stem false ++ more)) (titleNode stem label :: children)) =
        true
    have hm' : SvgAttr.allOk (.xmlns :: (titledAttrs stem false ++ more)) = true := hm
    rw [SvgNode.okIn_svg, hctx, hm', SvgNode.okAllAt_cons, titleNode_ok _ hx, h]
    rfl
  | some text =>
    show SvgNode.okIn ctx
      (.element .svg (.xmlns :: (titledAttrs stem true ++ more))
        (titleNode stem label :: descNode stem text :: children)) = true
    have hm' : SvgAttr.allOk (.xmlns :: (titledAttrs stem true ++ more)) = true := hm
    rw [SvgNode.okIn_svg, hctx, hm', SvgNode.okAllAt_cons, SvgNode.okAllAt_cons,
      titleNode_ok _ hx, descNode_ok _ hx, h]
    rfl

/-! ## Cuts as definitions -/

/-- **The cuts of every flat list of calls pass**, balanced or not: the marks of `Defs.cuts`
pass among the marks when each mark of the list does, and each of its definitions passes when
the clip path of each label does. With `okAllAt_withDefs_of_holds` this is the structure of the
picture, for every list of calls and under every stem. -/
theorem Defs.cuts_holds {α : Type} (x : Exclusions) (clip : α → List SvgNode)
    (calls : List (SvgNode.Flat α))
    (hl : ∀ node, SvgNode.Flat.leaf node ∈ calls → node.okAt (Pos.inSvg x) = true)
    (hc : ∀ label, (Svg.clipPath "" (clip label)).okAt (Pos.inSvg x) = true) :
    Defs.Holds (fun marks => SvgNode.okAllAt (Pos.inSvg x) marks = true)
      (fun d => d.okAt (Pos.inSvg x) = true) (Defs.cuts clip calls) :=
  fun stem n =>
    ⟨SvgNode.okAllAt_nest _ _
        (fun k kids hk => by
          show SvgNode.okAllAt (Pos.inSvg x)
            [Svg.g [SvgAttr.clipBy ⟨Defs.name stem k.1⟩] kids] = true
          rw [SvgNode.okAllAt_cons, SvgNode.okAllAt_nil, Svg.okAt_g, hk]
          conv => lhs; whnf)
        _ (fun node hn => hl node (SvgNode.Flat.leaf_mem_numbered node n calls hn)),
      fun d hd => by
        obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hd
        exact hlabel ▸ Def.clip_ok x "" _ (hc label)⟩

/-! ## The closing laws of a picture -/

/-- **What every picture of a frame is owed, in one**: it passes the structure test at every
HTML position that admits `svg`, the checker accepts its raw tree in flow content (law V8), and
every value of it is of its grammar (law V7). A writer proves its marks, and the keys of its
further attributes by one evaluation. -/
theorem Frame.picture_laws (f : Frame) {more : List (SvgAttr .svg)}
    (hm : SvgAttr.allOk (.xmlns :: (more ++ f.attrs)) = true) {marks : List SvgNode}
    (h : ∀ x : Exclusions, SvgNode.okAllAt (Pos.inSvg x) marks = true) :
    (∀ ctx : Ctx, ctx.admits .svg = true → (f.svg more marks).okIn ctx = true) ∧
      validIn Ctx.flow (f.svg more marks).toRaw = true ∧
      valuesOk (f.svg more marks).toRaw = true :=
  ⟨fun _ hctx => Frame.okIn_of hctx f hm (h _),
    SvgNode.validIn_of_okIn (Frame.okIn_of (by decide +kernel) f hm (h _)),
    SvgNode.valuesOk_toRaw _⟩

end Svg

end Whatwg.Html
