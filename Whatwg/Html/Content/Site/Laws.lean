import Whatwg.Html.Content.Site
import Whatwg.Html.Content.Document.Laws

/-!
# Whatwg.Html.Content.Site.Laws

Owner: the laws of the check across a site (`Whatwg/Html/Content/Site.lean`).

- **The check decides the plain statement.** `errors_eq_nil_iff`: `errors s` is empty exactly
  when the site is `Sound`: every page sound alone, a page at the root, one page at a path, a
  page above every page, and every address leading somewhere. The check looks pages and
  identifiers up in tables; `Sound` speaks of lists alone. Each part has its own law
  (`shape_eq_nil_iff`, `pageErrors_eq_nil_iff`, `linkErrors_eq_nil_iff`). `ok_iff` is the same
  law at the Boolean test, and `check?` makes a `Checked` site of one that passes.
- **What it is for an address to lead somewhere.** `faultOf_eq_none_iff`: the address is on no
  `base`, and it leads off the site, or to a file the site lists, or to a folder where a page
  stands, with a fragment that names an identifier of that page as a document's own fragment
  would (`Document.Ref.NamesIn`).
- **A page added to a sound site leaves it sound.** `Sound.add`: the page is sound alone, its
  path is new, a page stands above it, and its own addresses lead somewhere in the larger
  site. No address of an older page is read again: `faultOf_add` says that what led somewhere
  still does. `Checked.add?` is the same as a program: it reads the new page alone and keeps
  the proof for the others.
- **A proof by evaluation.** `sound_iff_onLists`: `Sound` is `SoundOnLists`, whose every part
  is decided on lists, so `by decide +kernel` proves a small site sound.

What the laws do not say: that a browser follows a link to the page this check finds. `resolve`
is the reading of `Site.lean`, with the limits its header lists.
-/

namespace Whatwg.Html.Content.Site

open Whatwg.Html (RawNode)
open Whatwg.Html.Content.Document (Placed Fact Address Ref)

/-! ## The shape of a site -/

/-- The pass from any set, where `prior` lists the paths the set holds: it reports nothing
exactly when no path of the list was met before and none repeats. -/
theorem repeatsFrom_eq_nil_iff :
    ∀ (paths : List (List String)) (seen : Std.HashSet (List String)) (prior : List (List String)),
      (∀ k, seen.contains k = true ↔ k ∈ prior) →
        (repeatsFrom seen paths = [] ↔ (∀ path ∈ paths, path ∉ prior) ∧ paths.Nodup)
  | [], _, _, _ => by
    rw [repeatsFrom]
    exact ⟨fun _ => ⟨fun _ h => (nomatch h), List.nodup_nil⟩, fun _ => rfl⟩
  | path :: rest, seen, prior, hseen => by
    rw [repeatsFrom]
    split
    · next hmet =>
      exact ⟨fun h => (nomatch h), fun h => absurd ((hseen path).mp hmet) (h.1 path List.mem_cons_self)⟩
    · next hmet =>
      have hnew : path ∉ prior := fun h => hmet ((hseen path).mpr h)
      have hseen' : ∀ k, (seen.insert path).contains k = true ↔ k ∈ path :: prior := fun k => by
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hseen k, List.mem_cons, eq_comm]
      rw [repeatsFrom_eq_nil_iff rest _ _ hseen', List.nodup_cons]
      constructor
      · intro ⟨hrest, hnodup⟩
        refine ⟨fun e he => ?_, fun hin => hrest path hin List.mem_cons_self, hnodup⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact hnew
        · exact fun h => hrest e he (List.mem_cons_of_mem _ h)
      · intro ⟨hall, hfresh, hnodup⟩
        refine ⟨fun e he h => ?_, hnodup⟩
        rcases List.mem_cons.mp h with heq | h
        · exact hfresh (heq ▸ he)
        · exact hall e (List.mem_cons_of_mem _ he) h

/-- The pass reports nothing exactly when no path repeats. -/
theorem repeats_eq_nil_iff (paths : List (List String)) : repeats paths = [] ↔ paths.Nodup := by
  rw [repeats, repeatsFrom_eq_nil_iff paths ∅ []
    (fun k => ⟨fun h => by rw [Std.HashSet.contains_empty] at h; exact Bool.noConfusion h,
      fun h => (nomatch h)⟩)]
  exact ⟨fun h => h.2, fun h => ⟨fun _ _ h => (nomatch h), h⟩⟩

/-- A site's shape has no problem exactly when a page stands at the root, no path repeats, and
a page stands above every page but the root. -/
theorem shape_eq_nil_iff (paths : List (List String)) :
    shape paths = [] ↔
      [] ∈ paths ∧ paths.Nodup ∧ ∀ path ∈ paths, path ≠ [] → path.dropLast ∈ paths := by
  have hknown : ∀ k, (Std.HashSet.ofList paths).contains k = true ↔ k ∈ paths := fun k => by
    rw [Std.HashSet.contains_ofList, List.contains_iff_mem]
  show ((if (Std.HashSet.ofList paths).contains [] = true then [] else [Problem.noRoot]) ++
      (repeats paths).map Problem.twoPages ++
      (paths.filter fun path =>
        !path.isEmpty && !(Std.HashSet.ofList paths).contains path.dropLast).map
          Problem.noParent) = [] ↔ _
  rw [List.append_eq_nil_iff, List.append_eq_nil_iff, List.map_eq_nil_iff, List.map_eq_nil_iff,
    repeats_eq_nil_iff, List.filter_eq_nil_iff]
  have hroot : (if (Std.HashSet.ofList paths).contains [] = true then [] else [Problem.noRoot]) = []
      ↔ [] ∈ paths := by
    rw [← hknown []]
    split
    · next h => exact ⟨fun _ => h, fun _ => rfl⟩
    · next h => exact ⟨fun hnil => (nomatch hnil), fun hc => absurd hc h⟩
  have hparents : (∀ path ∈ paths,
      ¬(!path.isEmpty && !(Std.HashSet.ofList paths).contains path.dropLast) = true) ↔
      ∀ path ∈ paths, path ≠ [] → path.dropLast ∈ paths := by
    refine forall_congr' fun path => forall_congr' fun _ => ?_
    rw [← hknown path.dropLast]
    cases path with
    | nil => exact ⟨fun _ h => absurd rfl h, fun _ h => Bool.noConfusion h⟩
    | cons first rest =>
      cases (Std.HashSet.ofList paths).contains (first :: rest).dropLast with
      | true => exact ⟨fun _ _ => rfl, fun _ h => Bool.noConfusion h⟩
      | false => exact ⟨fun h => absurd rfl h, fun h => Bool.noConfusion (h (List.cons_ne_nil _ _))⟩
  rw [hroot, hparents]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-! ## The pages -/

theorem pageErrors_eq_nil_iff (sheets : List Sheet) :
    pageErrors sheets = [] ↔
      ∀ sheet ∈ sheets,
        (Document.problemsOf sheet.facts).filter Document.Problem.isError = [] := by
  simp only [pageErrors, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]

/-! ## The addresses -/

/-- **The table of pages is the list of pages**: a look for the page at a folder gives the test
of the identifiers of the first page with that path. -/
theorem pageAt_index (pages : List Page) (folder : List String) :
    ((Document.firstTable (fun entry => entry.1)
        ((pages.map read).map fun sheet =>
          (sheet.path, Std.HashSet.ofList (Document.namesOf sheet.facts))))[folder]?).map
        (fun entry => entry.2.contains) =
      (pages.find? fun page => page.path == folder).map fun page =>
        (Document.names page.tree).contains := by
  rw [Document.getElem?_firstTable, List.find?_map, List.find?_map, Option.map_map,
    Option.map_map]
  show Option.map (fun page : Page => (Std.HashSet.ofList (Document.names page.tree)).contains)
    (pages.find? fun page => page.path == folder) = _
  congr 1
  funext page x
  exact Std.HashSet.contains_ofList

/-- The check of the addresses reports nothing exactly when no address of any page has a
fault, on the lists of the site. -/
theorem linkErrors_eq_nil_iff (s : Site) :
    linkErrors (s.pages.map read) s.files = [] ↔
      ∀ page ∈ s.pages, ∀ a ∈ Document.addresses page.tree, s.faultOf page.path a.it = none := by
  have hpage : (fun folder =>
      ((Document.firstTable (fun entry => entry.1)
        ((s.pages.map read).map fun sheet =>
          (sheet.path, Std.HashSet.ofList (Document.namesOf sheet.facts))))[folder]?).map
        (fun entry => entry.2.contains)) =
      fun folder => (s.at? folder).map fun page => (Document.names page.tree).contains :=
    funext fun folder => pageAt_index s.pages folder
  have hfile : (Std.HashSet.ofList s.files).contains = fun file => s.files.contains file :=
    funext fun _ => Std.HashSet.contains_ofList
  show (s.pages.map read).flatMap (fun sheet =>
      (Document.addressesIn sheet.facts).filterMap fun a =>
        (fault? (fun folder =>
          ((Document.firstTable (fun entry => entry.1)
            ((s.pages.map read).map fun sheet =>
              (sheet.path, Std.HashSet.ofList (Document.namesOf sheet.facts))))[folder]?).map
            (fun entry => entry.2.contains)) (Std.HashSet.ofList s.files).contains
          sheet.path a.it).map (Problem.ofFault sheet.path a)) = [] ↔ _
  rw [hpage, hfile, List.flatMap_eq_nil_iff, List.forall_mem_map]
  refine forall_congr' fun page => forall_congr' fun _ => ?_
  rw [List.filterMap_eq_nil_iff]
  refine forall_congr' fun a => forall_congr' fun _ => ?_
  rw [Option.map_eq_none_iff]
  rfl

/-! ## The check decides the plain statement -/

/-- **The check decides the plain statement**: a site has no error exactly when every page is
sound alone, a page stands at the root, no two pages stand at one path, a page stands above
every other page, and every address leads to a page (and its fragment to an identifier of that
page), to a file, or off the site. -/
theorem errors_eq_nil_iff (s : Site) : errors s = [] ↔ s.Sound := by
  rw [errors, errorsOf, List.append_eq_nil_iff, List.append_eq_nil_iff, shape_eq_nil_iff,
    pageErrors_eq_nil_iff, linkErrors_eq_nil_iff, List.map_map, List.forall_mem_map,
    List.forall_mem_map]
  constructor
  · intro ⟨⟨⟨hroot, hdistinct, hparents⟩, hpages⟩, hlinks⟩
    exact ⟨fun page hp => (Document.errors_eq_nil_iff page.tree).mp (hpages page hp), hroot,
      hdistinct, hparents, hlinks⟩
  · intro h
    exact ⟨⟨⟨h.root, h.distinct, h.parents⟩,
      fun page hp => (Document.errors_eq_nil_iff page.tree).mpr (h.pages page hp)⟩, h.links⟩

/-- The Boolean test decides the plain statement. -/
theorem ok_iff (s : Site) : ok s = true ↔ s.Sound := by
  rw [ok, List.isEmpty_iff, errors_eq_nil_iff]

/-- `Sound` is decided by the check, with its tables. -/
instance (s : Site) : Decidable s.Sound := decidable_of_iff _ (ok_iff s)

/-- A site as a checked one, when the checker accepts every page at the root of a document and
the site has no error; none otherwise. `Content.explain` of a page and `errors` say why. -/
def check? (s : Site) : Option Checked :=
  if h : (s.pages.all fun page => validIn Ctx.document page.tree) = true ∧ ok s = true then
    some ⟨s, fun page hp => List.all_eq_true.mp h.1 page hp, (ok_iff s).mp h.2⟩
  else none

/-- `check?` answers exactly for a site that passes both checks. -/
theorem isSome_check? (s : Site) :
    (check? s).isSome = true ↔
      (∀ page ∈ s.pages, validIn Ctx.document page.tree = true) ∧ ok s = true := by
  unfold check?
  split
  · next h => exact ⟨fun _ => ⟨List.all_eq_true.mp h.1, h.2⟩, fun _ => rfl⟩
  · next h =>
    exact ⟨fun hsome => (nomatch hsome), fun hboth => absurd ⟨List.all_eq_true.mpr hboth.1, hboth.2⟩ h⟩

/-- The checked site that `check?` answers holds the site it was asked about. -/
theorem site_of_check? {s : Site} {checked : Checked} (h : check? s = some checked) :
    checked.site = s := by
  unfold check? at h
  split at h
  · rw [← Option.some.inj h]
  · exact nomatch h

/-! ## What it is for an address to lead somewhere -/

/-- **An address has no fault exactly when** it is on no `base`, and it leads off the site, or
to a file the site lists, or to a folder where a page stands, with a fragment (if it has one)
that names an identifier of that page as a document's own fragment would. -/
theorem faultOf_eq_none_iff (s : Site) (here : List String) (a : Address) :
    s.faultOf here a = none ↔
      a.element ≠ "base" ∧
        match resolve here a.href with
        | .elsewhere => True
        | .path segments fragment =>
          match folder? segments with
          | none => segments ∈ s.files
          | some folder =>
            ∃ page, s.at? folder = some page ∧
              ∀ f, fragment = some f →
                (⟨a.element, a.attr, .fragment, f⟩ : Ref).NamesIn (Document.names page.tree) := by
  rw [faultOf, fault?]
  split
  · next hbase => exact ⟨fun h => (nomatch h), fun h => absurd (eq_of_beq hbase) h.1⟩
  · next hbase =>
    have hne : a.element ≠ "base" := fun h => hbase (h ▸ beq_self_eq_true _)
    refine ⟨fun h => ⟨hne, ?_⟩, fun h => ?_⟩
    · cases hlead : resolve here a.href with
      | elsewhere => trivial
      | path segments fragment =>
        rw [hlead, faultAt] at h
        show match folder? segments with
          | none => segments ∈ s.files
          | some folder => ∃ page, s.at? folder = some page ∧ _
        cases hfolder : folder? segments with
        | none =>
          rw [hfolder] at h
          show segments ∈ s.files
          apply List.contains_iff_mem.mp
          cases hfile : s.files.contains segments with
          | true => rfl
          | false =>
            simp only [hfile] at h
            exact nomatch h
        | some folder =>
          rw [hfolder] at h
          show ∃ page, s.at? folder = some page ∧ _
          cases hat : s.at? folder with
          | none =>
            simp only [hat, Option.map_none, faultIn] at h
            exact nomatch h
          | some page =>
            refine ⟨page, rfl, fun f hf => ?_⟩
            subst hf
            simp only [hat, Option.map_some, faultIn] at h
            apply (Document.Ref.namesBy_iff (fun _ => List.contains_iff_mem) _).mp
            cases hnames : (⟨a.element, a.attr, .fragment, f⟩ : Ref).namesBy
                (Document.names page.tree).contains with
            | true => rfl
            | false =>
              simp only [hnames] at h
              exact nomatch h
    · have hlead := h.2
      cases hres : resolve here a.href with
      | elsewhere => rfl
      | path segments fragment =>
        rw [hres] at hlead
        rw [faultAt]
        cases hfolder : folder? segments with
        | none =>
          simp only [hfolder] at hlead
          show (if s.files.contains segments = true then none else some (Fault.dead segments)) = none
          rw [if_pos (List.contains_iff_mem.mpr hlead)]
        | some folder =>
          simp only [hfolder] at hlead
          obtain ⟨page, hat, hfragment⟩ := hlead
          show faultIn a segments fragment
            ((s.at? folder).map fun page => (Document.names page.tree).contains) = none
          rw [hat, Option.map_some]
          cases fragment with
          | none => rfl
          | some f =>
            show (if (⟨a.element, a.attr, .fragment, f⟩ : Ref).namesBy
              (Document.names page.tree).contains = true then none else _) = none
            rw [if_pos ((Document.Ref.namesBy_iff (fun _ => List.contains_iff_mem) _).mpr
              (hfragment f rfl))]

/-! ## A page added to a sound site -/

/-- A page that stands at a folder still stands there, and is still the first, when a page is
added after the others. -/
theorem at?_add_of_some {s : Site} (page : Page) (files : List (List String))
    {folder : List String} {found : Page} (h : s.at? folder = some found) :
    (s.add page files).at? folder = some found := by
  rw [at?] at h
  rw [at?, add, List.find?_append, h]
  rfl

/-- A fault does not appear when more folders hold pages and more paths hold files: what led
to a page or a file still does. -/
theorem fault?_mono {pageAt pageAt' : List String → Option (String → Bool)}
    {fileAt fileAt' : List String → Bool}
    (hmore : ∀ folder known, pageAt folder = some known → pageAt' folder = some known)
    (hfiles : ∀ file, fileAt file = true → fileAt' file = true)
    {here : List String} {a : Address} (h : fault? pageAt fileAt here a = none) :
    fault? pageAt' fileAt' here a = none := by
  rw [fault?] at h ⊢
  split
  · next hbase =>
    rw [if_pos hbase] at h
    exact nomatch h
  · next hbase =>
    rw [if_neg hbase] at h
    cases hlead : resolve here a.href with
    | elsewhere => rfl
    | path segments fragment =>
      rw [hlead, faultAt] at h
      rw [faultAt]
      cases hfolder : folder? segments with
      | none =>
        rw [hfolder] at h
        show (if fileAt' segments = true then none else some (Fault.dead segments)) = none
        cases hfile : fileAt segments with
        | true => rw [if_pos (hfiles segments hfile)]
        | false =>
          simp only [hfile] at h
          exact nomatch h
      | some folder =>
        rw [hfolder] at h
        show faultIn a segments fragment (pageAt' folder) = none
        cases hat : pageAt folder with
        | none =>
          simp only [hat, faultIn] at h
          exact nomatch h
        | some known =>
          rw [hmore folder known hat]
          simp only [hat] at h
          exact h

/-- **What led somewhere still does** after a page is added, with any files: no address of an
older page needs reading again. -/
theorem faultOf_add {s : Site} (page : Page) (files : List (List String)) {here : List String}
    {a : Address} (h : s.faultOf here a = none) : (s.add page files).faultOf here a = none := by
  refine fault?_mono (fun folder known hknown => ?_) (fun file hfile => ?_) h
  · cases hat : s.at? folder with
    | none =>
      rw [hat] at hknown
      exact nomatch hknown
    | some found =>
      rw [hat] at hknown
      rw [at?_add_of_some page files hat]
      exact hknown
  · exact List.contains_iff_mem.mpr (List.mem_append_left _ (List.contains_iff_mem.mp hfile))

/-- **A page added to a sound site leaves it sound**, with the files that come with it, when
the page is sound alone, its path is new, a page stands above it, and its own addresses lead
somewhere in the larger site. -/
theorem Sound.add {s : Site} (hs : s.Sound) {page : Page} {files : List (List String)}
    (hpage : Document.Sound page.tree)
    (hnew : page.path ∉ s.pages.map fun page => page.path)
    (habove : page.path.dropLast ∈ s.pages.map fun page => page.path)
    (hlinks : ∀ a ∈ Document.addresses page.tree,
      (s.add page files).faultOf page.path a.it = none) :
    (s.add page files).Sound where
  pages := fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · exact hs.pages p hp
    · rw [List.mem_singleton.mp hp]
      exact hpage
  root := by
    show [] ∈ (s.pages ++ [page]).map fun page => page.path
    rw [List.map_append]
    exact List.mem_append_left _ hs.root
  distinct := by
    show ((s.pages ++ [page]).map fun page => page.path).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hs.distinct, List.pairwise_singleton _ _, fun x hx y hy hxy => ?_⟩
    rw [List.map_singleton, List.mem_singleton] at hy
    exact hnew (hy ▸ hxy ▸ hx)
  parents := fun p hp hroot => by
    show p.path.dropLast ∈ (s.pages ++ [page]).map fun page => page.path
    rw [List.map_append]
    rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append_left _ (hs.parents p hp hroot)
    · rw [List.mem_singleton.mp hp]
      exact List.mem_append_left _ habove
  links := fun p hp a ha => by
    rcases List.mem_append.mp hp with hp | hp
    · exact faultOf_add page files (hs.links p hp a ha)
    · rw [List.mem_singleton.mp hp] at ha ⊢
      exact hlinks a ha

/-- **One more page on a checked site, by reading that page alone**, with the files that come
with it. The page is checked where it stands, its document is checked, its path must be new
and below a page, and its own addresses must lead somewhere in the larger site; the proof for
the older pages is kept, by `Sound.add`. The tree of a page that the new page links to is read for its identifiers. None
when a condition fails; `check?` of the larger site says why. -/
def Checked.add? (checked : Checked) (page : Page) (files : List (List String) := []) :
    Option Checked :=
  if h : validIn Ctx.document page.tree = true ∧ Document.ok page.tree = true ∧
      page.path ∉ checked.site.pages.map (fun page => page.path) ∧
      page.path.dropLast ∈ checked.site.pages.map (fun page => page.path) ∧
      ∀ a ∈ Document.addresses page.tree,
        (checked.site.add page files).faultOf page.path a.it = none then
    some ⟨checked.site.add page files,
      fun p hp => by
        rcases List.mem_append.mp hp with hp | hp
        · exact checked.valid p hp
        · rw [List.mem_singleton.mp hp]
          exact h.1,
      checked.sound.add ((Document.ok_iff page.tree).mp h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩
  else none

/-- The checked site that `add?` answers is the older site with the page added. -/
theorem Checked.site_of_add? {checked larger : Checked} {page : Page} {files : List (List String)}
    (h : checked.add? page files = some larger) : larger.site = checked.site.add page files := by
  unfold Checked.add? at h
  split at h
  · rw [← Option.some.inj h]
  · exact nomatch h

/-! ## A proof by evaluation -/

/-- `Sound`, with every part decided on lists. The kernel cannot run the check's tables, so a
proof by evaluation proves this, and `sound_iff_onLists` gives `Sound`. -/
def SoundOnLists (s : Site) : Prop :=
  (∀ page ∈ s.pages, Document.SoundOnLists page.tree) ∧
    [] ∈ s.pages.map (fun page => page.path) ∧ (s.pages.map fun page => page.path).Nodup ∧
    (∀ page ∈ s.pages, page.path ≠ [] →
      page.path.dropLast ∈ s.pages.map fun page => page.path) ∧
    ∀ page ∈ s.pages, ∀ a ∈ Document.addresses page.tree, s.faultOf page.path a.it = none

instance (s : Site) : Decidable s.SoundOnLists := by
  unfold SoundOnLists
  exact inferInstance

theorem sound_iff_onLists (s : Site) : s.Sound ↔ s.SoundOnLists :=
  ⟨fun h => ⟨fun page hp => (Document.sound_iff_onLists page.tree).mp (h.pages page hp), h.root,
      h.distinct, h.parents, h.links⟩,
    fun ⟨hpages, hroot, hdistinct, hparents, hlinks⟩ =>
      ⟨fun page hp => (Document.sound_iff_onLists page.tree).mpr (hpages page hp), hroot,
        hdistinct, hparents, hlinks⟩⟩

end Whatwg.Html.Content.Site
