import Whatwg.Html.Node.Nav
import Whatwg.Html.Content.Document.Addresses
import Whatwg.Html.Content.Site.Link.Laws
import Whatwg.Html.Content.Structure

/-!
# Whatwg.Html.Node.Nav.Laws

Owner: the laws of the navigations of `Whatwg/Html/Node/Nav.lean`, and the items that are
written from the paths of a site's pages.

- **Where the current page is marked.** `places_listRaw`: the places of the fact
  `Structure.Fact.currentPage` in a list are the links of the items that are marked as the
  page, each at the path `[0, k, 0]` of the k-th item. `places_trail`: a trail of at least one
  crumb shows the fact once, at its last crumb. A sheet's rule for the current page draws that
  element and no other.
- **What addresses a navigation holds.** `hrefsAt_listRaw` and `hrefsAt_pagerRaw`: one address
  for each item, its `href`, unless that is a fragment of the page itself. These are the
  addresses that the check of a site reads (`Document.addresses_eq_hrefsAt`).
- **A navigation written from a site's paths has no dead link.** `Item.toPage here there` is
  the item that leads from the page at `here` to the page at `there`, by `Site.linkTo`.
  `Item.leads_toPage` says that its link has no fault where a page stands at `there`, and
  `list_leads`, `trail_leads`, `pager_leads` that a navigation whose every item leads
  somewhere holds no address with a fault. That is the premise `Sound.links` of a sound site, and of `Sound.add`,
  for the part of a page that is its navigation.
- **One current page among distinct pages.** `Item.toSection here there` marks the link to the
  page itself as `page` and a link to a page above it as `true`. `pages_toSection_le`: among
  links to distinct paths at most one is the page, and `pages_toSection_of_mem` that it is the
  one whose path is the page's.

What the laws do not say: that a reader is told the current page. `aria-current` is from
memory of WAI-ARIA, which is not sealed here (debt D138); the law is about the attribute in the
tree. And nothing is said of an `href` that leads off the site: `Site.resolve` counts those and
judges none.
-/

namespace Whatwg.Html.Nav

open Whatwg.Html.Content
open Whatwg.Html.Content.Structure (Spot Where places placesOf placesAmong)
open Whatwg.Html.Content.Document (Address hrefsAt hrefsAllAt)

/-! ## Where the current page is marked -/

/-- The place of the current page: the fact `Structure.Fact.currentPage`, the element with
`aria-current="page"`. -/
def pageMark : Where := Structure.Fact.currentPage.place

/-- The item is marked as the page. -/
def Item.isPage (i : Item) : Bool := i.current == some "page"

/-- The indices of the items that are marked as the page, the first item at `index`. -/
def Item.pagesFrom : Nat → List Item → List Nat
  | _, [] => []
  | index, i :: rest => (if i.isPage then [index] else []) ++ Item.pagesFrom (index + 1) rest

/-- The indices of the items that are marked as the page. -/
def Item.pages (items : List Item) : List Nat := Item.pagesFrom 0 items

/-- The fact holds of an item's link exactly when the item is marked as the page. -/
theorem holds_link (i : Item) (before after : Nat) (above : List Spot) :
    pageMark.holds (⟨"a", rawAttrs i.attrs, before, after⟩ :: above) = i.isPage := by
  obtain ⟨href, label, current⟩ := i
  cases current <;> rfl

theorem placesOf_linkRaw (i : Item) (above : List Spot) (before after : Nat) :
    placesOf pageMark above before after i.linkRaw = if i.isPage then [[]] else [] := by
  rw [Item.linkRaw, placesOf, holds_link, placesAmong, placesOf, placesAmong]
  exact List.append_nil _

theorem placesOf_entryRaw (i : Item) (above : List Spot) (before after : Nat) :
    placesOf pageMark above before after i.entryRaw = if i.isPage then [[0]] else [] := by
  have hli : pageMark.holds (⟨"li", [], before, after⟩ :: above) = false := rfl
  rw [Item.entryRaw, placesOf, hli, placesAmong, placesOf_linkRaw, placesAmong]
  cases i.isPage <;> rfl

/-- The places of the fact among the items of a list: the link of each item that is marked. -/
theorem placesAmong_entries (chain : List Spot) : ∀ (items : List Item) (index before : Nat),
    placesAmong pageMark chain index before (items.map Item.entryRaw) =
      (Item.pagesFrom index items).map fun k => [k, 0]
  | [], _, _ => by
    rw [List.map_nil, placesAmong]
    rfl
  | i :: rest, index, before => by
    rw [List.map_cons, placesAmong, placesOf_entryRaw, placesAmong_entries chain rest,
      Item.pagesFrom, List.map_append]
    cases i.isPage <;> rfl

/-- **Where a list marks the current page**: the fact `currentPage` holds at the link of each
item that is marked as the page, and nowhere else in the navigation. The k-th item's link is at
the path `[0, k, 0]`: the `ol`, the item, its link. -/
theorem places_listRaw (name : Region.Name) (items : List Item) (className : Option String) :
    places pageMark (listRaw name items className) = (Item.pages items).map fun k => [0, k, 0] := by
  have hnav : pageMark.holds [⟨"nav", rawAttrs (attrs name className), 0, 0⟩] = false := by
    cases name <;> cases className <;> rfl
  have hol : ∀ before after above, pageMark.holds (⟨"ol", [], before, after⟩ :: above) = false :=
    fun _ _ _ => rfl
  rw [places, listRaw, placesOf, hnav, placesAmong, placesOf, hol, placesAmong_entries, placesAmong,
    Item.pages]
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.append_nil, List.map_map]
  rfl

/-- The items of a trail that are marked as the page: the last, and no other. -/
theorem pagesFrom_trail : ∀ (crumbs : List (String × String)) (index : Nat), crumbs ≠ [] →
    Item.pagesFrom index (Item.trail crumbs) = [index + (crumbs.length - 1)]
  | [], _, h => absurd rfl h
  | [crumb], index, _ => rfl
  | crumb :: next :: rest, index, _ => by
    have hnext := pagesFrom_trail (next :: rest) (index + 1) (List.cons_ne_nil _ _)
    rw [Item.trail, Item.pagesFrom, hnext]
    show [index + 1 + (rest.length + 1 - 1)] = [index + (rest.length + 1 + 1 - 1)]
    congr 1
    omega

/-- **A trail marks the current page once**: a trail of at least one crumb shows the fact
`currentPage` at one place, the link of its last crumb. -/
theorem places_trail (name : Region.Name) (crumbs : List (String × String))
    (className : Option String) (h : crumbs ≠ []) :
    places pageMark (listRaw name (Item.trail crumbs) className) = [[0, crumbs.length - 1, 0]] := by
  rw [places_listRaw, Item.pages, pagesFrom_trail crumbs 0 h, Nat.zero_add]
  rfl

/-! ## The addresses of a navigation -/

/-- The address that an item's link holds: its `href`, unless that is `#` and a fragment, which
is a reference to the page itself and no address. -/
def Item.address? (i : Item) : Option Address :=
  if (Document.fragmentOf? i.href).isSome then none else some ⟨"a", "href", i.href⟩

/-- The addresses among the attributes of an item's link: that of its `href`. The mark holds
none. -/
theorem flatMap_attrs (i : Item) :
    (rawAttrs i.attrs).flatMap (Document.htmlAddresses "a") = i.address?.toList := by
  obtain ⟨href, label, current⟩ := i
  have hhref : Document.htmlAddresses "a" ("href", href) =
      (Item.address? ⟨href, label, current⟩).toList := by
    unfold Item.address? Document.htmlAddresses
    cases (Document.fragmentOf? href).isSome <;> rfl
  cases current with
  | none =>
    show Document.htmlAddresses "a" ("href", href) ++ [] = _
    rw [List.append_nil, hhref]
  | some how =>
    show Document.htmlAddresses "a" ("href", href) ++ ([] ++ []) = _
    rw [List.append_nil, List.append_nil, hhref]

theorem hrefsAt_linkRaw (i : Item) : hrefsAt .html i.linkRaw = i.address?.toList := by
  rw [Item.linkRaw, Document.hrefsAt_htmlElement rfl rfl, flatMap_attrs, Document.hrefsAllAt_cons,
    Document.hrefsAt_text, Document.hrefsAllAt_nil, List.append_nil, List.append_nil]

theorem hrefsAt_entryRaw (i : Item) : hrefsAt .html i.entryRaw = i.address?.toList := by
  rw [Item.entryRaw, Document.hrefsAt_htmlElement rfl rfl, Document.hrefsAllAt_cons,
    hrefsAt_linkRaw, Document.hrefsAllAt_nil, List.append_nil]
  rfl

theorem hrefsAllAt_entries : ∀ items : List Item,
    hrefsAllAt .html (items.map Item.entryRaw) = items.flatMap fun i => i.address?.toList
  | [] => rfl
  | i :: rest => by
    rw [List.map_cons, Document.hrefsAllAt_cons, hrefsAt_entryRaw, hrefsAllAt_entries rest,
      List.flatMap_cons]

/-- The attributes of a navigation hold no address. -/
theorem flatMap_nav_attrs (name : Region.Name) (className : Option String) :
    (rawAttrs (attrs name className)).flatMap (Document.htmlAddresses "nav") = [] := by
  cases name <;> cases className <;> rfl

/-- **The addresses of a list**: one for each item, its `href`, unless that is a fragment. -/
theorem hrefsAt_listRaw (name : Region.Name) (items : List Item) (className : Option String) :
    hrefsAt .html (listRaw name items className) = items.flatMap fun i => i.address?.toList := by
  rw [listRaw, Document.hrefsAt_htmlElement rfl rfl, flatMap_nav_attrs, List.nil_append,
    Document.hrefsAllAt_cons, Document.hrefsAt_htmlElement rfl rfl, hrefsAllAt_entries,
    Document.hrefsAllAt_nil, List.append_nil]
  rfl

theorem hrefsAt_turnRaw (rel word : String) (i : Item) (wordClass : Option String) :
    hrefsAt .html (turnRaw rel word i wordClass) = i.address?.toList := by
  have hspan : hrefsAt .html
      (.element "span" (rawAttrs (A.opt Region.classAttr wordClass)) [.text word]) = [] := by
    rw [Document.hrefsAt_htmlElement rfl rfl, Document.hrefsAllAt_cons, Document.hrefsAt_text,
      Document.hrefsAllAt_nil]
    cases wordClass <;> rfl
  rw [turnRaw, Document.hrefsAt_htmlElement rfl rfl, Document.hrefsAllAt_cons, hspan,
    Document.hrefsAllAt_cons, Document.hrefsAt_text, Document.hrefsAllAt_nil]
  show ([] ++ (rawAttrs i.attrs).flatMap (Document.htmlAddresses "a")) ++ ([] ++ ([] ++ [])) = _
  rw [flatMap_attrs]
  simp only [List.nil_append, List.append_nil]

/-- **The addresses of a pager**: that of the link before, then that of the link after. -/
theorem hrefsAt_pagerRaw (name : Region.Name) (previous next : Option Item) (words : String × String)
    (className wordClass : Option String) :
    hrefsAt .html (pagerRaw name previous next words className wordClass) =
      (previous.toList ++ next.toList).flatMap fun i => i.address?.toList := by
  rw [pagerRaw, Document.hrefsAt_htmlElement rfl rfl, flatMap_nav_attrs, List.nil_append,
    Document.hrefsAllAt_append]
  cases previous <;> cases next <;>
    simp only [Option.map_none, Option.map_some, Option.toList_none, Option.toList_some,
      Document.hrefsAllAt_nil, Document.hrefsAllAt_cons, hrefsAt_turnRaw, List.append_nil,
      List.nil_append, List.flatMap_cons, List.flatMap_nil, List.cons_append]

/-! ## A navigation written from a site's paths -/

/-- The item's link leads somewhere in the site, from the page at `here`: its address has no
fault. An item whose `href` is a fragment holds no address, and leads somewhere by that. -/
def Item.Leads (s : Site) (here : List String) (i : Item) : Prop :=
  ∀ a ∈ i.address?.toList, s.faultOf here a = none

/-- The item that leads from the page at `here` to the page at `there`, with its words and its
mark: its `href` is `Site.linkTo here there`. -/
def Item.toPage (here there : List String) (label : String) (current : Option String := none) :
    Item :=
  ⟨Site.linkTo here there, label, current⟩

/-- **An item written from a path of the site is no dead link**: where a page stands at
`there` and the names of `there` are plain, the item's link has no fault, from every page. -/
theorem Item.leads_toPage {s : Site} {there : List String} {page : Site.Page}
    (hat : s.at? there = some page) (hplain : there.all Site.plain = true) (here : List String)
    (label : String) (current : Option String) : (Item.toPage here there label current).Leads s here := by
  intro a ha
  have hfault := Site.faultOf_linkTo s hat hplain here (element := "a") "href" (by decide)
  unfold Item.address? Item.toPage at ha
  split at ha
  · exact nomatch ha
  · rw [List.mem_singleton.mp ha]
    exact hfault

/-- **A list whose every item leads somewhere holds no address with a fault.** -/
theorem list_leads {s : Site} {here : List String} {items : List Item}
    (h : ∀ i ∈ items, i.Leads s here) (name : Region.Name) (className : Option String) :
    ∀ a ∈ hrefsAt .html (listRaw name items className), s.faultOf here a = none := by
  intro a ha
  rw [hrefsAt_listRaw] at ha
  obtain ⟨i, hi, hin⟩ := List.mem_flatMap.mp ha
  exact h i hi a hin

/-- The addresses of a trail's items are those of its crumbs: a mark is no part of one. -/
theorem trail_hrefs : ∀ crumbs : List (String × String),
    (Item.trail crumbs).map (·.href) = crumbs.map (·.1)
  | [] => rfl
  | [_] => rfl
  | crumb :: next :: rest => by
    rw [Item.trail, List.map_cons, trail_hrefs (next :: rest)]
    rfl

/-- **A trail whose every crumb leads somewhere holds no address with a fault.** -/
theorem trail_leads {s : Site} {here : List String} {crumbs : List (String × String)}
    (h : ∀ crumb ∈ crumbs, (⟨crumb.1, crumb.2, none⟩ : Item).Leads s here) (name : Region.Name)
    (className : Option String) :
    ∀ a ∈ hrefsAt .html (listRaw name (Item.trail crumbs) className), s.faultOf here a = none :=
  list_leads
    (fun i hi => by
      have hhref : i.href ∈ crumbs.map (·.1) := by
        rw [← trail_hrefs]
        exact List.mem_map_of_mem hi
      obtain ⟨crumb, hcrumb, hsame⟩ := List.mem_map.mp hhref
      have hleads := h crumb hcrumb
      unfold Item.Leads Item.address? at hleads ⊢
      rw [← hsame]
      exact hleads)
    name className

/-- **A pager whose links lead somewhere holds no address with a fault.** -/
theorem pager_leads {s : Site} {here : List String} {previous next : Option Item}
    (hprevious : ∀ i, previous = some i → i.Leads s here)
    (hnext : ∀ i, next = some i → i.Leads s here) (name : Region.Name) (words : String × String)
    (className wordClass : Option String) :
    ∀ a ∈ hrefsAt .html (pagerRaw name previous next words className wordClass),
      s.faultOf here a = none := by
  intro a ha
  rw [hrefsAt_pagerRaw] at ha
  obtain ⟨i, hi, hin⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp hi with hi | hi
  · exact hprevious i (Option.mem_toList.mp hi) a hin
  · exact hnext i (Option.mem_toList.mp hi) a hin

/-! ## One current page among distinct pages -/

/-- How a link from the page at `here` to the page at `there` is the current one: `page` when
it leads to the page itself, `true` when the page stands below `there`, and not otherwise. -/
def markFor (here there : List String) : Option String :=
  if there == here then some "page" else if there.isPrefixOf here then some "true" else none

/-- The item of a section: the link from the page at `here` to the page at `there`, marked as
the page when it is the page, and as current when the page stands below it. -/
def Item.toSection (here : List String) (target : List String × String) : Item :=
  Item.toPage here target.1 target.2 (markFor here target.1)

theorem isPage_toSection (here : List String) (target : List String × String) :
    (Item.toSection here target).isPage = (target.1 == here) := by
  unfold Item.toSection Item.toPage Item.isPage markFor
  cases hsame : target.1 == here with
  | true => rfl
  | false =>
    show ((if target.1.isPrefixOf here = true then some "true" else none) == some "page") = false
    split <;> rfl

/-- No section is the page where no target is the page's path. -/
theorem pagesFrom_toSection_of_not_mem (here : List String) :
    ∀ (targets : List (List String × String)) (index : Nat), here ∉ targets.map (·.1) →
      Item.pagesFrom index (targets.map (Item.toSection here)) = []
  | [], _, _ => rfl
  | target :: rest, index, h => by
    have hne : (target.1 == here) = false := by
      cases hsame : target.1 == here with
      | false => rfl
      | true => exact absurd (List.mem_map.mpr ⟨target, List.mem_cons_self, eq_of_beq hsame⟩) h
    rw [List.map_cons, Item.pagesFrom, isPage_toSection, hne,
      pagesFrom_toSection_of_not_mem here rest (index + 1)
        (fun hin => h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hin))]
    rfl

/-- **Among links to distinct paths, at most one is the current page.** -/
theorem pages_toSection_le (here : List String) :
    ∀ (targets : List (List String × String)) (index : Nat), (targets.map (·.1)).Nodup →
      (Item.pagesFrom index (targets.map (Item.toSection here))).length ≤ 1
  | [], _, _ => Nat.zero_le _
  | target :: rest, index, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.map_cons, Item.pagesFrom, isPage_toSection]
    cases hsame : target.1 == here with
    | false => exact pages_toSection_le here rest (index + 1) h.2
    | true =>
      rw [pagesFrom_toSection_of_not_mem here rest (index + 1) (eq_of_beq hsame ▸ h.1)]
      exact Nat.le_refl 1

/-- **The page's own section is marked**: where the page's path is a target, some item is the
current page. With `pages_toSection_le`, exactly one. -/
theorem pages_toSection_of_mem (here : List String) :
    ∀ (targets : List (List String × String)) (index : Nat), here ∈ targets.map (·.1) →
      Item.pagesFrom index (targets.map (Item.toSection here)) ≠ []
  | [], _, h => nomatch h
  | target :: rest, index, h => by
    rw [List.map_cons, Item.pagesFrom, isPage_toSection]
    cases hsame : target.1 == here with
    | true => exact List.cons_ne_nil _ _
    | false =>
      rw [List.map_cons] at h
      rcases List.mem_cons.mp h with hhead | htail
      · rw [← hhead, beq_self_eq_true] at hsame
        exact Bool.noConfusion hsame
      · exact pages_toSection_of_mem here rest (index + 1) htail

end Whatwg.Html.Nav
