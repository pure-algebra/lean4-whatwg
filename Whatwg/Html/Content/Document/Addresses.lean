import Whatwg.Html.Content.Document.Laws

/-!
# Whatwg.Html.Content.Document.Addresses

Owner: the addresses of a part of a document, node by node (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entry W6 of `docs/research/2026-10-12-whatwg-requests.md`).
`Whatwg/Html/Content/Document/Laws.lean` reads the identifiers and the references of an
element from its attributes and its children (`namesAt_element`, `linksAt_element`), so that a
builder can say what its tree defines and names. The check across a site
(`Whatwg/Html/Content/Site.lean`) reads a third part of the same facts: the addresses, every
`href` that is no reference to the document itself. This module is the same law for them.

- `hrefsAt ns node` is the addresses that a node holds, in tree order, without their paths, and
  `hrefsAllAt` the same for a list of nodes.
- `hrefsAt_element`: the addresses of an element are those of its attributes, then those of
  its children. `hrefsAt_text` and its two fellows: a leaf holds none.
- `addresses_eq_hrefsAt`: the addresses that the check of a site reads from a tree are these.
- `hrefsAt_htmlElement`, and with it `namesAt_htmlElement` and `linksAt_htmlElement`: the three
  laws of an element in the form a builder of HTML meets, for an element that is no `svg` and
  no `template`. For a name that is written out the two premises are `rfl`.

So a builder of a part says once which addresses the part holds, and a law about those
addresses (that each leads to a page of the site) is a law about every page that holds the
part: `Whatwg/Html/Node/Nav/Laws.lean` does this for a navigation.

What this module does not claim: where an address leads. That is `Site.resolve`.
-/

namespace Whatwg.Html.Content.Document

open Whatwg.Html (RawNode Walk)

/-- The addresses among some facts, without their paths. -/
def hrefsIn (facts : List (Placed Fact)) : List Address := facts.filterMap fun p => p.it.address?

/-- The addresses that a node holds where it stands in `ns`, in tree order. -/
def hrefsAt (ns : Ns) (node : RawNode) : List Address := hrefsIn (factsAt ns node)

/-- The addresses that a list of nodes holds. -/
def hrefsAllAt (ns : Ns) (nodes : List RawNode) : List Address := nodes.flatMap (hrefsAt ns)

theorem Fact.address?_under (offset : Nat) (reset : Bool) (fact : Fact) :
    (fact.under offset reset).address? = fact.address? := by
  cases fact <;> rfl

theorem hrefsIn_append (a b : List (Placed Fact)) : hrefsIn (a ++ b) = hrefsIn a ++ hrefsIn b :=
  List.filterMap_append

/-- A path is no part of an address. -/
theorem hrefsIn_map_under (index : Nat) (facts : List (Placed Fact)) :
    hrefsIn (facts.map (Placed.under index)) = hrefsIn facts := by
  rw [hrefsIn, hrefsIn, List.filterMap_map]
  rfl

/-- An ancestor's heading offset changes no address. -/
theorem hrefsIn_settle (ns : Ns) (attrs : List (String × String)) (facts : List (Placed Fact)) :
    hrefsIn (settle ns attrs facts) = hrefsIn facts := by
  cases ns with
  | svg => rfl
  | html =>
    rw [settle, hrefsIn, hrefsIn, List.filterMap_map]
    congr 1
    funext p
    exact Fact.address?_under _ _ p.it

/-- The addresses without their paths are the addresses at their paths, without the paths. -/
theorem hrefsIn_eq_map (facts : List (Placed Fact)) :
    hrefsIn facts = (addressesIn facts).map (·.it) := by
  rw [hrefsIn, addressesIn, List.map_filterMap]
  congr 1
  funext p
  rw [Placed.pick, Option.map_map]
  cases p.it.address? <;> rfl

/-- **The addresses that the check of a site reads from a tree** are those of its root. -/
theorem addresses_eq_hrefsAt (tree : RawNode) : (addresses tree).map (·.it) = hrefsAt .html tree :=
  (hrefsIn_eq_map (facts tree)).symm

/-- An address of a tree, as the check of a site meets it, is one of `hrefsAt`. -/
theorem mem_hrefsAt_of_mem_addresses {tree : RawNode} {a : Placed Address}
    (h : a ∈ addresses tree) : a.it ∈ hrefsAt .html tree := by
  rw [← addresses_eq_hrefsAt]
  exact List.mem_map.mpr ⟨a, h, rfl⟩

theorem filterMap_address?_map_ident (owner : Owner) : ∀ ids : List String,
    (ids.map fun id => Fact.ident id owner).filterMap Fact.address? = []
  | [] => rfl
  | id :: rest => by
    rw [List.map_cons, List.filterMap_cons_none (rfl : (Fact.ident id owner).address? = none),
      filterMap_address?_map_ident owner rest]

theorem filterMap_address?_map_ref : ∀ links : List Ref,
    (links.map Fact.ref).filterMap Fact.address? = []
  | [] => rfl
  | r :: rest => by
    rw [List.map_cons, List.filterMap_cons_none (rfl : (Fact.ref r).address? = none),
      filterMap_address?_map_ref rest]

theorem filterMap_address?_map_address : ∀ addresses : List Address,
    (addresses.map Fact.address).filterMap Fact.address? = addresses
  | [] => rfl
  | a :: rest => by
    rw [List.map_cons, List.filterMap_cons_some (rfl : (Fact.address a).address? = some a),
      filterMap_address?_map_address rest]

theorem filterMap_address?_markFacts (element : String) (attrs : List (String × String)) :
    (markFacts element attrs).filterMap Fact.address? = [] := by
  unfold markFacts
  split <;> split <;> split <;> rfl

/-- The addresses among an element's own facts are those of its attributes. -/
theorem filterMap_address?_ownFacts (ns : Ns) (element : String) (attrs : List (String × String)) :
    (ownFacts ns element attrs).filterMap Fact.address? = attrs.flatMap (addressesOf ns element) := by
  have hattrs : ∀ (all list : List (String × String)),
      (list.flatMap (attrFacts ns element all)).filterMap Fact.address? =
        list.flatMap (addressesOf ns element) := by
    intro all list
    induction list with
    | nil => rfl
    | cons attr rest ih =>
      rw [List.flatMap_cons, List.filterMap_append, attrFacts, List.filterMap_append,
        List.filterMap_append, filterMap_address?_map_ident, filterMap_address?_map_ref,
        filterMap_address?_map_address, List.nil_append, List.nil_append, ih, List.flatMap_cons]
  unfold ownFacts
  rw [List.filterMap_append, hattrs]
  cases ns with
  | html => rw [filterMap_address?_markFacts, List.append_nil]
  | svg => exact List.append_nil _

theorem hrefsIn_here (own : List Fact) :
    hrefsIn (own.map fun fact => (⟨[], fact⟩ : Placed Fact)) = own.filterMap Fact.address? := by
  rw [hrefsIn, List.filterMap_map]
  rfl

theorem hrefsAllAt_nil (ns : Ns) : hrefsAllAt ns [] = [] := rfl

theorem hrefsAllAt_cons (ns : Ns) (node : RawNode) (rest : List RawNode) :
    hrefsAllAt ns (node :: rest) = hrefsAt ns node ++ hrefsAllAt ns rest := by
  rw [hrefsAllAt, List.flatMap_cons]
  rfl

/-- The addresses of two lists of nodes in a row are those of each, in a row. -/
theorem hrefsAllAt_append (ns : Ns) (as bs : List RawNode) :
    hrefsAllAt ns (as ++ bs) = hrefsAllAt ns as ++ hrefsAllAt ns bs := by
  rw [hrefsAllAt, List.flatMap_append]
  rfl

/-- The addresses of a list of children do not read the index of the first. -/
theorem hrefsIn_factsAllAt (ns : Ns) : ∀ (index : Nat) (nodes : List RawNode),
    hrefsIn (factsAllAt ns index nodes) = hrefsAllAt ns nodes
  | _, [] => by
    rw [factsAllAt_nil]
    rfl
  | index, node :: rest => by
    rw [factsAllAt_cons, hrefsIn_append, hrefsIn_map_under, hrefsIn_factsAllAt ns (index + 1) rest,
      hrefsAllAt_cons, hrefsAt]

/-- **The addresses of an element** are those of its attributes, read in the element's own
namespace, then those of its children. A `template` gives only its own. -/
theorem hrefsAt_element (ns : Ns) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    hrefsAt ns (.element name attrs children) =
      attrs.flatMap (addressesOf (ns.ofElement name) name) ++
        if holdsOtherTree (ns.ofElement name) name then []
        else hrefsAllAt (ns.step name) children := by
  rw [hrefsAt, factsAt_element, hrefsIn_settle, hrefsIn_append, hrefsIn_here,
    filterMap_address?_ownFacts]
  split
  · rfl
  · rw [hrefsIn_factsAllAt]

/-- The same for an HTML element among HTML elements that is no `svg` and no `template`: the
form a builder of HTML meets. For a name that is written out, both premises are `rfl`. -/
theorem hrefsAt_htmlElement {name : String} (hstep : Ns.step .html name = .html)
    (htree : holdsOtherTree .html name = false) (attrs : List (String × String))
    (children : List RawNode) :
    hrefsAt .html (.element name attrs children) =
      attrs.flatMap (htmlAddresses name) ++ hrefsAllAt .html children := by
  have hof : Ns.ofElement .html name = .html := hstep
  rw [hrefsAt_element, hof, htree, hstep]
  rfl

/-- The identifiers of an HTML element among HTML elements that is no `svg` and no `template`:
`namesAt_element` in the form a builder of HTML meets. -/
theorem namesAt_htmlElement {name : String} (hstep : Ns.step .html name = .html)
    (htree : holdsOtherTree .html name = false) (attrs : List (String × String))
    (children : List RawNode) :
    namesAt .html (.element name attrs children) =
      attrs.filterMap identOf? ++ namesAllAt .html children := by
  have hof : Ns.ofElement .html name = .html := hstep
  rw [namesAt_element, hof, htree, hstep]
  rfl

/-- The references of such an element: `linksAt_element` in the same form. -/
theorem linksAt_htmlElement {name : String} (hstep : Ns.step .html name = .html)
    (htree : holdsOtherTree .html name = false) (attrs : List (String × String))
    (children : List RawNode) :
    linksAt .html (.element name attrs children) =
      attrs.flatMap (htmlLinks name) ++ linksAllAt .html children := by
  have hof : Ns.ofElement .html name = .html := hstep
  rw [linksAt_element, hof, htree, hstep]
  rfl

theorem hrefsAt_text (ns : Ns) (content : String) : hrefsAt ns (.text content) = [] := by
  rw [hrefsAt, factsAt_text]
  rfl

theorem hrefsAt_entity (ns : Ns) (name : String) : hrefsAt ns (.entity name) = [] := by
  rw [hrefsAt, factsAt_entity]
  rfl

theorem hrefsAt_comment (ns : Ns) (content : String) : hrefsAt ns (.comment content) = [] := by
  rw [hrefsAt, factsAt_comment]
  rfl

end Whatwg.Html.Content.Document
