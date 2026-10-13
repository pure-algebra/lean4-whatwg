import Whatwg.Html.Node.Outline
import Whatwg.Html.Content.Document.Addresses

/-!
# Whatwg.Html.Node.Outline.Laws

Owner: the laws of the contents list of `Whatwg/Html/Node/Outline.lean`.

- **Which references the list makes.** `linksAt_contentsRaw`: the references of the list are
  those of its title's line, then one for each identifier of the outline, in the order of the
  page: what the writer of fragments makes of the identifier (`refsOf`). With the default
  writer that is the identifier itself (`refsOf_plainHref`). `namesAt_contentsRaw`: the list
  defines the identifier of its title's line, and no other.
- **The list is closed against a page that has the parts.** `contents_closed`: every reference
  of the list names one of `names`, when `names` holds the identifiers of the outline and the
  title's own, and the writer of fragments is read back (`ReadsBack`). With
  `names := Content.Document.names page`, this is the part of `Document.Sound.closed` that the
  list owes: a page that holds the parts has no dangling link from its contents.
- `tokens_of_idOk`: a well-formed identifier is one token, so a title's line that is named by
  `aria-labelledby` is named once.

What the laws do not say: that the identifiers of an outline differ from each other. That is
the page's (`Document.Sound.distinct`), and an outline with one identifier twice gives a list
with two links to the first of them.
-/

namespace Whatwg.Html.Outline

open Whatwg.Html.Content
open Whatwg.Html.Content.Document (Ref linksAt linksAllAt namesAt namesAllAt)

/-! ## One identifier, one token -/

/-- A run of characters with no white space is one token, after the characters already
read. -/
theorem tokensFrom_word : ∀ (cs word : List Char), (∀ c ∈ cs, Document.isSpace c = false) →
    word ++ cs ≠ [] → Document.tokensFrom word cs = [String.ofList (word.reverse ++ cs)]
  | [], word, _, hne => by
    rw [List.append_nil] at hne
    rw [Document.tokensFrom, List.append_nil]
    cases word with
    | nil => exact absurd rfl hne
    | cons c rest => rfl
  | c :: cs, word, h, _ => by
    rw [Document.tokensFrom, if_neg (ne_true_of_eq_false (h c List.mem_cons_self)),
      tokensFrom_word cs (c :: word) (fun d hd => h d (List.mem_cons_of_mem c hd))
        (List.cons_ne_nil _ _),
      List.reverse_cons, List.append_assoc]
    rfl

/-- **A well-formed identifier is one token.** -/
theorem tokens_of_idOk {id : String} (h : Document.idOk id = true) : Document.tokens id = [id] := by
  unfold Document.idOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
  rw [Document.tokens, tokensFrom_word id.toList [] h.2 (by rw [List.nil_append]; exact h.1)]
  show [String.ofList id.toList] = [id]
  rw [String.ofList_toList]

/-! ## The references of the list -/

/-- The references of a link to the part `id`, as the writer of fragments `href` writes it: a
fragment, when what it writes is `#` and a target. -/
def refsOf (href : String → String) (id : String) : List Ref :=
  (Document.fragmentOf? (href id)).toList.map fun target => ⟨"a", "href", .fragment, target⟩

/-- The default writer's link names the identifier itself. -/
theorem refsOf_plainHref (id : String) : refsOf plainHref id = [⟨"a", "href", .fragment, id⟩] := by
  unfold refsOf plainHref
  rw [Document.fragmentOf?_hash]
  rfl

/-- The references of a title: one for each token of the identifier of its line. -/
def Title.refs : Title → List Ref
  | .hidden _ => []
  | .shown id _ _ => (Document.tokens id).map fun token => ⟨"nav", "aria-labelledby", .aria, token⟩

/-- The identifiers that a title defines: that of its line. -/
def Title.ids : Title → List String
  | .hidden _ => []
  | .shown id _ _ => [id]

theorem linksAt_link (href : String → String) (id title : String) :
    linksAt .html (.element "a" [("href", href id)] [.text title]) = refsOf href id := by
  rw [Document.linksAt_htmlElement rfl rfl, Document.linksAllAt_cons, Document.linksAt_text]
  show (Document.htmlLinks "a" ("href", href id) ++ []) ++ ([] ++ Document.linksAllAt .html []) = _
  rw [List.append_nil]
  exact List.append_nil _

theorem namesAt_link (href : String → String) (id title : String) :
    namesAt .html (.element "a" [("href", href id)] [.text title]) = [] := by
  rw [Document.namesAt_htmlElement rfl rfl, Document.namesAllAt_cons, Document.namesAt_text]
  rfl

mutual

/-- The references of the item of a part: the link to it, then those of its parts. -/
theorem Entry.linksAt_raw (href : String → String) :
    ∀ entry : Entry, linksAt .html (entry.raw href) = entry.ids.flatMap (refsOf href)
  | .mk id title parts => by
    have hbelow := linksAllAt_rawAll href parts
    rw [Entry.raw, Entry.ids, Document.linksAt_htmlElement rfl rfl, Document.linksAllAt_cons,
      linksAt_link, List.flatMap_cons]
    cases parts with
    | nil => rfl
    | cons first rest =>
      show [] ++ (refsOf href id ++
        Document.linksAllAt .html [.element "ol" [] (rawAll href (first :: rest))]) = _
      rw [Document.linksAllAt_cons, Document.linksAt_htmlElement rfl rfl, hbelow, List.nil_append]
      show refsOf href id ++ (([] ++ _) ++ Document.linksAllAt .html []) = _
      rw [List.nil_append]
      exact congrArg _ (List.append_nil _)

/-- The references of the items of an outline: one link for each identifier, in order. -/
theorem linksAllAt_rawAll (href : String → String) :
    ∀ entries : List Entry, linksAllAt .html (rawAll href entries) = (ids entries).flatMap (refsOf href)
  | [] => by
    rw [rawAll, ids]
    rfl
  | entry :: rest => by
    rw [rawAll, ids, Document.linksAllAt_cons, Entry.linksAt_raw href entry,
      linksAllAt_rawAll href rest, List.flatMap_append]

end

mutual

/-- The item of a part defines no identifier. -/
theorem Entry.namesAt_raw (href : String → String) :
    ∀ entry : Entry, namesAt .html (entry.raw href) = []
  | .mk id title parts => by
    have hbelow := namesAllAt_rawAll href parts
    rw [Entry.raw, Document.namesAt_htmlElement rfl rfl, Document.namesAllAt_cons, namesAt_link]
    cases parts with
    | nil => rfl
    | cons first rest =>
      show [] ++ ([] ++ Document.namesAllAt .html [.element "ol" [] (rawAll href (first :: rest))]) = []
      rw [Document.namesAllAt_cons, Document.namesAt_htmlElement rfl rfl, hbelow]
      rfl

theorem namesAllAt_rawAll (href : String → String) :
    ∀ entries : List Entry, namesAllAt .html (rawAll href entries) = []
  | [] => by
    rw [rawAll]
    rfl
  | entry :: rest => by
    rw [rawAll, Document.namesAllAt_cons, Entry.namesAt_raw href entry, namesAllAt_rawAll href rest]
    rfl

end

/-- The attributes of the `nav` make the title's references. -/
theorem flatMap_nav_links (title : Title) (className : Option String) :
    (rawAttrs (Nav.attrs title.name className)).flatMap (Document.htmlLinks "nav") = title.refs := by
  cases title <;> cases className <;>
    simp only [Title.name, Title.refs, Nav.attrs, Region.Name.attr, Region.classAttr, A.opt,
      rawAttrs, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] <;>
    rfl

/-- The title's line makes no reference, and defines its identifier. -/
theorem linksAllAt_lineRaw (title : Title) : linksAllAt .html title.lineRaw = [] := by
  cases title with
  | hidden words => rfl
  | shown id words className =>
    rw [Title.lineRaw, Document.linksAllAt_cons, Document.linksAt_htmlElement rfl rfl,
      Document.linksAllAt_cons, Document.linksAt_text]
    cases className <;> rfl

theorem namesAllAt_lineRaw (title : Title) : namesAllAt .html title.lineRaw = title.ids := by
  cases title with
  | hidden words => rfl
  | shown id words className =>
    rw [Title.lineRaw, Document.namesAllAt_cons, Document.namesAt_htmlElement rfl rfl,
      Document.namesAllAt_cons, Document.namesAt_text]
    cases className <;> rfl

/-- **The references of the contents list**: those of its title, then one link for each
identifier of the outline, in the order of the page. -/
theorem linksAt_contentsRaw (title : Title) (entries : List Entry) (href : String → String)
    (className : Option String) :
    linksAt .html (contentsRaw title entries href className) =
      title.refs ++ (ids entries).flatMap (refsOf href) := by
  rw [contentsRaw, Document.linksAt_htmlElement rfl rfl, flatMap_nav_links,
    Document.linksAllAt_append, linksAllAt_lineRaw, Document.linksAllAt_cons,
    Document.linksAt_htmlElement rfl rfl, linksAllAt_rawAll, List.nil_append]
  show title.refs ++ (([] ++ _) ++ Document.linksAllAt .html []) = _
  rw [List.nil_append]
  exact congrArg _ (List.append_nil _)

/-- With the default writer, each link names its identifier as it is. -/
theorem linksAt_contentsRaw_plain (title : Title) (entries : List Entry)
    (className : Option String) :
    linksAt .html (contentsRaw title entries plainHref className) =
      title.refs ++ (ids entries).map fun id => ⟨"a", "href", .fragment, id⟩ := by
  rw [linksAt_contentsRaw]
  congr 1
  induction ids entries with
  | nil => rfl
  | cons id rest ih => rw [List.flatMap_cons, refsOf_plainHref, ih, List.map_cons]; rfl

/-- **The identifiers of the contents list**: that of its title's line, and no other. -/
theorem namesAt_contentsRaw (title : Title) (entries : List Entry) (href : String → String)
    (className : Option String) :
    namesAt .html (contentsRaw title entries href className) = title.ids := by
  have hattrs : (rawAttrs (Nav.attrs title.name className)).filterMap Document.identOf? = [] := by
    cases title <;> cases className <;> rfl
  rw [contentsRaw, Document.namesAt_htmlElement rfl rfl, hattrs, Document.namesAllAt_append,
    namesAllAt_lineRaw, Document.namesAllAt_cons, Document.namesAt_htmlElement rfl rfl,
    namesAllAt_rawAll, List.nil_append]
  exact List.append_nil _

/-! ## Closed against a page that has the parts -/

/-- A writer of fragments is read back: what it writes for an identifier is a fragment that
names that identifier, as a document's own fragment is found. -/
def ReadsBack (href : String → String) : Prop := ∀ id, ∀ r ∈ refsOf href id, r.NamesIn [id]

/-- The default writer is read back: the identifier is found as written. -/
theorem readsBack_plainHref : ReadsBack plainHref := by
  intro id r hr
  rw [refsOf_plainHref, List.mem_singleton] at hr
  rw [hr]
  exact Or.inl List.mem_cons_self

/-- **The contents list is closed against a page that has the parts**: every reference it
makes names one of `names`, when `names` holds the identifiers of the outline and what the
title's line is named by, and the writer of fragments is read back. -/
theorem contents_closed (title : Title) (entries : List Entry) {href : String → String}
    (hback : ReadsBack href) (className : Option String) {names : List String}
    (htitle : ∀ r ∈ title.refs, r.target ∈ names) (hparts : ∀ id ∈ ids entries, id ∈ names) :
    ∀ r ∈ linksAt .html (contentsRaw title entries href className), r.NamesIn names := by
  intro r hr
  rw [linksAt_contentsRaw] at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact Or.inl (htitle r hr)
  · obtain ⟨id, hid, hin⟩ := List.mem_flatMap.mp hr
    exact (hback id r hin).mono fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact hparts id hid

/-- A title whose line has a well-formed identifier is named by that line and nothing else:
its one reference names the identifier that the list itself defines. -/
theorem title_refs_of_idOk {title : Title} (h : ∀ id ∈ title.ids, Document.idOk id = true) :
    ∀ r ∈ title.refs, r.target ∈ title.ids := by
  cases title with
  | hidden words => exact fun _ hr => nomatch hr
  | shown id words className =>
    intro r hr
    rw [Title.refs, tokens_of_idOk (h id List.mem_cons_self), List.map_cons, List.map_nil,
      List.mem_singleton] at hr
    rw [hr]
    exact List.mem_cons_self

end Whatwg.Html.Outline
