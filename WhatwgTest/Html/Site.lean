import Whatwg.Html.Content.Site.Laws

/-!
# WhatwgTest.Html.Site

The documentation site of lean4-effect4 on the check across a site
(`Whatwg/Html/Content/Site.lean`; entries W6 and W13 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer is read at the checkout beside
this repository: `tools/Tools/Document.lean` (`Algebra`, its monoid fold `Algebra.collect`,
`Document.check`), `tools/Tools/Site.lean` (`Page`, `Site`, `linkTo`, `slug`, `split`, `keys`,
`keyIndex`, `target`, `resolve`, `links`, `Site.check`, `contents`, the shell),
`tools/Drivers/Site.lean` (how the site is put together) and `Test/Audit/SiteControls.lean`
(its controls). This module imports nothing of that package. It restates the value and the
folds under the consumer's names, on a document cut down to a paragraph, a list and a part.
The shell is the consumer's, element for element, written as a raw tree: the consumer writes
it in `html!`.

What it shows:

- **Each refusal of the consumer's `Site.check` is given by the package's check, with the same
  link named.** For each control of `SiteControls.lean` the consumer's check is run as ported,
  and gives the consumer's words; the package's check is run on the pages as written, and
  names the same page and the same link. Where the two differ the guards say how: the
  package reads the tree a browser gets, so it also reads the shell's own links, and it knows
  nothing of a key's space.
- **More than the consumer checks today.** A link into a page with a fragment that page does
  not have; a stylesheet the site does not hold; a `base` element.
- **The reading of a reference**, on the cases of the URL Standard's path state.
- **The laws at this site.** `check?` answers a checked site for the consumer's; `Checked.add?`
  adds a page to it by reading that page alone, and refuses a page with a dead link, a taken
  path or no page above it. `plain_sound` proves a site written out plainly sound by
  evaluation, and `plain_grows` is `Site.Sound.add` at it.
- **A site of the consumer's size**: 33 pages, as its driver makes them from a report of 16
  parts, 241 claims and 14 requirements.

What this battery does not claim: that the pages are those lean4-effect4 writes. No theorem
relates this port to that package. The guards are finite evaluations.
-/

namespace WhatwgTest.Html.Site

open Whatwg.Html

/-! ## The consumer's document, as it has it (`Tools.Document`) -/

/-- `Tools.Document.Inline`, without the code and the status. -/
inductive Inline where
  | text (s : String)
  | ref (key label : String)
  | link (href label : String)

/-- `Tools.Document.Line`. -/
abbrev Line := List Inline

/-- `Tools.Document.Block`, cut down to a paragraph, a list and a part. -/
inductive Block where
  | para (line : Line)
  | items (lines : List Line)
  | part (key title : String) (body : List Block)

/-- `Tools.Document.Document`, without its producer. -/
structure Document where
  title : String
  body : List Block

/-- `Tools.Document.Algebra`: one field for each constructor. -/
structure Algebra (α : Type) where
  para : Line → α
  items : List Line → α
  part : String → String → List α → α

mutual

/-- `Tools.Document.Block.fold`. -/
def Block.fold {α : Type} (a : Algebra α) : Block → α
  | .para l => a.para l
  | .items ls => a.items ls
  | .part k t body => a.part k t (Block.foldList a body)
termination_by structural b => b

/-- `Tools.Document.Block.foldList`. -/
def Block.foldList {α : Type} (a : Algebra α) : List Block → List α
  | [] => []
  | b :: bs => b.fold a :: Block.foldList a bs
termination_by structural bs => bs

end

/-- `Tools.Document.Algebra.collect`, the consumer's monoid fold: each line mapped and joined,
and at a part its body's results combined. -/
def Algebra.collect {β : Type} (line : Line → List β)
    (part : String → String → List β → List β := fun _ _ body => body) : Algebra (List β) where
  para l := line l
  items ls := ls.flatMap line
  part k t body := part k t body.flatten

/-- `Tools.Document.Block.collect`. -/
def Block.collect {β : Type} (a : Algebra (List β)) (bs : List Block) : List β :=
  (Block.foldList a bs).flatten

/-- `Tools.Document.Finding`, without the malformed block. -/
inductive Finding where
  | key (k : String)
  | ref (k : String)
  | link (href : String)

/-- The census of `Tools.Document`: the lines' references and links, and the parts' keys. -/
def census : Algebra (List Finding) :=
  Algebra.collect
    (fun l => l.filterMap fun
      | .ref k _ => some (.ref k)
      | .link h _ => some (.link h)
      | _ => none)
    (fun k _ body => .key k :: body)

/-- `Tools.Document.Document.check`: a blank or duplicate key, a reference to no part, a blank
link, each by name. A reference may name a key that `outside` holds. -/
def Document.check (d : Document) (outside : String → Bool := fun _ => false) : List String :=
  Id.run do
    let fs := Block.collect census d.body
    let mut errors : List String := []
    let mut seen : Std.HashSet String := {}
    for f in fs do
      if let .key k := f then
        if k.isEmpty || k.toList.any Char.isWhitespace then
          errors := errors ++ [s!"key {k.quote}: blank or with a space"]
        if seen.contains k then errors := errors ++ [s!"key {k}: duplicate"]
        seen := seen.insert k
    for f in fs do
      match f with
      | .ref r =>
        unless seen.contains r || outside r do
          errors := errors ++ [s!"reference {r}: no part has this key"]
      | .link h =>
        if h.isEmpty || h.toList.any Char.isWhitespace then
          errors := errors ++ [s!"link {h.quote}: blank or with a space"]
      | _ => pure ()
    return errors

/-! ## The consumer's site, as it has it (`Tools.Site`) -/

/-- `Tools.Site.Page`: a folder path, a document, the space its references resolve in, and the
key of the part it was split from. -/
structure Page where
  path : List String
  doc : Document
  space : String := ""
  key : Option String := none

/-- `Tools.Site.Site`: the pages in reading order, and the other files by their paths. -/
structure Site where
  pages : List Page
  files : List String := []

/-- `Tools.Site.folders`. -/
def folders (path : List String) : String := String.join (path.map (· ++ "/"))

/-- `Tools.Site.up`. -/
def up (path : List String) : String := String.join (path.map fun _ => "../")

/-- `Tools.Site.linkTo`: the shortest relative path from one page to another. -/
def linkTo (here there : List String) : String :=
  let common := (here.zip there).takeWhile (fun (a, b) => a == b) |>.length
  let s := up (here.drop common) ++ folders (there.drop common)
  if s.isEmpty then "./" else s

/-- `Tools.Site.slug`: a key as a folder. -/
def slug (key : String) : String :=
  String.ofList ((((key.splitOn ":").getLast?.getD key).toList).map fun c =>
    let c := c.toLower
    if c.isAlphanum || c == '-' then c else '-')

/-- `gather` of `Tools.Site`: consecutive links as one list. -/
def gather : List (Sum Block Line) → List Block
  | [] => []
  | .inl b :: rest => b :: gather rest
  | .inr l :: rest =>
    match gather rest with
    | .items ls :: more => .items (l :: ls) :: more
    | more => .items [l] :: more

mutual

/-- `splitBlock` of `Tools.Site`: a block kept, or a part made a page, with the pages below. -/
def splitBlock (cut : List String → String → Bool) (path : List String) (space : String) :
    Block → List (Sum Block Line) × List Page
  | .part k t body =>
    if cut path k then
      let here := path ++ [slug k]
      let (kept, pages) := splitBlocks cut here space body
      let summary : Line :=
        match body with
        | .para l :: _ => .text ": " :: l
        | _ => []
      ([.inr (.link (slug k ++ "/") t :: summary)],
        { path := here, space, key := some k, doc := { title := t, body := gather kept } } :: pages)
    else ([.inl (.part k t body)], [])
  | b => ([.inl b], [])
termination_by structural b => b

/-- `splitBlocks` of `Tools.Site`. -/
def splitBlocks (cut : List String → String → Bool) (path : List String) (space : String) :
    List Block → List (Sum Block Line) × List Page
  | [] => ([], [])
  | b :: bs =>
    let (k1, p1) := splitBlock cut path space b
    let (k2, p2) := splitBlocks cut path space bs
    (k1 ++ k2, p1 ++ p2)
termination_by structural bs => bs

end

/-- `Tools.Site.split`: a document as pages, each part that `cut` names one folder down. -/
def split (cut : List String → String → Bool) (path : List String) (space : String)
    (d : Document) : List Page :=
  let (kept, pages) := splitBlocks cut path space d.body
  { path, space, doc := { d with body := gather kept } } :: pages

/-- `Tools.Site.parts`: a page's parts and their sub-parts, a monoid fold that reads no line. -/
def parts (d : Document) : List (String × String × List (String × String)) :=
  Block.collect (Algebra.collect (fun _ => [])
    fun k t sub => [(k, t, sub.map fun (k', t', _) => (k', t'))]) d.body

/-- `Tools.Site.keys`: every key of a page, at every depth. -/
def keys (d : Document) : List String :=
  Block.collect (Algebra.collect (fun _ => []) (fun k _ body => k :: body)) d.body

/-- `Tools.Site.links`: the links of a page's document, a monoid fold of its lines. -/
def links (d : Document) : List String :=
  Block.collect (Algebra.collect fun l => l.filterMap fun
    | .link h _ => some h
    | _ => none) d.body

/-- `Tools.Site.keyIndex`: the page that each key names in each space, and whether the key is
the page's own. -/
def keyIndex (s : Site) : Std.HashMap (String × String) (List String × Bool) :=
  s.pages.foldl (init := {}) fun m p =>
    let m :=
      match p.key with
      | some k => m.insert (p.space, k) (p.path, true)
      | none => m
    (keys p.doc).foldl (fun m k => m.insert (p.space, k) (p.path, false)) m

/-- `Tools.Document.Html.fragment`: a key as a fragment, percent-encoded. -/
def fragment (key : String) : String :=
  "#" ++ String.join (key.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && (c.isAlphanum || "-._~:@!$'()*+,;=/?".toList.contains c) then c.toString
    else
      let digits := String.ofList (Nat.toDigits 16 b.toNat)
      "%" ++ (if digits.length == 1 then "0" ++ digits else digits).toUpper)

/-- `Tools.Site.target`: the link of a reference from a page. A key no page holds falls back to
a fragment. -/
def target (ix : Std.HashMap (String × String) (List String × Bool)) (p : Page) (k : String) :
    String :=
  match ix[(p.space, k)]? with
  | some (path, true) => linkTo p.path path
  | some (path, false) =>
    if path == p.path then fragment k else linkTo p.path path ++ fragment k
  | none => fragment k

/-- `Tools.Site.Site.at?`. -/
def Site.at? (s : Site) (path : List String) : Option Page := s.pages.find? (·.path == path)

/-- `Tools.Site.Site.sections`: the pages one folder below the root. -/
def Site.sections (s : Site) : List Page := s.pages.filter (·.path.length == 1)

/-- `Tools.Site.Site.around`: the previous and the next page in reading order. -/
def Site.around (s : Site) (p : Page) : Option Page × Option Page :=
  let i := s.pages.findIdx (·.path == p.path)
  ((if i == 0 then none else s.pages[i - 1]?), s.pages[i + 1]?)

/-- `Tools.Site.resolve`: a link's path from the root and whether it names a folder; none for a
link off the site. -/
def resolve (here : List String) (href : String) : Option (List String × Bool) :=
  let href := (href.splitOn "#").head!
  if href.startsWith "https://" || href.startsWith "http://" || href.startsWith "mailto:" then none
  else
    let (start, rest) :=
      if href.startsWith "/" then ([], String.ofList (href.toList.drop 1)) else (here, href)
    let segs := (rest.splitOn "/").foldl (fun acc seg =>
      match seg with
      | "." | "" => acc
      | ".." => acc.dropLast
      | _ => acc ++ [seg]) start
    some (segs, rest.isEmpty || rest.endsWith "/")

/-- `Tools.Site.Site.check`, the consumer's check: a repeated path, a page with no parent, a
page's own check, a key twice in one space, and a relative link to no page or file. -/
def Site.check (s : Site) : List String := Id.run do
  let mut errors : Array String := #[]
  let paths := s.pages.map (·.path)
  if !paths.contains [] then errors := errors.push "no page at the root"
  for p in s.pages do
    let place := "/" ++ folders p.path
    if (paths.filter (· == p.path)).length > 1 then
      errors := errors.push s!"{place}: two pages at this path"
    if !p.path.isEmpty && !paths.contains p.path.dropLast then
      errors := errors.push s!"{place}: no page above it"
  let ix := keyIndex s
  for p in s.pages do
    errors := errors ++
      ((p.doc.check (fun k => ix.contains (p.space, k))).map (s!"/{folders p.path}: " ++ ·)).toArray
  let mut seen : Std.HashSet (String × String) := {}
  for p in s.pages do
    for k in p.key.toList ++ keys p.doc do
      if seen.contains (p.space, k) then
        errors := errors.push s!"/{folders p.path}: key {k} twice in space {p.space.quote}"
      seen := seen.insert (p.space, k)
  let pageFiles := s.pages.map fun p => p.path ++ ["document.json"]
  for p in s.pages do
    for h in links p.doc do
      match resolve p.path h with
      | none => pure ()
      | some (r, folder) =>
        let ok :=
          if folder then paths.contains r
          else pageFiles.contains r || s.files.contains ("/".intercalate r)
        unless ok do
          errors := errors.push s!"/{folders p.path}: link {h}: no page or file of the site"
  return errors.toList

/-- `Tools.Site.contents`: every page under each section. -/
def contents (s : Site) : Document where
  title := "Contents"
  body := [.para [.text "Every page of the site, by section."]] ++
    s.sections.map fun sec =>
      .part (slug (String.join sec.path)) sec.doc.title
        [.items ((s.pages.filter fun q => sec.path.isPrefixOf q.path).map fun q =>
          [Inline.link (linkTo ["contents"] q.path) q.doc.title])]

/-- The site as `tools/Drivers/Site.lean` puts it together: the pages, then the contents page,
and the files the driver writes beside them. -/
def assemble (pages : List Page) : Site :=
  let files := ["page.css", "looks.css", "site.json", "_headers", "404.html"]
  let draft : Site := { pages, files }
  { draft with pages := pages ++ [{ path := ["contents"], doc := contents draft, space := "contents" }] }

/-! ## The pages as written -/

/-- An element by its name, its children, then its attributes (`el` of the consumer). -/
def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- `Tools.Document.Html.inline`, with a reference's link from `target`. -/
def inline (target : String → String) : Inline → RawNode
  | .text s => .text s
  | .ref k label => el "a" [.text label] [("href", target k)]
  | .link href label => el "a" [.text label] [("href", href)]

/-- `Tools.Document.Html.algebra`: a part is a `section` whose `id` is its key, with a heading
by its depth and a link to itself. -/
def htmlAlgebra (target : String → String) : Algebra (Nat → List RawNode) where
  para l _ := [el "p" (l.map (inline target))]
  items ls _ := [el "ul" (ls.map fun l => el "li" (l.map (inline target)))]
  part k t body depth :=
    let heading := el ("h" ++ toString (min 6 depth))
      [.text t, el "a" [.text "#"]
        [("class", "self"), ("href", fragment k), ("aria-label", "Link to " ++ t)]]
    [el "section" (heading :: body.flatMap (· (depth + 1))) [("id", k)]]

/-- A link of the shell's navigation, marked when it is the current one. -/
def navLink (href label : String) (current : Option String) : RawNode :=
  el "li" [el "a" [.text label]
    ([("href", href)] ++ (current.map fun how => ("aria-current", how)).toList)]

/-- `Tools.Site.Site.shell` and `render`, as one raw tree: the head with the two style files,
the link past the header, the header with the link home and the sections, the parts of the
page, the breadcrumbs, the title, the document's blocks, the neighbouring pages, and the footer
with the page as data and the contents page. Every link is relative to the page's folder. -/
def pageTree (s : Site) (ix : Std.HashMap (String × String) (List String × Bool)) (p : Page) :
    RawNode :=
  let href (q : List String) := linkTo p.path q
  let (prev, next) := s.around p
  let sections := s.sections.map fun q =>
    navLink (href q.path) q.doc.title
      (if q.path == p.path then some "page" else if q.path.isPrefixOf p.path then some "true" else none)
  let crumbs := if p.path.length < 2 then [] else
    (List.range p.path.length).filterMap fun k =>
      (s.at? (p.path.take (k + 1))).map fun q =>
        navLink (href q.path) q.doc.title (if k + 1 == p.path.length then some "page" else none)
  let toc := (parts p.doc).map fun (k, t, sub) =>
    el "li" ([el "a" [.text t] [("href", fragment k)]] ++
      if sub.isEmpty then [] else
        [el "ol" (sub.map fun (k, t) => el "li" [el "a" [.text t] [("href", fragment k)]])])
  let pager :=
    (prev.map fun q => el "a" [el "span" [.text "Previous"] [("class", "label")], .text q.doc.title]
      [("rel", "prev"), ("href", href q.path)]).toList ++
    (next.map fun q => el "a" [el "span" [.text "Next"] [("class", "label")], .text q.doc.title]
      [("rel", "next"), ("href", href q.path)]).toList
  el "html" [
    el "head" [el "meta" [] [("charset", "utf-8")], el "title" [.text p.doc.title],
      el "link" [] [("rel", "stylesheet"), ("href", up p.path ++ "looks.css")],
      el "link" [] [("rel", "stylesheet"), ("href", up p.path ++ "page.css")]],
    el "body" (
      [el "a" [.text "Skip to the content"] [("class", "skip"), ("href", "#content")],
       el "header" ([el "a" [.text "Effect4"] [("class", "home"), ("href", href [])]] ++
        if sections.isEmpty then [] else [el "nav" [el "ol" sections] [("aria-label", "Site")]])] ++
      (if toc.isEmpty then [] else
        [el "nav" [el "p" [.text "On this page"] [("id", "toc-label"), ("class", "label")], el "ol" toc]
          [("class", "toc"), ("aria-labelledby", "toc-label")]]) ++
      [el "main" (
          (if crumbs.isEmpty then [] else
            [el "nav" [el "ol" crumbs] [("class", "crumbs"), ("aria-label", "Breadcrumb")]]) ++
          [el "h1" [.text p.doc.title]] ++
          (Block.foldList (htmlAlgebra (target ix p)) p.doc.body).flatMap (· 2) ++
          (if pager.isEmpty then [] else [el "nav" pager [("class", "pager"), ("aria-label", "Pages")]]))
          [("id", "content")],
       el "footer" [el "p" [.text "Provenance"] [("class", "label")],
        el "ul" [el "li" [el "a" [.text "This page as data"] [("href", "document.json")]],
          el "li" [el "a" [.text "Every page of the site"] [("href", href ["contents"])]]]]])]
    [("lang", "en")]

/-- **The consumer's site as the package's**: each page with its tree as written, and the
files: the driver's, and each page's `document.json`. -/
def written (s : Site) : Content.Site :=
  let ix := keyIndex s
  { pages := s.pages.map fun p => ⟨p.path, pageTree s ix p⟩
    files := (s.files.map fun f => f.splitOn "/") ++ s.pages.map fun p => p.path ++ ["document.json"] }

/-- The errors of the package's check on the pages as written, in words. -/
def told (s : Site) : List String :=
  let w := written s
  (Content.Site.errors w).map fun p => p.describe (Content.Site.trail w)

/-! ## The consumer's controls (`Test/Audit/SiteControls.lean`) -/

/-- The site of the controls: a root page, and a document of two parts, one referring to the
other, split at its top-level parts under `/s/`. -/
def controlPages : List Page :=
  { path := [], doc := { title := "Root", body := [] } } ::
    split (fun path _ => path == ["s"]) ["s"] "s"
      { title := "Source",
        body := [.part "a" "A" [.para [.ref "b" "to B"]], .part "b" "B" [.para [.text "B"]]] }

/-- The control site, put together as the driver does. -/
def control : Site := assemble controlPages

-- The split: the section, then a page for each part. Both checks pass, and the content model
-- admits every page as written.
#guard control.pages.map (·.path) == [[], ["s"], ["s", "a"], ["s", "b"], ["contents"]]
#guard control.check == []
#guard told control == []
#guard (written control).pages.all fun page => Content.validIn Content.Ctx.document page.tree
#guard (Content.Site.check? (written control)).isSome

-- A reference to a part made a page links to that page's folder, from its sibling; the package
-- reads that link as leading to the page.
#guard (control.at? ["s", "a"]).map (fun p => target (keyIndex control) p "b") == some "../b/"
#guard Content.Site.resolve ["s", "a"] "../b/" == .path ["s", "b", ""] none
#guard Content.Site.folder? ["s", "b", ""] == some ["s", "b"]

/-- The control site with one more page. -/
def withPage (page : Page) : Site := assemble (controlPages ++ [page])

/-- A page with a link to no page. -/
def deadPage : Page :=
  { path := ["x"], doc := { title := "X", body := [.para [.link "../nowhere/" "dead"]] } }

/-- A page of another space that refers to a key of the space `s`. -/
def strayPage : Page :=
  { path := ["y"], space := "other", doc := { title := "Y", body := [.para [.ref "b" "B"]] } }

/-- A page two folders down, with no page above it. -/
def deepPage : Page := { path := ["z", "deep"], doc := { title := "Z", body := [] } }

-- Control: a link to no page or file of the site. The consumer's words, then the package's:
-- the same page, the same link.
#guard (withPage deadPage).check == ["/x/: link ../nowhere/: no page or file of the site"]
#guard told (withPage deadPage) ==
  ["/x/: link `../nowhere/` leads to `/nowhere/`: no page or file of the site: at " ++
    "html/body[1]/main[2]/p[1]/a[0]"]

-- Control: a reference resolves in its own space only. The consumer refuses the key; its
-- `target` falls back to a fragment of the page, and the package refuses that fragment.
#guard (withPage strayPage).check == ["/y/: reference b: no part has this key"]
#guard told (withPage strayPage) ==
  ["/y/: the link `#b` names no identifier of the document: at html/body[1]/main[2]/p[1]/a[0]"]

-- Control: a page whose parent is no page. The same words.
#guard (withPage deepPage).check == ["/z/deep/: no page above it"]
#guard told (withPage deepPage) == ["/z/deep/: no page above it"]

-- Two pages at one path. The consumer says so at each of the two, and the package once, at
-- the second.
#guard (withPage { path := ["s", "a"], doc := { title := "Again", body := [] } }).check ==
  ["/s/a/: two pages at this path", "/s/a/: two pages at this path"]
#guard told (withPage { path := ["s", "a"], doc := { title := "Again", body := [] } }) ==
  ["/s/a/: two pages at this path"]

-- No page at the root: the same three refusals. The package says besides that the link home
-- of each page then leads nowhere.
#guard (assemble [{ path := ["s"], doc := { title := "S", body := [] } }]).check ==
  ["no page at the root", "/s/: no page above it", "/contents/: no page above it"]
#guard told (assemble [{ path := ["s"], doc := { title := "S", body := [] } }]) ==
  ["no page at the root", "/s/: no page above it", "/contents/: no page above it",
   "/s/: link `../` leads to `/`: no page or file of the site: at html/body[1]/header[1]/a[0]",
   "/contents/: link `../` leads to `/`: no page or file of the site: at " ++
    "html/body[1]/header[1]/a[0]"]

/-! ## Where the two checks differ -/

/-- A page with one key on two parts. -/
def twicePage : Page :=
  { path := ["k"], doc := { title := "K", body := [.part "a" "One" [], .part "a" "Two" []] } }

/-- A page of the space `s` that holds a key another page of that space holds. -/
def againPage : Page :=
  { path := ["s", "c"], space := "s", doc := { title := "C", body := [.part "b" "B again" []] } }

-- A key twice on one page: the consumer refuses the key, and the package the identifier, with
-- the paths of both sections.
#guard (withPage twicePage).check == ["/k/: key a: duplicate", "/k/: key a twice in space \"\""]
#guard told (withPage twicePage) ==
  ["/k/: the identifier `a` is defined twice: at html/body[1]/main[3]/section[1] and at " ++
    "html/body[1]/main[3]/section[2]"]

-- A key on two pages of one space is the consumer's alone to refuse: its `target` could not
-- choose between them. Each page's identifiers are its own, so the pages as written have no
-- problem.
#guard (withPage againPage).check == ["/s/c/: key b twice in space \"s\""]
#guard told (withPage againPage) == []

-- The package reads the tree a browser gets, so the shell's own links are checked too. A site
-- put together without its contents page has a dead link in every footer, which the consumer's
-- check, reading documents, does not see.
#guard ({ pages := controlPages, files := ["page.css", "looks.css"] } : Site).check == []
#guard told { pages := controlPages, files := ["page.css", "looks.css"] } ==
  ["/: link `contents/` leads to `/contents/`: no page or file of the site: at " ++
    "html/body[1]/footer[3]/ul[1]/li[1]/a[0]",
   "/s/: link `../contents/` leads to `/contents/`: no page or file of the site: at " ++
    "html/body[1]/footer[3]/ul[1]/li[1]/a[0]",
   "/s/a/: link `../../contents/` leads to `/contents/`: no page or file of the site: at " ++
    "html/body[1]/footer[3]/ul[1]/li[1]/a[0]",
   "/s/b/: link `../../contents/` leads to `/contents/`: no page or file of the site: at " ++
    "html/body[1]/footer[3]/ul[1]/li[1]/a[0]"]

/-! ## More than the consumer checks today -/

/-- A page with a link into `/s/b/`, to a fragment that page does not have. -/
def fragmentPage : Page :=
  { path := ["x"], doc := { title := "X", body := [.para [.link "../s/b/#gone" "B"]] } }

/-- A page with a part, and a page that links to that part. -/
def partPages : List Page :=
  [{ path := ["x"], doc := { title := "X", body := [.part "here" "Here" []] } },
   { path := ["w"], doc := { title := "W", body := [.para [.link "../x/#here" "there"]] } }]

/-- A page with three links off the site. -/
def outPage : Page :=
  { path := ["x"],
    doc := { title := "X", body := [.para [.link "https://example.org/x" "out",
      .link "mailto:someone" "write", .link "//example.org/x" "host"]] } }

-- A link into a page that is there, with a fragment that page does not have. The consumer's
-- check reads the link's path alone.
#guard (withPage fragmentPage).check == []
#guard told (withPage fragmentPage) ==
  ["/x/: link `../s/b/#gone` leads to `/s/b/`, and `#gone` names no identifier of that page: at " ++
    "html/body[1]/main[2]/p[1]/a[0]"]

-- A fragment that the page has.
#guard told (assemble (controlPages ++ partPages)) == []

-- A stylesheet the site does not hold: every page links `looks.css` and `page.css`.
#guard (told { (assemble controlPages) with files := ["page.css"] }).head? ==
  some ("/: link `looks.css` leads to `/looks.css`: no page or file of the site: at " ++
    "html/head[0]/link[2]")

-- A link off the site is counted and not judged; so is a link to a host.
#guard told (withPage outPage) == []
#guard (Content.Site.elsewhere (written (withPage outPage))).map
    (fun found => (found.1, found.2.it.href)) ==
  [(["x"], "https://example.org/x"), (["x"], "mailto:someone"), (["x"], "//example.org/x")]

-- A `base` element: the page is refused, since its links would be read against another
-- address.
#guard (Content.Site.errors { pages := [⟨[], el "html" [el "head" [el "title" [.text "t"],
    el "base" [] [("href", "https://example.org/")]], el "body" [el "h1" [.text "T"]]]⟩] }).map
  (·.describe) ==
  ["/: a `base` element with `href` `https://example.org/`: the links of such a page are not " ++
    "read: at the child path [0, 1]"]

/-! ## The reading of a reference -/

-- From the page `/s/a/`: its own folder, a file beside it, its parent, the root.
#guard Content.Site.resolve ["s", "a"] "" == .path ["s", "a", ""] none
#guard Content.Site.resolve ["s", "a"] "./" == .path ["s", "a", ""] none
#guard Content.Site.resolve ["s", "a"] "." == .path ["s", "a", ""] none
#guard Content.Site.resolve ["s", "a"] "document.json" == .path ["s", "a", "document.json"] none
#guard Content.Site.resolve ["s", "a"] ".." == .path ["s", ""] none
#guard Content.Site.resolve ["s", "a"] "../../page.css" == .path ["page.css"] none
#guard Content.Site.resolve ["s", "a"] "/" == .path [""] none
#guard Content.Site.resolve ["s", "a"] "/contents/" == .path ["contents", ""] none

-- The standard's own note on the path state: `/usr/..` is `/`, and not a lack of a path.
#guard Content.Site.resolve [] "/usr/.." == .path [""] none

-- A query is dropped, and a fragment kept as written.
#guard Content.Site.resolve ["s", "a"] "?q=1#x" == .path ["s", "a", ""] (some "x")
#guard Content.Site.resolve ["s", "a"] "../b/#claim:3" == .path ["s", "b", ""] (some "claim:3")

-- A scheme, and a host, lead off the site.
#guard Content.Site.resolve ["s", "a"] "https://example.org/x" == .elsewhere
#guard Content.Site.resolve ["s", "a"] "mailto:someone" == .elsewhere
#guard Content.Site.resolve ["s", "a"] "//example.org/x" == .elsewhere

-- The parser's cleaning, its dot segments in either spelling, and the reverse solidus.
#guard Content.Site.resolve ["s", "a"] "  ../%2E%2e/b/\t " == .path ["b", ""] none
#guard Content.Site.resolve ["s", "a"] "..\\b\\" == .path ["s", "b", ""] none

-- No path leads above the root, and a segment names its folder percent-decoded.
#guard Content.Site.resolve [] "../../x/" == .path ["x", ""] none
#guard Content.Site.resolve ["s"] "%C3%A9tat/" == .path ["s", "état", ""] none

-- The consumer's `linkTo` and the package's `resolve` agree on every pair of pages of the
-- control site: a link written from one page to another leads to that page.
#guard control.pages.all fun here => control.pages.all fun there =>
  Content.Site.resolve here.path (linkTo here.path there.path) == .path (there.path ++ [""]) none

/-! ## The laws at this site -/

/-- The tree of one more page for the control site as written, from its document. -/
def extraTree (page : Page) : RawNode :=
  let larger := withPage page
  pageTree larger (keyIndex larger) page

/-- A page under `/s/` that links to its sibling and to the contents page. -/
def newPage : Page :=
  { path := ["s", "new"],
    doc := { title := "New", body := [.para [.link "../a/" "A", .link "../../contents/" "all"]] } }

/-- A page under `/s/` with a link to no page. -/
def newDeadPage : Page :=
  { path := ["s", "new"], doc := { title := "New", body := [.para [.link "../nowhere/" "dead"]] } }

/-- A page at a path that the control site has. -/
def takenPage : Page := { path := ["s", "a"], doc := { title := "Again", body := [] } }

/-- The control site, checked once, with one more page added by `Checked.add?`, and the file
of the page's data, which its footer links. -/
def grown (page : Page) : Option Content.Site.Checked :=
  (Content.Site.check? (written control)).bind fun checked =>
    checked.add? ⟨page.path, extraTree page⟩ [page.path ++ ["document.json"]]

-- `Checked.add?` at the consumer's site: the site is checked once, and one more page is added
-- by reading that page alone. A page whose links lead somewhere is taken, and the site it
-- gives is one that a full check accepts.
#guard (grown newPage).isSome
#guard (grown newPage).map (fun larger => Content.Site.ok larger.site) == some true
#guard (grown newPage).map (fun larger => larger.site.pages.map fun page => page.path) ==
  some [[], ["s"], ["s", "a"], ["s", "b"], ["contents"], ["s", "new"]]

-- A page with a dead link, a page at a path that is taken, and a page with no page above it
-- are not taken.
#guard (grown newDeadPage).isNone
#guard (grown takenPage).isNone
#guard (grown deepPage).isNone

/-- A site written out plainly, for a proof by evaluation: the consumer's own code keeps its
keys in a table, which the kernel cannot run. A root page that links to a page below it and to
a part of that page, and the page, which links back and to a file. -/
def plain : Content.Site where
  pages :=
    [⟨[], el "html" [el "head" [el "title" [.text "Root"]],
        el "body" [el "h1" [.text "Root"],
          el "p" [el "a" [.text "S"] [("href", "s/")], el "a" [.text "part"] [("href", "s/#part")]]]]⟩,
     ⟨["s"], el "html" [el "head" [el "title" [.text "S"]],
        el "body" [el "h1" [.text "S"],
          el "section" [el "h2" [.text "Part"]] [("id", "part")],
          el "p" [el "a" [.text "up"] [("href", "../")], el "a" [.text "data"] [("href", "data.json")]]]]⟩]
  files := [["s", "data.json"]]

/-- The plain site is sound, by evaluation on lists. -/
theorem plain_sound : plain.Sound :=
  (Content.Site.sound_iff_onLists plain).mpr (by decide +kernel)

/-- **`Site.Sound.add` at a site**: any page under `/s/` that is sound alone and whose own
addresses lead somewhere leaves the site sound. Its path is new and a page stands above it by
evaluation; no page of the site is read again. -/
theorem plain_grows (extra : RawNode) (hpage : Content.Document.Sound extra)
    (hlinks : ∀ a ∈ Content.Document.addresses extra,
      (plain.add ⟨["s", "new"], extra⟩).faultOf ["s", "new"] a.it = none) :
    (plain.add ⟨["s", "new"], extra⟩).Sound :=
  plain_sound.add hpage
    (show ["s", "new"] ∉ plain.pages.map (fun page => page.path) by decide +kernel)
    (show ["s"] ∈ plain.pages.map (fun page => page.path) by decide +kernel) hlinks

/-! ## A site of the consumer's size -/

/-- A report shaped as the consumer's: `concepts` parts of `claims` claims each, every claim
referring to a claim of another part and to a requirement, and a plan of `requirements`
requirements, each referring to a claim. -/
def report (concepts claims requirements : Nat) : Document where
  title := "Semantics evidence"
  body :=
    [.part "statuses" "How to read a status" [.para [.text "A status is a word."]]] ++
    ((List.range concepts).map fun c =>
      .part ("concept:" ++ toString c) ("Concept " ++ toString c)
        (.para [.text "What the concept claims."] ::
          (List.range claims).map fun k =>
            .part ("claim:" ++ toString c ++ "." ++ toString k) ("Claim " ++ toString k)
              [.para [.text "See ",
                .ref ("claim:" ++ toString ((c + 1) % concepts) ++ "." ++ toString ((k * 7 + 3) % claims)) "another",
                .text " and ", .ref ("req:R" ++ toString ((c + k) % requirements)) "its requirement"]])) ++
    [.part "plan" "Plan"
      ((List.range requirements).map fun r =>
        .part ("req:R" ++ toString r) ("R" ++ toString r)
          [.para [.text "Rests on ", .ref ("claim:" ++ toString (r % concepts) ++ ".0") "a claim"]])]

/-- The consumer's site: the landing page, the report split as its driver splits it (a page
for each part of the first page but the legend, and for each requirement), a specimen, and the
contents page. -/
def modelled (concepts claims requirements : Nat) : Site :=
  assemble (
    [{ path := [], space := "landing",
       doc := { title := "Effect4", body := [.part "start" "Start here"
        [.items [[.link "semantics/" "Semantics evidence"], [.link "specimen/" "Document specimen"],
          [.link "contents/" "Contents"]]]] } }] ++
    split (fun path key => (path == ["semantics"] && key != "statuses") || path == ["semantics", "plan"])
      ["semantics"] "semantics" (report concepts claims requirements) ++
    [{ path := ["specimen"], space := "specimen",
       doc := { title := "Document specimen", body := [.part "blocks" "Every block kind" []] } }])

-- The consumer's report has 16 parts, 241 claims and 14 requirements, which its driver makes
-- 33 pages. Here: 16 parts, 238 claims, 14 requirements, 33 pages. Both checks pass.
#guard (modelled 14 17 14).pages.length == 33
#guard (modelled 14 17 14).check == []
#guard told (modelled 14 17 14) == []

-- What the package's check read: 5,832 nodes, 294 identifiers, 537 references inside a page,
-- and 967 addresses between pages and files, none of them off the site.
#guard ((written (modelled 14 17 14)).pages.map fun page => page.tree.size).sum == 5832
#guard ((written (modelled 14 17 14)).pages.map fun page =>
    (Content.Document.names page.tree).length).sum == 294
#guard ((written (modelled 14 17 14)).pages.map fun page =>
    (Content.Document.refs page.tree).length).sum == 537
#guard ((written (modelled 14 17 14)).pages.map fun page =>
    (Content.Document.addresses page.tree).length).sum == 967
#guard (Content.Site.elsewhere (written (modelled 14 17 14))).length == 0

end WhatwgTest.Html.Site