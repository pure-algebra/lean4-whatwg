import Whatwg.Html.Content.Document

/-!
# Whatwg.Html.Content.Site

Owner: the rules that hold across the pages of a site (entries W6 and W13 of
`docs/research/2026-10-12-whatwg-requests.md`). A site is a list of pages, each a path of
folders from the root and a tree, and the other files it holds. `Content/Document.lean` judges
one tree and keeps every `href` that leaves it as an address. This module reads each address
against the path of its page and says where it leads: off the site, to a page of the site and
perhaps a fragment in it, to a file of the site, or nowhere.

What it gives:

- `resolve here href`, where a reference leads from the page at `here`: `Lead.elsewhere`, or a
  path of the site with its fragment.
- `Site.Problem`, located by page and by path in the page: a problem of one page's document; a
  site with no page at the root, two pages at one path, a page with no page above it; a page
  with a `base` element; a link to no page or file; a link to a page whose fragment names no
  identifier of that page. `problems`, `errors`, `advice`, `ok`, and `Problem.describe`.
- `Site.Sound`, the plain statement, and `Site.Checked`, a site that the checker accepts page
  by page and that is `Sound`. `Whatwg/Html/Content/Site/Laws.lean` proves that `errors` is
  empty exactly for a `Sound` site, and that a page added to a sound site leaves it sound when
  the page is sound, stands at a new path below a page, and its own links lead somewhere;
  `Checked.add?` there adds a page to a checked site by reading that page alone.
- `elsewhere`, the addresses that lead off the site: counted, not judged.

## How a reference is read, and why here

The URL library of this repository holds the percent-encoding of the URL Standard and no more:
`Whatwg/Url/Parser.lean`, `Record.lean` and `Serializer.lean` declare nothing yet. So there is
no parser to call. `resolve` is the part of the basic URL parser that a link between pages of
one site meets, written from the sealed text (`vendor/whatwg-url-55d66993/url.bs`; the line of
each state at the pin):

- the input loses a C0 control or space at each end, and every tab and line break (lines 2304
  and 2310);
- a letter, then letters, digits, `+`, `-` or `.`, then `:` is a scheme (scheme start state and
  scheme state, lines 2331 and 2349): the reference is absolute, and leads `elsewhere`;
- otherwise it is relative to the page (no scheme state, line 2435; relative state, line 2479):
  an empty path keeps the page's own; a path that begins with one slash starts at the root,
  and with two it names a host and leads `elsewhere` (relative slash state, line 2528); any
  other path starts in the page's folder, the base's path shortened (line 2047);
- each segment between slashes is added, a single-dot segment adds nothing, a double-dot
  segment takes one away, and a path that ends in a slash or a dot segment ends in the empty
  segment (path state, line 2948; the dot segments, lines 1956 and 1962). `\` is a slash, as in
  a special scheme;
- what follows `?` is dropped, and what follows `#` is the fragment.

The address of the page at the folders `here` is taken to be `here` and the empty segment: its
folder, with a slash. A static host serves a page's `index.html` there. The base's scheme is
taken to be special and not `file`.

The module stands in the HTML library and imports nothing of the URL library, because nothing
there reads a reference. When the parser lands, the theorem that `resolve` is that parser at a
base of this shape belongs where both are imported: the test tree first, as
`unescapeBytes_eq` does for the percent-decoding.

## What each rule rests on

Every rule of a site is a convention of this module (`Document.Basis.convention`). The HTML
Standard asks that the `href` of `a` and `area` be "a valid URL potentially surrounded by
spaces" (`vendor/whatwg-html-746f2ede/source`, line 26389), and says how a fragment is found
in a document (section "Scrolling to a fragment", line 112697); no sealed text requires a
link to lead to a page. The three rules of shape (a page at the root, one page at a path, a
page above every page) are those of the consumer's site, whose breadcrumbs and whose link
home need them.

## What this module does not claim

- That `resolve` is the URL parser. It is the states above. It does not read a scheme that is
  the page's own with no slashes after it (`https:page/`, which the parser reads as relative),
  a host, a port or credentials; a path is not percent-encoded as the parser would write it,
  and is percent-decoded segment by segment instead, as a host does to find a file.
- That a reference off the site leads anywhere, or that a host of the same name is this site:
  `//host/page/` is `elsewhere`.
- The `base` element. A page that has one with `href` is refused (`Problem.base`): its links
  would be read against another address, and its own fragments too.
- A fragment into a file: only a page's tree has identifiers this module knows.
- `index.html`. A page is named by its folder; a link to `page/index.html` is a link to a
  file, which is there only if the site lists it.
- `src`, `action` and the other attributes that hold an address: `Document.addresses` keeps
  `href` alone.
-/

namespace Whatwg.Html.Content

open Whatwg.Html (RawNode)
open Whatwg.Html.Content.Document (Placed Fact Address Ref)

/-- A page of a site: the folders from the root to it (none for the root), and its tree. -/
structure Site.Page where
  path : List String
  tree : RawNode

/-- A site: its pages, and its other files, each by its path from the root. -/
structure Site where
  pages : List Site.Page
  files : List (List String) := []

namespace Site

/-! ## Reading a reference -/

/-- A C0 control or a space: what the parser takes off the ends of its input. -/
def isEdge (c : Char) : Bool := c.toNat ≤ 0x20

/-- An ASCII tab or newline: what the parser takes out of its input. -/
def isBreak (c : Char) : Bool := c == '\t' || c == '\n' || c == '\r'

/-- The input as the parser first makes it. -/
def cleaned (href : String) : List Char :=
  ((href.toList.dropWhile isEdge).reverse.dropWhile isEdge).reverse.filter fun c => !isBreak c

/-- The characters after a scheme's first letter run to a `:`. -/
def schemeEnds : List Char → Bool
  | [] => false
  | c :: rest =>
    if c == ':' then true
    else if c.isAlphanum || c == '+' || c == '-' || c == '.' then schemeEnds rest
    else false

/-- The input opens with a scheme: it is an absolute reference. -/
def hasScheme : List Char → Bool
  | [] => false
  | c :: rest => c.isAlpha && schemeEnds rest

/-- A slash, or the reverse solidus that a special scheme reads as one. -/
def isSlash (c : Char) : Bool := c == '/' || c == '\\'

/-- The segments of the characters `rest`, after the characters `run` of a segment that has
begun, last first. A path of `n` slashes has `n + 1` segments. -/
def segmentsFrom : List Char → List Char → List (List Char)
  | run, [] => [run.reverse]
  | run, c :: rest =>
    if isSlash c then run.reverse :: segmentsFrom [] rest else segmentsFrom (c :: run) rest

/-- The segments of a path: the runs between its slashes. -/
def segments (path : List Char) : List (List Char) := segmentsFrom [] path

/-- A single-dot URL path segment: `.` or `%2e`, in either case. -/
def isSingleDot (segment : List Char) : Bool :=
  segment == ['.'] || segment.map Char.toLower == "%2e".toList

/-- A double-dot URL path segment: `..`, `.%2e`, `%2e.` or `%2e%2e`, in either case. -/
def isDoubleDot (segment : List Char) : Bool :=
  segment == ['.', '.'] || segment.map Char.toLower == ".%2e".toList ||
    segment.map Char.toLower == "%2e.".toList || segment.map Char.toLower == "%2e%2e".toList

/-- The folder or file that a segment names: the segment percent-decoded, or as written when
its bytes are no UTF-8. A segment with no `%` is its own name, and is not decoded. -/
def nameOf (segment : List Char) : String :=
  if segment.contains '%' then
    (Document.unescape (String.ofList segment)).getD (String.ofList segment)
  else String.ofList segment

/-- The path after one more segment: the path state. `last` says that no slash follows it. -/
def stepSegment (path : List String) (segment : List Char) (last : Bool) : List String :=
  if isDoubleDot segment then path.dropLast ++ (if last then [""] else [])
  else if isSingleDot segment then path ++ (if last then [""] else [])
  else path ++ [nameOf segment]

/-- The path after each segment of a list. -/
def walk (path : List String) : List (List Char) → List String
  | [] => path
  | [segment] => stepSegment path segment true
  | segment :: next :: rest => walk (stepSegment path segment false) (next :: rest)

/-- Where a reference leads. -/
inductive Lead where
  /-- Off the site, as far as the site can tell: another scheme, or a host. -/
  | elsewhere
  /-- A path of the site, as the path of a URL: a folder ends in the empty segment. With the
  fragment, when the reference has one. -/
  | path (segments : List String) (fragment : Option String)
  deriving DecidableEq, Repr, Inhabited

/-- **Where a reference leads from the page at the folders `here`**: the relative states of the
basic URL parser, at a base whose path is `here` and the empty segment. -/
def resolve (here : List String) (href : String) : Lead :=
  let input := cleaned href
  if hasScheme input then .elsewhere
  else
    let front := input.takeWhile fun c => c != '#'
    let fragment : Option String :=
      match input.dropWhile fun c => c != '#' with
      | _ :: after => some (String.ofList after)
      | [] => none
    match front.takeWhile fun c => c != '?' with
    | [] => .path (here ++ [""]) fragment
    | c :: rest =>
      if isSlash c then
        match rest with
        | d :: _ => if isSlash d then .elsewhere else .path (walk [] (segments rest)) fragment
        | [] => .path (walk [] (segments rest)) fragment
      else .path (walk here (segments (c :: rest))) fragment

/-- The folder that a path of the site names, when it ends in a slash. -/
def folder? (segments : List String) : Option (List String) :=
  match segments.getLast? with
  | some "" => some segments.dropLast
  | _ => none

/-! ## Where an address leads -/

/-- Why an address leads nowhere. -/
inductive Fault where
  /-- It stands on a `base` element. -/
  | base
  /-- It leads to a path where no page and no file of the site stands. -/
  | dead (to : List String)
  /-- It leads to a page, and its fragment names no identifier of that page. -/
  | fragment (to : List String) (fragment : String)
  deriving DecidableEq, Repr, Inhabited

/-- Why an address that leads to a folder leads nowhere, from the test of the identifiers of
the page there, when a page is there. The fragment is read as a document's own fragment is
(`Document.Ref.namesBy`). -/
def faultIn (a : Address) (segments : List String) (fragment : Option String) :
    Option (String → Bool) → Option Fault
  | none => some (.dead segments)
  | some known =>
    match fragment with
    | none => none
    | some f =>
      if (⟨a.element, a.attr, .fragment, f⟩ : Ref).namesBy known then none
      else some (.fragment segments f)

/-- Why an address leads nowhere, from where it leads. `pageAt` gives the test of a page's
identifiers, when a page stands at a folder; `fileAt` says whether a file stands at a path. -/
def faultAt (pageAt : List String → Option (String → Bool)) (fileAt : List String → Bool)
    (a : Address) : Lead → Option Fault
  | .elsewhere => none
  | .path segments fragment =>
    match folder? segments with
    | none => if fileAt segments then none else some (.dead segments)
    | some folder => faultIn a segments fragment (pageAt folder)

/-- Why an address of the page at `here` leads nowhere; none when it leads to a page, to a
file, or off the site. An address on a `base` element is refused before it is read. -/
def fault? (pageAt : List String → Option (String → Bool)) (fileAt : List String → Bool)
    (here : List String) (a : Address) : Option Fault :=
  if a.element == "base" then some .base else faultAt pageAt fileAt a (resolve here a.href)

/-! ## Problems -/

/-- What is wrong with a site. -/
inductive Problem where
  /-- No page stands at the root. -/
  | noRoot
  /-- Two pages stand at one path. -/
  | twoPages (page : List String)
  /-- The folder above the page holds no page. -/
  | noParent (page : List String)
  /-- A problem of one page's document. -/
  | inPage (page : List String) (problem : Document.Problem)
  /-- The page has a `base` element with `href`: its addresses are not read. -/
  | base (page : List String) (path : List Nat) (address : Address)
  /-- An address leads to no page and no file of the site. -/
  | deadLink (page : List String) (path : List Nat) (address : Address) (to : List String)
  /-- An address leads to a page, and its fragment names no identifier of that page. -/
  | deadFragment (page : List String) (path : List Nat) (address : Address) (to : List String)
      (fragment : String)
  deriving DecidableEq, Repr, Inhabited

namespace Problem

/-- The problem of an address, from why it leads nowhere. -/
def ofFault (page : List String) (a : Placed Address) : Fault → Problem
  | .base => .base page a.path a.it
  | .dead to => .deadLink page a.path a.it to
  | .fragment to fragment => .deadFragment page a.path a.it to fragment

/-- The page the problem is on; none for a site with no root. -/
def page? : Problem → Option (List String)
  | .noRoot => none
  | .twoPages page => some page
  | .noParent page => some page
  | .inPage page _ => some page
  | .base page _ _ => some page
  | .deadLink page _ _ _ => some page
  | .deadFragment page _ _ _ _ => some page

/-- What the rule rests on: a page's own problem keeps its basis, and every rule of a site is a
convention. -/
def basis : Problem → Document.Basis
  | .inPage _ problem => problem.basis
  | _ => .convention

/-- The problem is an error, and not advice. -/
def isError (p : Problem) : Bool := p.basis.isError

end Problem

/-- A page's folders as a path: `/`, `/s/a/`. -/
def folderText (page : List String) : String := "/" ++ String.join (page.map fun name => name ++ "/")

/-- A path of the site as text: `/s/b/`, `/page.css`. -/
def pathText (segments : List String) : String := "/" ++ "/".intercalate segments

/-- The problem in words, for a message, the page first. `place` writes a path in a page; by
default it writes the child indices. No judgment reads this text. -/
def Problem.describe (p : Problem)
    (place : List String → List Nat → String := fun _ path => "the child path " ++ toString path) :
    String :=
  match p with
  | .noRoot => "no page at the root"
  | .twoPages page => folderText page ++ ": two pages at this path"
  | .noParent page => folderText page ++ ": no page above it"
  | .inPage page problem => folderText page ++ ": " ++ problem.describe (place page)
  | .base page path address =>
    folderText page ++ ": a `base` element with `href` `" ++ address.href ++
      "`: the links of such a page are not read: at " ++ place page path
  | .deadLink page path address to =>
    folderText page ++ ": link `" ++ address.href ++ "` leads to `" ++ pathText to ++
      "`: no page or file of the site: at " ++ place page path
  | .deadFragment page path address to fragment =>
    folderText page ++ ": link `" ++ address.href ++ "` leads to `" ++ pathText to ++ "`, and `#" ++
      fragment ++ "` names no identifier of that page: at " ++ place page path

/-! ## The check -/

/-- What the check reads of a page, once: its path and the facts of its tree. -/
structure Sheet where
  path : List String
  facts : List (Placed Fact)

/-- A page as the check reads it. -/
def read (page : Page) : Sheet := ⟨page.path, Document.facts page.tree⟩

/-- Each path that stands earlier in the list too, in one pass. `seen` holds every path met so
far. -/
def repeatsFrom (seen : Std.HashSet (List String)) : List (List String) → List (List String)
  | [] => []
  | path :: rest =>
    if seen.contains path then path :: repeatsFrom seen rest
    else repeatsFrom (seen.insert path) rest

/-- Each path that is a page's a second time or more. -/
def repeats (paths : List (List String)) : List (List String) := repeatsFrom ∅ paths

/-- The problems of a site's shape, from the paths of its pages: no root, two pages at a path,
a page with no page above it. -/
def shape (paths : List (List String)) : List Problem :=
  let known := Std.HashSet.ofList paths
  (if known.contains [] then [] else [.noRoot]) ++ (repeats paths).map .twoPages ++
    (paths.filter fun path => !path.isEmpty && !known.contains path.dropLast).map .noParent

/-- The errors of each page's own document. -/
def pageErrors (sheets : List Sheet) : List Problem :=
  sheets.flatMap fun sheet =>
    ((Document.problemsOf sheet.facts).filter Document.Problem.isError).map (.inPage sheet.path)

/-- The advice of each page's own document. -/
def pageAdvice (sheets : List Sheet) : List Problem :=
  sheets.flatMap fun sheet =>
    ((Document.problemsOf sheet.facts).filter fun p => !p.isError).map (.inPage sheet.path)

/-- Each address that leads nowhere. The identifiers of every page are put in a table once,
under the page's path, so that an address costs one look for its page and one for its
fragment. -/
def linkErrors (sheets : List Sheet) (files : List (List String)) : List Problem :=
  let index := Document.firstTable (fun entry => entry.1)
    (sheets.map fun sheet => (sheet.path, Std.HashSet.ofList (Document.namesOf sheet.facts)))
  let fileSet := Std.HashSet.ofList files
  sheets.flatMap fun sheet =>
    (Document.addressesIn sheet.facts).filterMap fun a =>
      (fault? (fun folder => (index[folder]?).map fun entry => entry.2.contains) fileSet.contains
        sheet.path a.it).map (Problem.ofFault sheet.path a)

/-- The errors of the pages as read: the site's shape, each page's own, then the links. -/
def errorsOf (sheets : List Sheet) (files : List (List String)) : List Problem :=
  shape (sheets.map fun sheet => sheet.path) ++ pageErrors sheets ++ linkErrors sheets files

/-- The errors of a site. A build fails on these. Each tree is read once. -/
def errors (s : Site) : List Problem := errorsOf (s.pages.map read) s.files

/-- The advice of a site: that of its pages. A build prints these. -/
def advice (s : Site) : List Problem := pageAdvice (s.pages.map read)

/-- The problems of a site: its errors, then its advice. Each tree is read once. -/
def problems (s : Site) : List Problem :=
  let sheets := s.pages.map read
  errorsOf sheets s.files ++ pageAdvice sheets

/-- The site has no error. -/
def ok (s : Site) : Bool := (errors s).isEmpty

/-! ## The plain statement -/

/-- The first page at a path. -/
def at? (s : Site) (path : List String) : Option Page := s.pages.find? fun page => page.path == path

/-- Why an address of the page at `here` leads nowhere in the site, on lists alone: the page at
a folder is the first with that path, its identifiers are those of its tree, and a file is one
the site lists. -/
def faultOf (s : Site) (here : List String) (a : Address) : Option Fault :=
  fault? (fun folder => (s.at? folder).map fun page => (Document.names page.tree).contains)
    (fun file => s.files.contains file) here a

/-- A site has no error, stated with no table: every page is sound alone; a page stands at the
root; no two pages stand at one path; a page stands above every other page; and every address
of every page leads to a page (and its fragment to an identifier of that page), to a file, or
off the site. `ok_iff` of the laws says that `ok` decides this. -/
structure Sound (s : Site) : Prop where
  pages : ∀ page ∈ s.pages, Document.Sound page.tree
  root : [] ∈ s.pages.map fun page => page.path
  distinct : (s.pages.map fun page => page.path).Nodup
  parents : ∀ page ∈ s.pages, page.path ≠ [] →
    page.path.dropLast ∈ s.pages.map fun page => page.path
  links : ∀ page ∈ s.pages, ∀ a ∈ Document.addresses page.tree, s.faultOf page.path a.it = none

/-- The addresses of a site that lead off it, each with the path of its page: counted, and not
judged. -/
def elsewhere (s : Site) : List (List String × Placed Address) :=
  s.pages.flatMap fun page =>
    ((Document.addresses page.tree).filter fun a =>
      a.it.element != "base" && resolve page.path a.it.href == .elsewhere).map fun a =>
        (page.path, a)

/-- A path in a page of the site as the element names along it, for `Problem.describe`. -/
def trail (s : Site) (page : List String) (path : List Nat) : String :=
  match s.at? page with
  | some found => Document.trail found.tree path
  | none => toString path

/-- The site with one more page, after its others, and the files that come with the page. -/
def add (s : Site) (page : Page) (files : List (List String) := []) : Site where
  pages := s.pages ++ [page]
  files := s.files ++ files

/-- A site that the checker accepts page by page and that has no error across it. -/
structure Checked where
  /-- The site. -/
  site : Site
  /-- Every node of every page may stand where it stands. -/
  valid : ∀ page ∈ site.pages, validIn Ctx.document page.tree = true
  /-- The rules across the site hold. -/
  sound : site.Sound

end Site

end Whatwg.Html.Content
