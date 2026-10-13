import Whatwg.Html.Content.Site

/-!
# Whatwg.Html.Content.Site.Link

Owner: the writer of a link between two pages of a site (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entries W6 and W13 of `docs/research/2026-10-12-whatwg-requests.md`).
`Whatwg/Html/Content/Site.lean` reads a reference against the path of its page (`resolve`).
This module writes one: from the folders of the page a link stands on to the folders of the
page it names.

What it gives:

- `linkTo here there`, the shortest relative reference from the page at `here` to the page at
  `there`: one `../` for each folder of `here` past the folders the two share, then each folder
  of `there` past them with a slash, and `./` when that is nothing.
- `linkToPart here there fragment`, the same with `#` and a fragment after it.
- `linkToFile here folder name`, the link to a file of the site: the way to its folder, then
  its name. A sheet at the root is `linkToFile here [] "page.css"`.
- `plain name`, a test that computes: the name is one that such a link writes as itself and
  that `resolve` reads back as itself.
- `shared` and `climb`, the two parts `linkTo` is made of.

`Whatwg/Html/Content/Site/Link/Laws.lean` holds the law that joins this writer to the reader:
`resolve here (linkTo here there)` is the folder `there`, for plain names, and
`resolve here (linkToFile here folder name)` is the file. So a navigation whose links are
written by `linkTo` from the paths of a site's own pages has no dead link.

What a plain name is. `linkTo` writes a name as its characters, with no escape. So a name is
plain when the reader takes those characters as one segment that names it: it is not empty, it
is not `.` or `..`, and it holds no `/` or `\` (a slash), no `#` (the fragment), no `?` (the
query), no `%` (the reader percent-decodes a segment), no `:` (a scheme) and no character at or
below U+0020 (the reader takes them off the ends of its input, and a tab or a line break out of
its middle). The test is sufficient and not necessary: a name with a space inside it is read
back too. `WhatwgTest/Html/Links.lean` has a control for each exclusion.

What this module does not claim:

- An escape. A name that is not plain is not written as a reference that names it. A writer
  with percent-encoding, and its round trip through `Document.unescape`, is not here.
- That the reference is valid as the URL Standard defines a valid URL string: `resolve` is the
  reading of `Site.lean`, with the limits its header lists.
- `index.html`. A page is named by its folder, with a slash.
-/

namespace Whatwg.Html.Content.Site

/-- A character that a link writes as itself and the reader takes as a character of a
segment: above U+0020, no slash, and none of `#`, `?`, `%` and `:`. -/
def plainChar (c : Char) : Bool :=
  !isEdge c && !isSlash c && c != '#' && c != '?' && c != '%' && c != ':'

/-- **A name that a link writes as itself.** Not empty, not `.` and not `..`, and every
character a `plainChar`. For such names `resolve` reads back what `linkTo` writes. -/
def plain (name : String) : Bool :=
  name.toList != [] && name.toList != ['.'] && name.toList != ['.', '.'] &&
    name.toList.all plainChar

/-- The number of folders that two paths share at their start. -/
def shared : List String → List String → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: here, b :: there => if a == b then shared here there + 1 else 0

/-- The characters of a reference that goes up `ups` folders and then down each of `downs`:
`../` for each folder up, and the name and a slash for each folder down. -/
def climbChars (ups : Nat) (downs : List String) : List Char :=
  (List.replicate ups ['.', '.', '/']).flatten ++ downs.flatMap fun name => name.toList ++ ['/']

/-- The same, and `./` for a reference that goes nowhere: the page's own folder. -/
def climb : Nat → List String → List Char
  | 0, [] => ['.', '/']
  | ups, downs => climbChars ups downs

/-- **The link from the page at the folders `here` to the page at the folders `there`**: the
shortest relative reference. `linkTo ["a", "b"] ["a", "c"]` is `../c/`, and `linkTo p p` is
`./`. -/
def linkTo (here there : List String) : String :=
  String.ofList (climb (here.length - shared here there) (there.drop (shared here there)))

/-- The link to a part of the page at `there`: `linkTo`, then `#` and the fragment as
written. -/
def linkToPart (here there : List String) (fragment : String) : String :=
  linkTo here there ++ "#" ++ fragment

/-- **The link from the page at `here` to the file `name` in the folder `folder`**: the way to
the folder as `linkTo` writes it, then the name. `linkToFile ["a", "b"] [] "page.css"` is
`../../page.css`, and a file in the page's own folder is its name alone. -/
def linkToFile (here folder : List String) (name : String) : String :=
  String.ofList
    (climbChars (here.length - shared here folder) (folder.drop (shared here folder)) ++ name.toList)

end Whatwg.Html.Content.Site
