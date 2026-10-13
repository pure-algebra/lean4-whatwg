import Whatwg.Html.Content.Site.Link.Laws

/-!
# WhatwgTest.Html.Links

lean4-effect4's link between two pages, on `Whatwg/Html/Content/Site/Link.lean` (slice S22 of
`docs/SVG-PACKAGE-PLAN.md`; entry W6 of `docs/research/2026-10-12-whatwg-requests.md`). The
consumer is read at `6ad8f7b8d`:

| The consumer's code | Here |
| --- | --- |
| `folders`, `up`, `linkTo`, `tools/Tools/Site.lean`, lines 70 to 79 | `Theirs.folders`, `Theirs.up`, `Theirs.linkTo`, word for word |
| `slug`, lines 85 to 88: how a part's key becomes a folder | `Theirs.slug`, word for word |
| `Site.shell`, lines 353 to 370: a link of a page's shell to a page is `linkTo p.path q.path` | `shell_link` |
| `Site.shell`, line 356: a sheet at the root is `up p.path ++ "looks.css"`; line 369: the page's data is `document.json` | `up_eq_linkToFile`, `theirs_sheet`, `theirs_data` |

`linkTo_eq_theirs` says that the package's `linkTo` writes the consumer's text, for every two
paths. So the law of the package is a law of the consumer's own function (`theirs_resolve`): a
link it writes to a path of plain names leads to that folder, from every page.

The controls say why each exclusion of `plain` stands: for each, a name with which the link is
not read back. And two names say that the test is sufficient and not necessary.

What this battery does not claim: that every folder the consumer's `slug` makes is plain. It is
not: `slug` of a key that ends in `:` is the empty name (a control below).
-/

namespace WhatwgTest.Html.Links

open Whatwg.Html.Content
open Whatwg.Html.Content.Site

/-! ## The consumer's code -/

namespace Theirs

/-- A path as the folders of a link, with a slash after each. -/
def folders (path : List String) : String := String.join (path.map (· ++ "/"))

/-- The way from a page's folder up to the root. -/
def up (path : List String) : String := String.join (path.map fun _ => "../")

/-- A link from the page at `here` to the page at `there`, as the shortest relative path. -/
def linkTo (here there : List String) : String :=
  let common := (here.zip there).takeWhile (fun (a, b) => a == b) |>.length
  let s := up (here.drop common) ++ folders (there.drop common)
  if s.isEmpty then "./" else s

/-- A part's key as a folder. -/
def slug (key : String) : String :=
  ((key.splitOn ":").getLast?.getD key).map fun c =>
    let c := c.toLower
    if c.isAlphanum || c == '-' then c else '-'

end Theirs

/-! ## The package's link is the consumer's -/

theorem common_eq_shared : ∀ here there : List String,
    ((here.zip there).takeWhile fun (a, b) => a == b).length = shared here there
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: here, b :: there => by
    cases h : a == b with
    | true =>
      rw [shared, if_pos h, ← common_eq_shared here there]
      simp only [List.zip_cons_cons, List.takeWhile_cons, h, ↓reduceIte, List.length_cons]
    | false =>
      rw [shared, if_neg (ne_true_of_eq_false h)]
      simp only [List.zip_cons_cons, List.takeWhile_cons, h, Bool.false_eq_true, ↓reduceIte,
        List.length_nil]

theorem toList_up (path : List String) :
    (Theirs.up path).toList = (List.replicate path.length ['.', '.', '/']).flatten := by
  rw [Theirs.up, String.toList_join]
  induction path with
  | nil => rfl
  | cons name rest ih =>
    rw [List.map_cons, List.flatMap_cons, ih, List.length_cons, List.replicate_succ, List.flatten_cons]
    rfl

theorem toList_folders (path : List String) :
    (Theirs.folders path).toList = path.flatMap fun name => name.toList ++ ['/'] := by
  rw [Theirs.folders, String.toList_join]
  induction path with
  | nil => rfl
  | cons name rest ih =>
    rw [List.map_cons, List.flatMap_cons, ih, List.flatMap_cons, String.toList_append]
    rfl

/-- A reference that goes up or down writes something. -/
theorem climbChars_eq_nil {ups : Nat} {downs : List String} (h : climbChars ups downs = []) :
    ups = 0 ∧ downs = [] := by
  cases ups with
  | succ ups =>
    rw [climbChars, List.replicate_succ, List.flatten_cons] at h
    exact nomatch h
  | zero =>
    cases downs with
    | nil => exact ⟨rfl, rfl⟩
    | cons name rest =>
      rw [climbChars, List.flatMap_cons] at h
      have hslash := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp
        (List.append_eq_nil_iff.mp h).2).1).2
      exact nomatch hslash

/-- **The package's link is the consumer's**, for every two paths. -/
theorem linkTo_eq_theirs (here there : List String) :
    Theirs.linkTo here there = linkTo here there := by
  have htext : (Theirs.up (here.drop (shared here there)) ++
      Theirs.folders (there.drop (shared here there))).toList =
      climbChars (here.length - shared here there) (there.drop (shared here there)) := by
    rw [String.toList_append, toList_up, toList_folders, List.length_drop]
    rfl
  unfold Theirs.linkTo linkTo
  simp only [common_eq_shared]
  split
  · next hempty =>
    have hnil := htext
    rw [String.isEmpty_iff.mp hempty] at hnil
    obtain ⟨hups, hdowns⟩ := climbChars_eq_nil hnil.symm
    rw [hups, hdowns]
    rfl
  · next hfull =>
    have hsome : climb (here.length - shared here there) (there.drop (shared here there)) =
        climbChars (here.length - shared here there) (there.drop (shared here there)) := by
      cases hups : here.length - shared here there with
      | succ ups => rfl
      | zero =>
        cases hdowns : there.drop (shared here there) with
        | cons name rest => rfl
        | nil =>
          have hnil : (Theirs.up (here.drop (shared here there)) ++
              Theirs.folders (there.drop (shared here there))).toList = [] := by
            rw [htext, hups, hdowns]
            rfl
          exact absurd (String.isEmpty_iff.mpr (String.toList_eq_nil_iff.mp hnil)) hfull
    rw [hsome, ← htext, String.ofList_toList]

/-- **The consumer's own link is read back**: a link it writes to a path of plain names leads
to that folder, from every page. Reader of `resolve_linkTo`. -/
theorem theirs_resolve (here there : List String) (hplain : there.all plain = true) :
    resolve here (Theirs.linkTo here there) = .path (there ++ [""]) none := by
  rw [linkTo_eq_theirs]
  exact resolve_linkTo here there hplain

/-! ## The shell's links -/

/-- Reader of `faultOf_linkTo` and `Sound.at?_eq`: every link of the consumer's shell is
`linkTo p.path q.path` for a page `q` of the site (`Site.shell`, lines 353 to 370: the link
home, the sections, the crumbs, the neighbours). In a sound site whose names are plain, such a
link has no fault, whatever the two pages are. -/
theorem shell_link {s : Site} (hs : s.Sound) {p q : Site.Page} (hq : q ∈ s.pages)
    (hplain : q.path.all plain = true) :
    s.faultOf p.path ⟨"a", "href", Theirs.linkTo p.path q.path⟩ = none := by
  rw [linkTo_eq_theirs]
  exact faultOf_linkTo s (hs.at?_eq hq) hplain p.path "href" (by decide)

/-- The consumer's link to a file at the root is the package's, for every page and name. -/
theorem up_eq_linkToFile (here : List String) (name : String) :
    Theirs.up here ++ name = linkToFile here [] name := by
  have hshared : shared here [] = 0 := by cases here <;> rfl
  apply String.ext
  rw [String.toList_append, toList_up, linkToFile, String.toList_ofList, hshared, Nat.sub_zero]
  simp only [climbChars, List.drop_nil, List.flatMap_nil, List.append_nil]

/-- **The consumer's link to a sheet is read back**: from every page it leads to the file at
the root. Reader of `resolve_linkToFile`. -/
theorem theirs_sheet (here : List String) {name : String} (hname : plain name = true) :
    resolve here (Theirs.up here ++ name) = .path [name] none := by
  rw [up_eq_linkToFile]
  exact resolve_linkToFile here [] name rfl hname

/-- **The consumer's link to its page's data is read back**: `document.json`, as written, leads
to the file in the page's folder. Reader of `linkToFile_self`. -/
theorem theirs_data (here : List String) (hplain : here.all plain = true) :
    resolve here "document.json" = .path (here ++ ["document.json"]) none := by
  have hlink := resolve_linkToFile here here "document.json" hplain (by decide)
  rw [linkToFile_self] at hlink
  exact hlink

-- Reader of `theirs_sheet` at the consumer's two sheets.
example (here : List String) :
    resolve here (Theirs.up here ++ "looks.css") = .path ["looks.css"] none ∧
      resolve here (Theirs.up here ++ "page.css") = .path ["page.css"] none :=
  ⟨theirs_sheet here (by decide), theirs_sheet here (by decide)⟩

#guard linkToFile ["semantics", "bind"] [] "page.css" == "../../page.css"
#guard linkToFile ["semantics", "bind"] ["fonts", "source-serif-4"] "regular.woff2" ==
  "../../fonts/source-serif-4/regular.woff2"

-- The texts, at paths of the consumer's site: a section from the root, a page from its
-- neighbour in another section, a page above, and the page itself.
#guard linkTo [] ["semantics"] == "semantics/"
#guard linkTo ["semantics", "bind"] ["plan", "phase-2"] == "../../plan/phase-2/"
#guard linkTo ["semantics", "bind"] ["semantics"] == "../"
#guard linkTo ["semantics", "bind"] ["semantics", "pure"] == "../pure/"
#guard linkTo ["semantics"] ["semantics"] == "./"
#guard linkTo ["semantics"] [] == "../"

-- A link to a part of another page: the fragment comes back as written, a colon in it too.
#guard resolve ["plan"] (linkToPart ["plan"] ["semantics", "bind"] "claim:keys-once") ==
  .path ["semantics", "bind", ""] (some "claim:keys-once")

/-! ## What `plain` is for -/

/-- The link to `there` is read back as the folder `there`. -/
def readsBack (here there : List String) : Bool :=
  resolve here (linkTo here there) == .path (there ++ [""]) none

-- The folders that `slug` makes of the consumer's keys are plain.
#guard (["Effect4.Program.Typed", "claim:keys-once", "A part, in words"].map Theirs.slug).all plain

-- Control: `slug` of a key that ends in a colon is the empty name. It is not plain. From the
-- page above, the link to a page in such a folder is `/`, and it leads to the root.
#guard Theirs.slug "claim:" == "" && !plain (Theirs.slug "claim:")
#guard linkTo ["semantics"] ["semantics", ""] == "/"
#guard resolve ["semantics"] (linkTo ["semantics"] ["semantics", ""]) == .path [""] none

-- Controls: one name for each exclusion of `plain`, and with each the law fails. The empty
-- name and the two dot segments name no folder; a slash is two segments; `#` opens a fragment
-- and `?` a query; `%41` is decoded; a colon after letters is a scheme; a space at the front
-- is taken off; a tab is taken out.
#guard !readsBack [] [""]
#guard !readsBack [] ["."]
#guard !readsBack ["a"] [".."]
#guard !readsBack [] ["a/b"]
#guard !readsBack [] ["a\\b"]
#guard !readsBack [] ["a#b"]
#guard !readsBack [] ["a?b"]
#guard !readsBack [] ["a%41"]
#guard !readsBack [] ["a:b"]
#guard !readsBack [] [" a"]
#guard !readsBack [] ["a\tb"]
#guard ["", ".", "..", "a/b", "a\\b", "a#b", "a?b", "a%41", "a:b", " a", "a\tb"].all fun name =>
  !plain name

-- Control: the test is sufficient and not necessary. A space inside a name, and a `%` that
-- opens no escape, are read back; `plain` refuses both.
#guard readsBack [] ["a b"] && !plain "a b"
#guard readsBack [] ["a%zz"] && !plain "a%zz"

-- Control: nothing is asked of the page the link stands on. From a folder whose name is not
-- plain, the link is read back.
#guard readsBack ["a/b", "?"] ["semantics"]

/-! ## Readers of the laws -/

-- Reader of `resolve_linkToPart`: a link to a part of a page, for every two paths.
example (here there : List String) (h : there.all plain = true) :
    resolve here (linkToPart here there "claim:keys-once") =
      .path (there ++ [""]) (some "claim:keys-once") :=
  resolve_linkToPart here there _ h (by decide)

-- Reader of `linkTo_self` and `resolve_linkTo`: a page's link to itself is `./`, and it leads
-- to the page.
example (path : List String) (h : path.all plain = true) :
    Theirs.linkTo path path = "./" ∧ resolve path "./" = .path (path ++ [""]) none := by
  rw [linkTo_eq_theirs, ← linkTo_self path]
  exact ⟨rfl, resolve_linkTo path path h⟩

-- Reader of `take_shared` and `shared_le_left`: the link climbs no further than the root.
example (here there : List String) : here.length - shared here there ≤ here.length := Nat.sub_le _ _

end WhatwgTest.Html.Links
