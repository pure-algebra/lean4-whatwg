import Whatwg.Html.Content.Site.Link
import Whatwg.Html.Content.Site.Laws

/-!
# Whatwg.Html.Content.Site.Link.Laws

Owner: the laws that join the writer of a link (`Whatwg/Html/Content/Site/Link.lean`) to the
reader of one (`resolve` of `Whatwg/Html/Content/Site.lean`).

- **What is written is read back.** `resolve_linkTo`: from any page, the link that `linkTo`
  writes to the folders `there` leads to the folder `there`, when the names of `there` are
  plain. Nothing is asked of the page the link stands on. `resolve_linkToPart` is the same with
  a fragment, which comes back as written, and `resolve_linkToFile` the same for a file: the
  link leads to the path of the file.
- **A link to a page of the site is no dead link.** `faultOf_linkTo`: where a page stands at
  `there`, an address that `linkTo` wrote has no fault, from every page and on every element
  but `base`. `faultOf_linkToPart`: the same with a fragment that is an identifier of the page
  there. `faultOf_linkToFile`: the same for a file that the site lists. These are the premises
  of `Sound.links` and of `Sound.add`, so a navigation written by `linkTo` from the paths of a
  site's pages adds no error to it.
- `at?_of_mem` and `Sound.at?_eq`: a page of a site stands at its own path, and in a sound site
  it is the page found there.
- `resolve_relative` is the reading that the two laws rest on: what `resolve` makes of a
  relative path written with plain characters and slashes. `shared_le_left`, `take_shared` and
  `linkTo_self` say what the shared folders are.

How the law is proved. `linkTo` is `String.ofList` of a list of characters, and `resolve`
begins with `String.toList`: the two cancel (`String.toList_ofList`), and everything after is
about lists. The reader's cleaning is the identity on characters above U+0020; no scheme is
found before a slash; the two `takeWhile` stop at no character; the segments are a `..` for
each folder up, then the names, then the empty segment; and the walk takes one folder away for
each `..` and adds each name.

What the laws do not say: that a browser follows the link to that page. `resolve` is the
reading of `Site.lean`.
-/

namespace Whatwg.Html.Content.Site

open Whatwg.Html.Content.Document (Address Ref)

/-! ## Characters -/

/-- A character whose lower case is `%` is `%`: only the letters `A` to `Z` change. -/
theorem eq_percent_of_toLower {c : Char} (h : c.toLower = '%') : c = '%' := by
  unfold Char.toLower at h
  split at h
  · next hc =>
    have hv : (c.val + ('a'.val - 'A'.val)).toNat = ('%' : Char).val.toNat := by rw [← h]
    have hlo : ('A' : Char).val.toNat ≤ c.val.toNat := UInt32.le_iff_toNat_le.mp hc.1
    have hhi : c.val.toNat ≤ ('Z' : Char).val.toNat := UInt32.le_iff_toNat_le.mp hc.2
    have hshift : ('a'.val - 'A'.val).toNat = 32 := by decide
    have hpercent : ('%' : Char).val.toNat = 37 := by decide
    have hA : ('A' : Char).val.toNat = 65 := by decide
    have hZ : ('Z' : Char).val.toNat = 90 := by decide
    rw [UInt32.toNat_add, hshift, hpercent] at hv
    rw [hA] at hlo
    rw [hZ] at hhi
    omega
  · exact h

/-- A segment that holds no `%` is none of the percent-encoded forms of a dot segment. -/
theorem map_toLower_bne {segment form : List Char} (hfree : '%' ∉ segment) (hform : '%' ∈ form) :
    (segment.map Char.toLower == form) = false := by
  cases h : segment.map Char.toLower == form with
  | false => rfl
  | true =>
    rw [← eq_of_beq h] at hform
    obtain ⟨c, hc, hlow⟩ := List.mem_map.mp hform
    exact absurd (eq_percent_of_toLower hlow ▸ hc) hfree

/-- What a plain character is, part by part. -/
theorem plainChar_spec {c : Char} (h : plainChar c = true) :
    isEdge c = false ∧ isSlash c = false ∧ c ≠ '#' ∧ c ≠ '?' ∧ c ≠ '%' ∧ c ≠ ':' := by
  unfold plainChar at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- What a plain name is, part by part. -/
theorem plain_spec {name : String} (h : plain name = true) :
    name.toList ≠ [] ∧ name.toList ≠ ['.'] ∧ name.toList ≠ ['.', '.'] ∧
      ∀ c ∈ name.toList, plainChar c = true := by
  unfold plain at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A line break is a character at or below U+0020. -/
theorem isBreak_of_not_isEdge {c : Char} (h : isEdge c = false) : isBreak c = false := by
  cases hb : isBreak c with
  | false => rfl
  | true =>
    unfold isBreak at hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with (rfl | rfl) | rfl <;> exact absurd h (by decide)

/-! ## The reader's first steps, on characters it leaves alone -/

/-- `dropWhile` drops nothing where the test fails of every element. -/
theorem dropWhile_of_all_false {p : Char → Bool} : ∀ {l : List Char},
    (∀ c ∈ l, p c = false) → l.dropWhile p = l
  | [], _ => rfl
  | c :: rest, h => by
    rw [List.dropWhile_cons, h c List.mem_cons_self]
    exact if_neg Bool.false_ne_true

/-- `takeWhile` takes everything where the test holds of every element. -/
theorem takeWhile_of_all {p : Char → Bool} : ∀ {l : List Char},
    (∀ c ∈ l, p c = true) → l.takeWhile p = l
  | [], _ => rfl
  | c :: rest, h => by
    rw [List.takeWhile_cons, h c List.mem_cons_self, if_pos rfl,
      takeWhile_of_all fun d hd => h d (List.mem_cons_of_mem c hd)]

/-- The reader's cleaning leaves a text alone when every character is above U+0020. -/
theorem cleaned_ofList {l : List Char} (h : ∀ c ∈ l, isEdge c = false) :
    cleaned (String.ofList l) = l := by
  have hkept : ∀ c ∈ l, (!isBreak c) = true := fun c hc => by
    rw [isBreak_of_not_isEdge (h c hc)]
    rfl
  unfold cleaned
  rw [String.toList_ofList, dropWhile_of_all_false h,
    dropWhile_of_all_false (l := l.reverse) (fun c hc => h c (List.mem_reverse.mp hc)),
    List.reverse_reverse, List.filter_eq_self.mpr hkept]

/-- No scheme ends where no character before the end of a text is a colon, and the text that
follows opens no scheme's end. -/
theorem schemeEnds_append : ∀ (l tail : List Char), (∀ c ∈ l, c ≠ ':') →
    schemeEnds tail = false → schemeEnds (l ++ tail) = false
  | [], _, _, htail => htail
  | c :: rest, tail, h, htail => by
    rw [List.cons_append, schemeEnds, if_neg (by rw [beq_iff_eq]; exact h c List.mem_cons_self)]
    split
    · exact schemeEnds_append rest tail (fun d hd => h d (List.mem_cons_of_mem c hd)) htail
    · rfl

/-- A text with no colon before a tail that ends no scheme opens with no scheme. -/
theorem hasScheme_append {l tail : List Char} (h : ∀ c ∈ l, c ≠ ':')
    (htail : schemeEnds tail = false) : hasScheme (l ++ tail) = false := by
  cases l with
  | nil =>
    cases tail with
    | nil => rfl
    | cons c rest =>
      unfold schemeEnds at htail
      rw [List.nil_append, hasScheme]
      split at htail
      · exact Bool.noConfusion htail
      · next hcolon =>
        cases halpha : c.isAlpha with
        | false => rfl
        | true =>
          have hnum : c.isAlphanum = true := by
            unfold Char.isAlphanum
            rw [halpha]
            rfl
          rw [hnum, Bool.true_or, Bool.true_or, Bool.true_or, if_pos rfl] at htail
          rw [htail]
          rfl
  | cons c rest =>
    rw [List.cons_append, hasScheme,
      schemeEnds_append rest tail (fun d hd => h d (List.mem_cons_of_mem c hd)) htail, Bool.and_false]

/-! ## Segments -/

/-- A run with no slash, then a slash: one segment, and the rest read afresh. -/
theorem segmentsFrom_name : ∀ (name run rest : List Char), (∀ c ∈ name, isSlash c = false) →
    segmentsFrom run (name ++ '/' :: rest) = (run.reverse ++ name) :: segmentsFrom [] rest
  | [], run, rest, _ => by
    rw [List.nil_append, segmentsFrom, if_pos (by decide), List.append_nil]
  | c :: name, run, rest, h => by
    rw [List.cons_append, segmentsFrom, if_neg (ne_true_of_eq_false (h c List.mem_cons_self)),
      segmentsFrom_name name (c :: run) rest (fun d hd => h d (List.mem_cons_of_mem c hd)),
      List.reverse_cons, List.append_assoc]
    rfl

/-- The segments of the folders up: a double dot for each. -/
theorem segmentsFrom_ups (rest : List Char) : ∀ ups : Nat,
    segmentsFrom [] ((List.replicate ups ['.', '.', '/']).flatten ++ rest) =
      List.replicate ups ['.', '.'] ++ segmentsFrom [] rest
  | 0 => rfl
  | ups + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc]
    show segmentsFrom [] (['.', '.'] ++ '/' :: ((List.replicate ups ['.', '.', '/']).flatten ++ rest)) = _
    rw [segmentsFrom_name ['.', '.'] [] _ (by decide), segmentsFrom_ups rest ups, List.replicate_succ]
    rfl

/-- The segments of the folders down, before what follows them: each name, then the segments
of the rest. -/
theorem segmentsFrom_downs_append (tail : List Char) : ∀ downs : List String,
    (∀ name ∈ downs, plain name = true) →
      segmentsFrom [] ((downs.flatMap fun name => name.toList ++ ['/']) ++ tail) =
        downs.map String.toList ++ segmentsFrom [] tail
  | [], _ => rfl
  | name :: rest, h => by
    have hname : ∀ c ∈ name.toList, isSlash c = false := fun c hc =>
      (plainChar_spec ((plain_spec (h name List.mem_cons_self)).2.2.2 c hc)).2.1
    rw [List.flatMap_cons, List.append_assoc, List.append_assoc]
    show segmentsFrom []
      (name.toList ++ '/' :: ((rest.flatMap fun name => name.toList ++ ['/']) ++ tail)) = _
    rw [segmentsFrom_name name.toList [] _ hname,
      segmentsFrom_downs_append tail rest
        (fun other hother => h other (List.mem_cons_of_mem name hother))]
    rfl

/-- The segments of the folders down: each name, and the empty segment after the last slash. -/
theorem segmentsFrom_downs (downs : List String) (h : ∀ name ∈ downs, plain name = true) :
    segmentsFrom [] (downs.flatMap fun name => name.toList ++ ['/']) =
      downs.map String.toList ++ [[]] := by
  have hall := segmentsFrom_downs_append [] downs h
  rw [List.append_nil] at hall
  exact hall

/-- A run with no slash to the end of the text is one segment. -/
theorem segmentsFrom_run : ∀ (name run : List Char), (∀ c ∈ name, isSlash c = false) →
    segmentsFrom run name = [run.reverse ++ name]
  | [], run, _ => by rw [segmentsFrom, List.append_nil]
  | c :: name, run, h => by
    rw [segmentsFrom, if_neg (ne_true_of_eq_false (h c List.mem_cons_self)),
      segmentsFrom_run name (c :: run) (fun d hd => h d (List.mem_cons_of_mem c hd)),
      List.reverse_cons, List.append_assoc]
    rfl

/-- The segments of a reference that climbs and goes down. -/
theorem segments_climbChars (ups : Nat) {downs : List String}
    (h : ∀ name ∈ downs, plain name = true) :
    segments (climbChars ups downs) =
      List.replicate ups ['.', '.'] ++ (downs.map String.toList ++ [[]]) := by
  rw [segments, climbChars, segmentsFrom_ups, segmentsFrom_downs downs h]

/-- The segments of a reference that climbs, goes down and names a file. -/
theorem segments_climbChars_file (ups : Nat) {downs : List String}
    (h : ∀ name ∈ downs, plain name = true) {name : String} (hname : plain name = true) :
    segments (climbChars ups downs ++ name.toList) =
      List.replicate ups ['.', '.'] ++ (downs.map String.toList ++ [name.toList]) := by
  have hrun : ∀ c ∈ name.toList, isSlash c = false := fun c hc =>
    (plainChar_spec ((plain_spec hname).2.2.2 c hc)).2.1
  rw [segments, climbChars, List.append_assoc, segmentsFrom_ups, segmentsFrom_downs_append _ downs h,
    segmentsFrom_run name.toList [] hrun]
  rfl

/-! ## The walk -/

/-- A segment that is not the last is walked as one that a slash follows. -/
theorem walk_cons_of_ne_nil (path : List String) (segment : List Char) :
    ∀ {rest : List (List Char)}, rest ≠ [] →
      walk path (segment :: rest) = walk (stepSegment path segment false) rest
  | [], h => absurd rfl h
  | _ :: _, _ => by rw [walk]

/-- A double dot takes one folder away. -/
theorem stepSegment_doubleDot (path : List String) :
    stepSegment path ['.', '.'] false = path.dropLast := by
  rw [stepSegment, if_pos (by decide)]
  exact List.append_nil _

/-- A plain name is the folder it names: it is no dot segment, and it is not decoded. -/
theorem stepSegment_plain {name : String} (h : plain name = true) (path : List String)
    (last : Bool) : stepSegment path name.toList last = path ++ [name] := by
  obtain ⟨_, hdot, hdots, hchars⟩ := plain_spec h
  have hfree : '%' ∉ name.toList := fun hin => (plainChar_spec (hchars _ hin)).2.2.2.2.1 rfl
  have hdouble : isDoubleDot name.toList = false := by
    unfold isDoubleDot
    rw [beq_false_of_ne hdots, map_toLower_bne hfree (by decide), map_toLower_bne hfree (by decide),
      map_toLower_bne hfree (by decide)]
    rfl
  have hsingle : isSingleDot name.toList = false := by
    unfold isSingleDot
    rw [beq_false_of_ne hdot, map_toLower_bne hfree (by decide)]
    rfl
  have hcontains : name.toList.contains '%' = false := by
    cases hc : name.toList.contains '%' with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hfree
  rw [stepSegment, if_neg (ne_true_of_eq_false hdouble), if_neg (ne_true_of_eq_false hsingle),
    nameOf, if_neg (ne_true_of_eq_false hcontains), String.ofList_toList]

/-- A double dot for each of `ups` folders takes that many folders away. -/
theorem walk_ups : ∀ (ups : Nat) (path : List String) {tail : List (List Char)}, tail ≠ [] →
    walk path (List.replicate ups ['.', '.'] ++ tail) = walk (path.take (path.length - ups)) tail
  | 0, path, _, _ => by
    rw [Nat.sub_zero, List.take_length]
    rfl
  | ups + 1, path, tail, htail => by
    rw [List.replicate_succ, List.cons_append,
      walk_cons_of_ne_nil path _ (List.append_ne_nil_of_right_ne_nil _ htail),
      stepSegment_doubleDot, walk_ups ups path.dropLast htail, List.dropLast_eq_take, List.take_take,
      List.length_take]
    congr 2
    omega

/-- Each plain name adds its folder, and the last segment is walked from there. -/
theorem walk_downs_then (last : List Char) : ∀ (downs : List String) (path : List String),
    (∀ name ∈ downs, plain name = true) →
      walk path (downs.map String.toList ++ [last]) = stepSegment (path ++ downs) last true
  | [], path, _ => by
    show stepSegment path last true = stepSegment (path ++ []) last true
    rw [List.append_nil]
  | name :: rest, path, h => by
    rw [List.map_cons, List.cons_append,
      walk_cons_of_ne_nil path _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      stepSegment_plain (h name List.mem_cons_self),
      walk_downs_then last rest (path ++ [name])
        (fun other hother => h other (List.mem_cons_of_mem name hother)),
      List.append_assoc path [name] rest]
    rfl

/-- Each plain name adds its folder, and the empty segment after the last slash ends the path
in a folder. -/
theorem walk_downs (downs : List String) (path : List String)
    (h : ∀ name ∈ downs, plain name = true) :
    walk path (downs.map String.toList ++ [[]]) = path ++ downs ++ [""] := by
  rw [walk_downs_then [] downs path h, stepSegment, if_neg (by decide), if_neg (by decide)]
  rfl

/-- **The walk of what `climb` writes**: `ups` folders are taken off the path, and the folders
`downs` are added. -/
theorem walk_segments_climb (path : List String) (ups : Nat) {downs : List String}
    (h : ∀ name ∈ downs, plain name = true) :
    walk path (segments (climb ups downs)) = path.take (path.length - ups) ++ downs ++ [""] := by
  have hgeneral : walk path (segments (climbChars ups downs)) =
      path.take (path.length - ups) ++ downs ++ [""] := by
    rw [segments_climbChars ups h,
      walk_ups ups path (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      walk_downs downs _ h]
  cases ups with
  | succ ups => exact hgeneral
  | zero =>
    cases downs with
    | cons name rest => exact hgeneral
    | nil =>
      show walk path [['.'], []] = _
      rw [walk, stepSegment, if_neg (by decide), if_pos (by decide), walk, stepSegment,
        if_neg (by decide), if_neg (by decide), Nat.sub_zero, List.take_length]
      rfl

/-- **The walk of a link to a file**: `ups` folders are taken off the path, the folders `downs`
are added, and the file's name ends the path. -/
theorem walk_segments_file (path : List String) (ups : Nat) {downs : List String}
    (h : ∀ name ∈ downs, plain name = true) {name : String} (hname : plain name = true) :
    walk path (segments (climbChars ups downs ++ name.toList)) =
      path.take (path.length - ups) ++ downs ++ [name] := by
  rw [segments_climbChars_file ups h hname,
    walk_ups ups path (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
    walk_downs_then name.toList downs _ h, stepSegment_plain hname]

/-! ## The characters of a link -/

/-- Every character that `climbChars` writes is a plain character or a slash. -/
theorem mem_climbChars {ups : Nat} {downs : List String} (h : ∀ name ∈ downs, plain name = true)
    {c : Char} (hc : c ∈ climbChars ups downs) : plainChar c = true ∨ c = '/' := by
  rcases List.mem_append.mp hc with hup | hdown
  · obtain ⟨part, hpart, hin⟩ := List.mem_flatten.mp hup
    rw [List.eq_of_mem_replicate hpart] at hin
    rcases List.mem_cons.mp hin with rfl | hin
    · exact Or.inl (by decide)
    · rcases List.mem_cons.mp hin with rfl | hin
      · exact Or.inl (by decide)
      · exact Or.inr (List.mem_singleton.mp hin)
  · obtain ⟨name, hname, hin⟩ := List.mem_flatMap.mp hdown
    rcases List.mem_append.mp hin with hin | hin
    · exact Or.inl ((plain_spec (h name hname)).2.2.2 c hin)
    · exact Or.inr (List.mem_singleton.mp hin)

/-- Every character that `climb` writes is a plain character or a slash. -/
theorem mem_climb {ups : Nat} {downs : List String} (h : ∀ name ∈ downs, plain name = true)
    {c : Char} (hc : c ∈ climb ups downs) : plainChar c = true ∨ c = '/' := by
  cases ups with
  | succ ups => exact mem_climbChars h hc
  | zero =>
    cases downs with
    | cons name rest => exact mem_climbChars h hc
    | nil =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl (by decide)
      · exact Or.inr (List.mem_singleton.mp hc)

/-- What `climb` writes begins with a character that is no slash. -/
theorem climb_head {ups : Nat} {downs : List String} (h : ∀ name ∈ downs, plain name = true) :
    ∃ first rest, climb ups downs = first :: rest ∧ isSlash first = false := by
  cases ups with
  | succ ups => exact ⟨'.', _, rfl, by decide⟩
  | zero =>
    cases downs with
    | nil => exact ⟨'.', _, rfl, by decide⟩
    | cons name rest =>
      obtain ⟨hne, _, _, hchars⟩ := plain_spec (h name List.mem_cons_self)
      cases hname : name.toList with
      | nil => exact absurd hname hne
      | cons first more =>
        refine ⟨first, more ++ ['/'] ++ rest.flatMap fun name => name.toList ++ ['/'], ?_, ?_⟩
        · show ([] : List Char) ++ ((name.toList ++ ['/']) ++ rest.flatMap _) = _
          rw [hname]
          rfl
        · exact (plainChar_spec (hchars first (by rw [hname]; exact List.mem_cons_self))).2.1

/-- What `linkToFile` writes begins with a character that is no slash. -/
theorem climbChars_file_head {ups : Nat} {downs : List String}
    (h : ∀ name ∈ downs, plain name = true) {name : String} (hname : plain name = true) :
    ∃ first rest, climbChars ups downs ++ name.toList = first :: rest ∧ isSlash first = false := by
  cases ups with
  | succ ups => exact ⟨'.', _, rfl, by decide⟩
  | zero =>
    cases downs with
    | nil =>
      obtain ⟨hne, _, _, hchars⟩ := plain_spec hname
      cases htext : name.toList with
      | nil => exact absurd htext hne
      | cons first more =>
        exact ⟨first, more, rfl,
          (plainChar_spec (hchars first (by rw [htext]; exact List.mem_cons_self))).2.1⟩
    | cons folder rest =>
      obtain ⟨hne, _, _, hchars⟩ := plain_spec (h folder List.mem_cons_self)
      cases htext : folder.toList with
      | nil => exact absurd htext hne
      | cons first more =>
        refine ⟨first,
          (more ++ ['/'] ++ rest.flatMap fun name => name.toList ++ ['/']) ++ name.toList, ?_, ?_⟩
        · show (([] : List Char) ++ ((folder.toList ++ ['/']) ++ rest.flatMap _)) ++ name.toList = _
          rw [htext]
          rfl
        · exact (plainChar_spec (hchars first (by rw [htext]; exact List.mem_cons_self))).2.1

/-! ## What is written is read back -/

/-- **What `resolve` makes of a relative path written plainly**, alone or before `#` and a
fragment: the walk of its segments from the page's folder, and the fragment as written. The
path is characters that are plain or slashes, and does not begin with a slash; the tail is
nothing, or `#` and characters above U+0020. -/
theorem resolve_relative (here : List String) {link tail : List Char}
    (hlink : ∀ c ∈ link, plainChar c = true ∨ c = '/')
    (hhead : ∃ first rest, link = first :: rest ∧ isSlash first = false)
    (htail : ∀ c ∈ tail, isEdge c = false) (hopens : tail = [] ∨ ∃ after, tail = '#' :: after) :
    resolve here (String.ofList (link ++ tail)) =
      .path (walk here (segments link)) (tail.tail?.map String.ofList) := by
  have hedge : ∀ c ∈ link ++ tail, isEdge c = false := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · rcases hlink c hc with hplain | rfl
      · exact (plainChar_spec hplain).1
      · decide
    · exact htail c hc
  have hcolon : ∀ c ∈ link, c ≠ ':' := fun c hc => by
    rcases hlink c hc with hplain | rfl
    · exact (plainChar_spec hplain).2.2.2.2.2
    · decide
  have hhash : ∀ c ∈ link, (c != '#') = true := fun c hc => by
    rcases hlink c hc with hplain | rfl
    · exact bne_iff_ne.mpr (plainChar_spec hplain).2.2.1
    · decide
  have hquery : ∀ c ∈ link, (c != '?') = true := fun c hc => by
    rcases hlink c hc with hplain | rfl
    · exact bne_iff_ne.mpr (plainChar_spec hplain).2.2.2.1
    · decide
  have hends : schemeEnds tail = false := by
    rcases hopens with rfl | ⟨after, rfl⟩
    · rfl
    · rw [schemeEnds, if_neg (by decide), if_neg (by decide)]
  have htake : (tail.takeWhile fun c => c != '#') = [] := by
    rcases hopens with rfl | ⟨after, rfl⟩
    · rfl
    · rfl
  have hdrop : (tail.dropWhile fun c => c != '#') = tail := by
    rcases hopens with rfl | ⟨after, rfl⟩
    · rfl
    · rfl
  obtain ⟨first, rest, rfl, hfirst⟩ := hhead
  unfold resolve
  dsimp only
  rw [cleaned_ofList hedge, hasScheme_append hcolon hends, if_neg Bool.false_ne_true,
    List.takeWhile_append_of_pos hhash, List.dropWhile_append_of_pos hhash, htake, hdrop,
    List.append_nil, takeWhile_of_all hquery]
  dsimp only
  rw [if_neg (ne_true_of_eq_false hfirst)]
  cases tail <;> rfl

/-! ## The folders two paths share -/

theorem shared_le_left : ∀ here there : List String, shared here there ≤ here.length
  | [], _ => Nat.le_refl 0
  | _ :: _, [] => Nat.zero_le _
  | a :: here, b :: there => by
    rw [shared]
    split
    · exact Nat.succ_le_succ (shared_le_left here there)
    · exact Nat.zero_le _

theorem shared_le_right : ∀ here there : List String, shared here there ≤ there.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.le_refl 0
  | a :: here, b :: there => by
    rw [shared]
    split
    · exact Nat.succ_le_succ (shared_le_right here there)
    · exact Nat.zero_le _

/-- The folders that two paths share are the same folders. -/
theorem take_shared : ∀ here there : List String,
    here.take (shared here there) = there.take (shared here there)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: here, b :: there => by
    rw [shared]
    split
    · next h => rw [List.take_succ_cons, List.take_succ_cons, take_shared here there, eq_of_beq h]
    · rfl

/-- A path shares all of its folders with itself. -/
theorem shared_self : ∀ path : List String, shared path path = path.length
  | [] => rfl
  | name :: rest => by
    rw [shared, if_pos (beq_self_eq_true name), shared_self rest]
    rfl

/-- The link from a page to itself is its own folder. -/
theorem linkTo_self (path : List String) : linkTo path path = "./" := by
  unfold linkTo
  rw [shared_self, Nat.sub_self, List.drop_length]
  rfl

/-- **What `linkTo` writes, `resolve` reads back**: from the page at any folders `here`, the
link to the folders `there` leads to the folder `there`, when each name of `there` is plain.
Nothing is asked of `here`: no name of it is written. -/
theorem resolve_linkTo (here there : List String) (hplain : there.all plain = true) :
    resolve here (linkTo here there) = .path (there ++ [""]) none := by
  have hdowns : ∀ name ∈ there.drop (shared here there), plain name = true := fun name hname =>
    List.all_eq_true.mp hplain name (List.mem_of_mem_drop hname)
  have hread := resolve_relative here
    (link := climb (here.length - shared here there) (there.drop (shared here there))) (tail := [])
    (fun _ hc => mem_climb hdowns hc) (climb_head hdowns) (fun _ h => nomatch h) (Or.inl rfl)
  rw [List.append_nil] at hread
  have hback : here.length - (here.length - shared here there) = shared here there := by
    have := shared_le_left here there
    omega
  rw [linkTo, hread, walk_segments_climb here _ hdowns, hback, take_shared, List.take_append_drop]
  rfl

/-- The same with a fragment, which comes back as written: the fragment holds no character at
or below U+0020. -/
theorem resolve_linkToPart (here there : List String) (fragment : String)
    (hplain : there.all plain = true) (hfragment : (fragment.toList.all fun c => !isEdge c) = true) :
    resolve here (linkToPart here there fragment) = .path (there ++ [""]) (some fragment) := by
  have hdowns : ∀ name ∈ there.drop (shared here there), plain name = true := fun name hname =>
    List.all_eq_true.mp hplain name (List.mem_of_mem_drop hname)
  have htext : linkToPart here there fragment =
      String.ofList (climb (here.length - shared here there) (there.drop (shared here there)) ++
        '#' :: fragment.toList) := by
    apply String.ext
    rw [linkToPart, linkTo, String.toList_append, String.toList_append, String.toList_ofList,
      String.toList_ofList, String.toList_ofList, List.append_assoc]
    rfl
  have htail : ∀ c ∈ '#' :: fragment.toList, isEdge c = false := fun c hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · decide
    · have hnot := List.all_eq_true.mp hfragment c hc
      rw [Bool.not_eq_true'] at hnot
      exact hnot
  have hread := resolve_relative here
    (link := climb (here.length - shared here there) (there.drop (shared here there)))
    (fun _ hc => mem_climb hdowns hc) (climb_head hdowns) htail (Or.inr ⟨fragment.toList, rfl⟩)
  have hback : here.length - (here.length - shared here there) = shared here there := by
    have := shared_le_left here there
    omega
  rw [htext, hread, walk_segments_climb here _ hdowns, hback, take_shared, List.take_append_drop]
  show Lead.path (there ++ [""]) (some (String.ofList fragment.toList)) = _
  rw [String.ofList_toList]

/-- **A link to a file is read back**: from the page at any folders `here`, the link that
`linkToFile` writes leads to the path of the file, when the names of the folder and of the
file are plain. -/
theorem resolve_linkToFile (here folder : List String) (name : String)
    (hplain : folder.all plain = true) (hname : plain name = true) :
    resolve here (linkToFile here folder name) = .path (folder ++ [name]) none := by
  have hdowns : ∀ other ∈ folder.drop (shared here folder), plain other = true := fun other hother =>
    List.all_eq_true.mp hplain other (List.mem_of_mem_drop hother)
  have hchars : ∀ c ∈ climbChars (here.length - shared here folder) (folder.drop (shared here folder)) ++
      name.toList, plainChar c = true ∨ c = '/' := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact mem_climbChars hdowns hc
    · exact Or.inl ((plain_spec hname).2.2.2 c hc)
  have hread := resolve_relative here (tail := []) hchars (climbChars_file_head hdowns hname)
    (fun _ h => nomatch h) (Or.inl rfl)
  rw [List.append_nil] at hread
  have hback : here.length - (here.length - shared here folder) = shared here folder := by
    have := shared_le_left here folder
    omega
  rw [linkToFile, hread, walk_segments_file here _ hdowns hname, hback, take_shared,
    List.take_append_drop]
  rfl

/-- A file in the page's own folder is linked by its name alone. -/
theorem linkToFile_self (path : List String) (name : String) : linkToFile path path name = name := by
  unfold linkToFile
  rw [shared_self, Nat.sub_self, List.drop_length]
  show String.ofList name.toList = name
  rw [String.ofList_toList]

/-! ## A link to a page of the site -/

/-- A path that ends in the empty segment names the folder before it. -/
theorem folder?_folder (path : List String) : folder? (path ++ [""]) = some path := by
  unfold folder?
  rw [List.getLast?_concat, List.dropLast_concat]
  rfl

/-- A page of a site stands at its own path: some page is found there. -/
theorem at?_of_mem {s : Site} {page : Page} (h : page ∈ s.pages) :
    ∃ found, s.at? page.path = some found ∧ found.path = page.path := by
  cases hfind : s.pages.find? (fun other => other.path == page.path) with
  | none => exact absurd (beq_self_eq_true page.path) (List.find?_eq_none.mp hfind page h)
  | some found =>
    have hsame : (found.path == page.path) = true :=
      List.find?_some (p := fun other : Page => other.path == page.path) hfind
    exact ⟨found, hfind, eq_of_beq hsame⟩

/-- Among pages with no path twice, the page found at a page's path is that page. -/
theorem find?_path_of_nodup : ∀ {pages : List Page}, (pages.map fun page => page.path).Nodup →
    ∀ {page : Page}, page ∈ pages → pages.find? (fun other => other.path == page.path) = some page
  | [], _, _, h => nomatch h
  | first :: rest, hnodup, page, h => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp h with rfl | hrest
    · rw [List.find?_cons, beq_self_eq_true]
    · have hne : (first.path == page.path) = false := by
        cases hsame : first.path == page.path with
        | false => rfl
        | true =>
          exact absurd (List.mem_map.mpr ⟨page, hrest, (eq_of_beq hsame).symm⟩) hnodup.1
      rw [List.find?_cons, hne]
      exact find?_path_of_nodup hnodup.2 hrest

/-- In a sound site the page found at a page's path is that page. -/
theorem Sound.at?_eq {s : Site} (hs : s.Sound) {page : Page} (h : page ∈ s.pages) :
    s.at? page.path = some page :=
  find?_path_of_nodup hs.distinct h

/-- **A link that `linkTo` writes to a folder where a page stands is no dead link**: the
address has no fault, from every page and on every element but `base`. -/
theorem faultOf_linkTo (s : Site) {there : List String} {page : Page}
    (hat : s.at? there = some page) (hplain : there.all plain = true) (here : List String)
    {element : String} (attr : String) (helement : element ≠ "base") :
    s.faultOf here ⟨element, attr, linkTo here there⟩ = none := by
  rw [faultOf_eq_none_iff]
  refine ⟨helement, ?_⟩
  show match resolve here (linkTo here there) with
    | .elsewhere => True
    | .path segments fragment => _
  rw [resolve_linkTo here there hplain]
  show match folder? (there ++ [""]) with
    | none => _
    | some folder => _
  rw [folder?_folder]
  exact ⟨page, hat, fun f hf => nomatch hf⟩

/-- The same for a link to a part of that page: the fragment is an identifier of the page
there. -/
theorem faultOf_linkToPart (s : Site) {there : List String} {page : Page}
    (hat : s.at? there = some page) (hplain : there.all plain = true) (here : List String)
    {element : String} (attr : String) (helement : element ≠ "base") {fragment : String}
    (hfragment : (fragment.toList.all fun c => !isEdge c) = true)
    (hnames : fragment ∈ Document.names page.tree) :
    s.faultOf here ⟨element, attr, linkToPart here there fragment⟩ = none := by
  rw [faultOf_eq_none_iff]
  refine ⟨helement, ?_⟩
  show match resolve here (linkToPart here there fragment) with
    | .elsewhere => True
    | .path segments fragment => _
  rw [resolve_linkToPart here there fragment hplain hfragment]
  show match folder? (there ++ [""]) with
    | none => _
    | some folder => _
  rw [folder?_folder]
  refine ⟨page, hat, fun f hf => ?_⟩
  cases Option.some.inj hf
  exact Or.inl hnames

/-- A path that ends in a name that is not empty names no folder: it is the path of a file. -/
theorem folder?_file (folder : List String) {name : String} (h : name ≠ "") :
    folder? (folder ++ [name]) = none := by
  unfold folder?
  rw [List.getLast?_concat]
  split
  · next heq => exact absurd (Option.some.inj heq) h
  · rfl

/-- **A link that `linkToFile` writes to a file of the site is no dead link.** -/
theorem faultOf_linkToFile (s : Site) {folder : List String} {name : String}
    (hfile : folder ++ [name] ∈ s.files) (hplain : folder.all plain = true)
    (hname : plain name = true) (here : List String) {element : String} (attr : String)
    (helement : element ≠ "base") :
    s.faultOf here ⟨element, attr, linkToFile here folder name⟩ = none := by
  have hne : name ≠ "" := fun h => (plain_spec hname).1 (String.toList_eq_nil_iff.mpr h)
  rw [faultOf_eq_none_iff]
  refine ⟨helement, ?_⟩
  show match resolve here (linkToFile here folder name) with
    | .elsewhere => True
    | .path segments fragment => _
  rw [resolve_linkToFile here folder name hplain hname]
  show match folder? (folder ++ [name]) with
    | none => _
    | some folder => _
  rw [folder?_file folder hne]
  exact hfile

end Whatwg.Html.Content.Site
