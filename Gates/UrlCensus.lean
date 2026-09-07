import Gates.UrlInventory

/-!
Strict source-to-census assignment for URL's reviewed authored inputs.
Declaration record: `docs/URL-CENSUS-INTERFACE.md`.
This tooling validates joins and source intervals, not URL execution or
the semantic justification of an authored explanation.
-/

namespace Gates.UrlCensus

structure SourceRow where
  row : Gates.Census.Row
  disposition : Gates.Census.Disposition
  parent : Option String := none
  dependencies : Array String := #[]
  origins : Array Nat
  deriving Inhabited

structure Explanation where
  b : Nat
  e : Nat
  reason : String
  deriving Repr, BEq, DecidableEq, Inhabited

structure Assignment where
  candidate : Gates.UrlInventory.Entry
  owner : Option String
  reason : String
  deriving Repr, BEq, DecidableEq, Inhabited

private def validSpan (bs : ByteArray) (b e : Nat) : Bool :=
  b < e && e ≤ bs.size && (String.fromUTF8? (bs.extract b e)).isSome

private def contains (b e innerB innerE : Nat) : Bool := b ≤ innerB && innerE ≤ e

private def overlaps (b e otherB otherE : Nat) : Bool := b < otherE && otherB < e

private def sameSpan (r s : Gates.Census.Row) : Bool :=
  r.spanB == s.spanB && r.spanE == s.spanE

private def rowContains (r : Gates.Census.Row) (b e : Nat) : Bool :=
  contains r.spanB r.spanE b e

private def rowSize (r : SourceRow) : Nat := r.row.spanE - r.row.spanB

/-- Smallest containing interval; validated row forests make this choice unique. -/
private def owner (rows : Array SourceRow) (b e : Nat) (omittedId : Option String := none) :
    Option SourceRow := Id.run do
  let mut best : Option SourceRow := none
  for r in rows do
    if some r.row.id == omittedId || !rowContains r.row b e then continue
    match best with
    | none => best := some r
    | some old => if rowSize r < rowSize old then best := some r
  return best

private def validateRows (bs : ByteArray) (candidates : Array Gates.UrlInventory.Entry)
    (rows : Array SourceRow) (externalIds : Array String) : Except String Unit := do
  let mut ids : Array String := #[]
  let mut origins : Array Nat := #[]
  for r in rows do
    let s := r.row
    let kindPrefix := s.kind.name ++ "."
    if !s.id.startsWith kindPrefix || s.id == kindPrefix then
      throw s!"invalid row ID {s.id} for kind {s.kind.name}"
    if ids.contains s.id then throw s!"duplicate row ID {s.id}"
    ids := ids.push s.id
    if !validSpan bs s.spanB s.spanE then throw s!"invalid source span for {s.id}"
    if s.anchorB != s.spanB || s.spanE < s.anchorE ||
        !validSpan bs s.anchorB s.anchorE then
      throw s!"invalid source anchor for {s.id}"
    let occurrences := Gates.Census.occurrences bs (bs.extract s.anchorB s.anchorE) 2
    if occurrences != #[s.anchorB] then throw s!"anchor for {s.id} is not unique"
    if r.origins.isEmpty then throw s!"row {s.id} has no declared origin"
    for n in r.origins do
      if n == 0 || candidates.size < n then throw s!"nonexistent origin {n} in {s.id}"
      if origins.contains n then throw s!"duplicate origin {n} in {s.id}"
      origins := origins.push n
      let candidate := candidates[n - 1]!
      if !rowContains s candidate.b candidate.e then
        throw s!"origin {n} is outside row {s.id}"
  for i in [:rows.size] do
    let r := (rows[i]!).row
    for j in [i + 1:rows.size] do
      let s := (rows[j]!).row
      if sameSpan r s then throw s!"identical source spans for {r.id} and {s.id}"
      if overlaps r.spanB r.spanE s.spanB s.spanE &&
          !rowContains r s.spanB s.spanE && !rowContains s r.spanB r.spanE then
        throw s!"crossing source spans for {r.id} and {s.id}"
  for r in rows do
    let enclosing := owner rows r.row.spanB r.row.spanE (some r.row.id)
    if r.parent != enclosing.map (·.row.id) then
      throw s!"incorrect immediate parent for {r.row.id}"
  let mut externals : Array String := #[]
  for id in externalIds do
    if id.isEmpty || externals.contains id || ids.contains id then
      throw s!"invalid, duplicate or colliding external ID {id}"
    externals := externals.push id
  for r in rows do
    let mut seen : Array String := #[]
    for dep in r.dependencies do
      if dep == r.row.id || seen.contains dep then
        throw s!"duplicate or self dependency {dep} in {r.row.id}"
      if !ids.contains dep && !externals.contains dep then
        throw s!"unresolved dependency {dep} in {r.row.id}"
      seen := seen.push dep
  for id in externalIds do
    if !rows.any (fun r => r.dependencies.contains id) then
      throw s!"unused external ID {id}"

private def validateExplanations (bs : ByteArray) (regions : Array Explanation) :
    Except String Unit := do
  for i in [:regions.size] do
    let r := regions[i]!
    if !validSpan bs r.b r.e then throw s!"invalid explanation span at index {i}"
    if r.reason.toList.all (fun c => [0x09, 0x0a, 0x0c, 0x0d, 0x20].contains c.toNat) then
      throw s!"explanation at index {i} has no justification"
    for j in [i + 1:regions.size] do
      let s := regions[j]!
      if overlaps r.b r.e s.b s.e then
        throw s!"overlapping explanatory regions {i} and {j}"

/-- Assign every scanned source candidate, refusing absent or inconsistent authored input. -/
def assign (bs : ByteArray) (rows : Array SourceRow)
    (explanations : Array Explanation) (externalIds : Array String) :
    Except String (Array Assignment) := do
  let candidates ← Gates.UrlInventory.scan bs
  validateRows bs candidates rows externalIds
  validateExplanations bs explanations
  let mut assigned : Array Assignment := #[]
  let mut used := Array.replicate explanations.size false
  let mut errors : Array String := #[]
  for i in [:candidates.size] do
    let candidate := candidates[i]!
    match owner rows candidate.b candidate.e with
    | some r =>
      assigned := assigned.push { candidate, owner := some r.row.id, reason := "" }
    | none =>
      if candidate.kind == .heading then
        assigned := assigned.push { candidate, owner := none, reason := "structural heading" }
      else
        let region := explanations.findIdx? (fun r => contains r.b r.e candidate.b candidate.e)
        match region with
        | some n =>
          used := used.set! n true
          assigned := assigned.push {
            candidate, owner := none, reason := (explanations[n]!).reason }
        | none => errors := errors.push s!"unassigned candidate {i + 1} at byte {candidate.b}"
  for i in [:explanations.size] do
    if !used[i]! then errors := errors.push s!"unused explanatory region {i}"
  if !errors.isEmpty then throw ("\n".intercalate errors.toList)
  for r in rows do
    for n in r.origins do
      if (assigned[n - 1]!).owner != some r.row.id then
        throw s!"origin {n} is assigned to another owner instead of {r.row.id}"
  return assigned

end Gates.UrlCensus
