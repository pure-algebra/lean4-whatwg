/-!
# Whatwg.Html.Print.Escape

The standard's "escaping a string" (the HTML fragment serialization
algorithm, `source` line 149701 at the pin; slice H7.2, ruling HP-12): `&`
becomes `&amp;`, U+00A0 becomes `&nbsp;`, `<` becomes `&lt;`, `>` becomes
`&gt;`, and in attribute mode `"` becomes `&quot;` as well. Nothing else is
touched: no control character is escaped, and `"` passes through in text.
Everything is computed at `List Char` and lifted once by `String.ofList`.

Two facts are proved about each mode, and they are the two that the
serializer's injectivity needs. No delimiter survives: a text run contains
no `<` or `>`, an attribute value no `<`, `>` or `"`. And the escaper's
output decodes back to its input (`unescape_escape`, `unescape_escapeAttr`),
from which injectivity follows; every `&` in the output begins one of the
five references, because the output decodes. `unescape` is a decoder for the
escaper's own alphabet and not an HTML parser (ruling HP-8).
-/

namespace Whatwg.Html.Print

/-! ## The escaper -/

/-- U+00A0 NO-BREAK SPACE. -/
def nbsp : Char := Char.ofNat 0xA0

/-- The characters whose appearance in a text run would change where the run
ends. -/
def isDelim (c : Char) : Bool := c == '<' || c == '>'

/-- The characters an attribute value may not contain. -/
def isAttrDelim (c : Char) : Bool := c == '<' || c == '>' || c == '"'

/-- Escaping a string, not in attribute mode, one character at a time. The
`if` chain rather than a literal-pattern `match` is deliberate: `split`
produces usable disequality hypotheses from it. -/
def escapeChar (c : Char) : List Char :=
  if c = '&' then ['&', 'a', 'm', 'p', ';']
  else if c = nbsp then ['&', 'n', 'b', 's', 'p', ';']
  else if c = '<' then ['&', 'l', 't', ';']
  else if c = '>' then ['&', 'g', 't', ';']
  else [c]

/-- Escaping a string, not in attribute mode. -/
def escape (l : List Char) : List Char := l.flatMap escapeChar

/-- Escaping a string in attribute mode, one character at a time. -/
def escapeAttrChar (c : Char) : List Char :=
  if c = '"' then ['&', 'q', 'u', 'o', 't', ';'] else escapeChar c

/-- Escaping a string in attribute mode. -/
def escapeAttr (l : List Char) : List Char := l.flatMap escapeAttrChar

def escapeString (s : String) : String := String.ofList (escape s.toList)
def escapeAttrString (s : String) : String := String.ofList (escapeAttr s.toList)

/-! ## No delimiter survives -/

theorem escapeChar_no_delim (c d : Char) (hd : isDelim d = true) : d ∉ escapeChar c := by
  have hd' : d = '<' ∨ d = '>' := by
    simp only [isDelim, Bool.or_eq_true, beq_iff_eq] at hd
    exact hd
  unfold escapeChar
  split
  · rcases hd' with rfl | rfl <;> decide
  split
  · rcases hd' with rfl | rfl <;> decide
  split
  · rcases hd' with rfl | rfl <;> decide
  split
  · rcases hd' with rfl | rfl <;> decide
  · rename_i _ _ h3 h4
    simp only [List.mem_singleton]
    rcases hd' with rfl | rfl
    · exact fun h => h3 h.symm
    · exact fun h => h4 h.symm

theorem escape_no_delim (l : List Char) (d : Char) (hd : isDelim d = true) : d ∉ escape l := by
  simp only [escape, List.mem_flatMap, not_exists, not_and]
  exact fun c _ hc => escapeChar_no_delim c d hd hc

/-- No character of an escaped run is a delimiter. -/
theorem escape_mem_ne {l : List Char} {x d : Char} (hd : isDelim d = true)
    (hx : x ∈ escape l) : x ≠ d := fun he => escape_no_delim l d hd (he ▸ hx)

theorem escapeChar_no_quote (c : Char) (hc : c ≠ '"') : '"' ∉ escapeChar c := by
  unfold escapeChar
  split
  · decide
  split
  · decide
  split
  · decide
  split
  · decide
  · simp only [List.mem_singleton]
    exact fun h => hc h.symm

theorem escapeAttrChar_no_delim (c d : Char) (hd : isAttrDelim d = true) : d ∉ escapeAttrChar c := by
  have hd' : d = '<' ∨ d = '>' ∨ d = '"' := by
    simp only [isAttrDelim, Bool.or_eq_true, beq_iff_eq] at hd
    rcases hd with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  unfold escapeAttrChar
  split
  · rcases hd' with rfl | rfl | rfl <;> decide
  · rename_i hq
    rcases hd' with rfl | rfl | rfl
    · exact escapeChar_no_delim c '<' (by decide)
    · exact escapeChar_no_delim c '>' (by decide)
    · exact escapeChar_no_quote c hq

theorem escapeAttr_no_delim (l : List Char) (d : Char) (hd : isAttrDelim d = true) :
    d ∉ escapeAttr l := by
  simp only [escapeAttr, List.mem_flatMap, not_exists, not_and]
  exact fun c _ hc => escapeAttrChar_no_delim c d hd hc

theorem escapeAttr_mem_ne {l : List Char} {x d : Char} (hd : isAttrDelim d = true)
    (hx : x ∈ escapeAttr l) : x ≠ d := fun he => escapeAttr_no_delim l d hd (he ▸ hx)

/-! ## The decoder for the escaper's own alphabet -/

/-- Structural in its argument: every recursive call is on a proper tail. -/
def unescape : List Char → List Char
  | [] => []
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescape rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescape rest
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescape rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescape rest
  | '&' :: 'n' :: 'b' :: 's' :: 'p' :: ';' :: rest => nbsp :: unescape rest
  | c :: rest => c :: unescape rest

/-- Outside a reference, the decoder copies a character and recurses on the
tail. Every case of the decoder that does otherwise begins with `&`. -/
theorem unescape_cons_of_ne_amp {c : Char} (h : c ≠ '&') (t : List Char) :
    unescape (c :: t) = c :: unescape t := by
  rw [unescape]
  all_goals exact fun _ hc _ => h hc

/-- The decoder recovers the character the escaper replaced, whatever
follows. -/
theorem unescape_escapeChar (c : Char) (rest : List Char) :
    unescape (escapeChar c ++ rest) = c :: unescape rest := by
  unfold escapeChar
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  split
  · rename_i h; subst h; rfl
  · rename_i h1 _ _ _
    exact unescape_cons_of_ne_amp h1 rest

theorem unescape_escape (l : List Char) : unescape (escape l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escape, List.flatMap_cons] at *
    rw [unescape_escapeChar, ih]

theorem escape_injective {l₁ l₂ : List Char} (h : escape l₁ = escape l₂) : l₁ = l₂ := by
  have hd := congrArg unescape h
  rwa [unescape_escape, unescape_escape] at hd

theorem unescape_escapeAttrChar (c : Char) (rest : List Char) :
    unescape (escapeAttrChar c ++ rest) = c :: unescape rest := by
  unfold escapeAttrChar
  split
  · rename_i h; subst h; rfl
  · exact unescape_escapeChar c rest

theorem unescape_escapeAttr (l : List Char) : unescape (escapeAttr l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [escapeAttr, List.flatMap_cons] at *
    rw [unescape_escapeAttrChar, ih]

theorem escapeAttr_injective {l₁ l₂ : List Char} (h : escapeAttr l₁ = escapeAttr l₂) : l₁ = l₂ := by
  have hd := congrArg unescape h
  rwa [unescape_escapeAttr, unescape_escapeAttr] at hd

/-- No character escapes to nothing. -/
theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar
  split
  · exact List.cons_ne_nil _ _
  split
  · exact List.cons_ne_nil _ _
  split
  · exact List.cons_ne_nil _ _
  split <;> exact List.cons_ne_nil _ _

/-- A nonempty run escapes to a nonempty run. -/
theorem escape_ne_nil {l : List Char} (h : l ≠ []) : escape l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons c cs =>
    simp only [escape, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
    exact fun hc => absurd hc (escapeChar_ne_nil c)

/-! ## The `String` boundary -/

theorem toList_escapeString (s : String) : (escapeString s).toList = escape s.toList := by
  simp only [escapeString, String.toList_ofList]

theorem toList_escapeAttrString (s : String) : (escapeAttrString s).toList = escapeAttr s.toList := by
  simp only [escapeAttrString, String.toList_ofList]

theorem escapeString_injective {s t : String} (h : escapeString s = escapeString t) : s = t := by
  apply String.toList_injective
  exact escape_injective (by rw [← toList_escapeString, ← toList_escapeString, h])

end Whatwg.Html.Print
