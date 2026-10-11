import Whatwg.Html.Print.Escape
import Whatwg.Html.Node.Erasure
import Whatwg.Html.Node.Walk
import Whatwg.Html.Svg

/-!
# Whatwg.Html.Print.Render

The serializer, following the HTML Standard's "serializing HTML fragments"
algorithm at the pin (`source` line 149330; slice H7.2, ruling HP-12):
`<name attrs>` with each attribute as ` name="value"` in attribute mode; no
end tag and no children for a void element; the children then `</name>`
otherwise; the text children of `style`, `script`, `xmp`, `iframe`,
`noembed`, `noframes` and `plaintext` written literally; text escaped
otherwise; a comment as `<!--data-->` with its data literal. The `noscript`
case, which depends on whether scripting is enabled, is read as escaped.
`renderDoc` prefixes the document type `<!DOCTYPE html>`. TyXML's `Make`,
which the H4 printer followed, wrote `<br />` and escaped comment data; both
are gone.

## The namespace

Since slice S3d of `docs/SVG-PACKAGE-PLAN.md` the printer is the third
algebra of the walk of `Whatwg.Html.Node.Walk` (ruling SV-23). Its state,
`PrintState`, is the namespace of the node and one bit: whether the node's
parent is an HTML raw-text element. The namespace moves by `Ns.step`, the
automaton the checker's transition agrees with (`Pos.child_ns`), so the
printer and the checker cannot disagree about a node's namespace.

The void rule and the raw-text rule of the algorithm are stated of HTML
elements. So in the SVG namespace no element is void and no text is written
literally (ruling SV-17): `<rect></rect>` has its end tag, and the text of an
SVG `style` or `script` is escaped (`renderIn_text_no_delim_of_svg`). The
rules return below an integration point.

## What is proved

Escaping soundness is inherited from `Whatwg.Html.Print.Escape`. Printer
injectivity is **false** on `RawNode` and two counterexamples prove it:
`text "&"` and `entity "amp"` print identically, and a text run split in two
prints as the single run. Injectivity is therefore stated over `wf`: no
entity node, no empty text run, no text run directly followed by another,
names spelled from `nameChar`, a void element with no children, a raw-text
element with at most one text child free of `<`, and a comment free of `>`.
`decodeNode?` is a budgeted decoder for the printer's own output, not an
HTML parser (ruling HP-8), and `decode_render` says it inverts the printer
on `wf`, whence `renderChars_injective_of_wf` and `render_injective_of_wf`.
`wf` and the decoder carry the namespace, and the three statements hold for
every well-formed tree, with SVG subtrees or without (nodes P1 and P3 of the
plan's section 6).
-/

namespace Whatwg.Html.Print

open Whatwg.Html (RawNode Walk)
open Whatwg.Html.Schema (Tag)
open Whatwg.Html.Content (forall_tag_of_all Ns)

/-! ## The void and raw-text names, read from the schema -/

/-- The markup names of the standard's void elements, derived from the
schema's `Tag.isVoid` and `Tag.markupName` rather than retyped. -/
def isVoidName (s : String) : Bool :=
  Tag.all.any (fun t => t.isVoid && t.markupName == some s)

/-- The thirteen names of the standard's void-elements list. -/
theorem isVoidName_eq :
    ∀ s ∈ ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
           "source", "track", "wbr"],
      isVoidName s = true := by decide

theorem isVoidName_div : isVoidName "div" = false := by decide

/-- The elements whose text children the algorithm writes literally. -/
def isRawText (s : String) : Bool :=
  ["style", "script", "xmp", "iframe", "noembed", "noframes", "plaintext"].contains s

/-! ## The print state -/

/-- The element is void where it stands: an HTML element of the void list. -/
def voidIn (ns : Ns) (name : String) : Bool := ns == .html && isVoidName name

/-- The element's text children are written literally: an HTML raw-text element. -/
def rawIn (ns : Ns) (name : String) : Bool := ns == .html && isRawText name

/-- The printer's state at a node: the node's namespace, and whether its parent is an HTML
raw-text element. -/
structure PrintState where
  ns : Ns
  raw : Bool
  deriving DecidableEq, Repr, Inhabited

namespace PrintState

/-- The state at the root of an HTML tree. -/
def root : PrintState := ⟨.html, false⟩

/-- The state of an element's children. -/
def step (s : PrintState) (name : String) : PrintState := ⟨s.ns.step name, rawIn s.ns name⟩

end PrintState

/-! ## The printer -/

/-- One attribute: a leading space, the name, `=`, and the value escaped in
attribute mode in double quotes. -/
def renderAttr (attr : String × String) : List Char :=
  ' ' :: (attr.1.toList ++ '=' :: '"' :: (escapeAttr attr.2.toList ++ ['"']))

def renderAttrs (attrs : List (String × String)) : List Char := attrs.flatMap renderAttr

def renderClose (name : String) : List Char := '<' :: '/' :: (name.toList ++ ['>'])

/-- The serializer as an algebra of the walk. -/
def printWalk : Walk PrintState (List Char) where
  step := PrintState.step
  element := fun s name attrs _ results =>
    if voidIn s.ns name then '<' :: (name.toList ++ renderAttrs attrs ++ ['>'])
    else '<' :: (name.toList ++ renderAttrs attrs ++ '>' :: (results.flatten ++ renderClose name))
  text := fun s content => if s.raw then content.toList else escape content.toList
  entity := fun _ name => '&' :: (name.toList ++ [';'])
  comment := fun _ content => '<' :: '!' :: '-' :: '-' :: (content.toList ++ ['-', '-', '>'])

/-- The serializer at a state, at `List Char`. -/
def renderIn (s : PrintState) (node : RawNode) : List Char := printWalk.run s node

/-- A forest at a state, in order and with no separator. -/
def renderAllIn (s : PrintState) (nodes : List RawNode) : List Char :=
  (printWalk.runAll s nodes).flatten

/-- The serializer at `List Char`, from the root of an HTML tree. -/
def renderChars (node : RawNode) : List Char := renderIn .root node

/-- A forest, in order and with no separator. -/
def renderCharsList (nodes : List RawNode) : List Char := renderAllIn .root nodes

def render (node : RawNode) : String := String.ofList (renderChars node)
def renderList (nodes : List RawNode) : String := String.ofList (renderCharsList nodes)

/-- The document type, as the algorithm writes a `DocumentType` named `html`. -/
def doctype : String := "<!DOCTYPE html>"

/-- A whole document: the document type, then the tree, with nothing between. -/
def renderDoc (node : RawNode) : String := doctype ++ render node

/-! ## The printer at each kind of node -/

theorem renderIn_element (s : PrintState) (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    renderIn s (.element name attrs children) =
      if voidIn s.ns name then '<' :: (name.toList ++ renderAttrs attrs ++ ['>'])
      else '<' :: (name.toList ++ renderAttrs attrs
        ++ '>' :: (renderAllIn (s.step name) children ++ renderClose name)) := by
  simp only [renderIn, renderAllIn, Walk.run_element, printWalk]

theorem renderIn_text (s : PrintState) (content : String) :
    renderIn s (.text content) = if s.raw then content.toList else escape content.toList := by
  simp only [renderIn, Walk.run, printWalk]

theorem renderIn_entity (s : PrintState) (name : String) :
    renderIn s (.entity name) = '&' :: (name.toList ++ [';']) := by
  simp only [renderIn, Walk.run, printWalk]

theorem renderIn_comment (s : PrintState) (content : String) :
    renderIn s (.comment content)
      = '<' :: '!' :: '-' :: '-' :: (content.toList ++ ['-', '-', '>']) := by
  simp only [renderIn, Walk.run, printWalk]

theorem renderAllIn_nil (s : PrintState) : renderAllIn s [] = [] := by
  simp only [renderAllIn, Walk.runAll_nil, List.flatten_nil]

theorem renderAllIn_cons (s : PrintState) (node : RawNode) (rest : List RawNode) :
    renderAllIn s (node :: rest) = renderIn s node ++ renderAllIn s rest := by
  simp only [renderAllIn, renderIn, Walk.runAll_cons, List.flatten_cons]

/-! ## The `String` boundary -/

theorem toList_render (node : RawNode) : (render node).toList = renderChars node := by
  simp [render]

theorem toList_renderList (nodes : List RawNode) :
    (renderList nodes).toList = renderCharsList nodes := by
  simp [renderList]

theorem toList_renderDoc (node : RawNode) :
    (renderDoc node).toList = doctype.toList ++ renderChars node := by
  simp [renderDoc, toList_render]

/-! ## The text-run statement, lifted from the escaper -/

theorem renderChars_text_no_delim (content : String) (d : Char) (hd : isDelim d = true) :
    d ∉ renderChars (.text content) := by
  rw [renderChars, renderIn_text]
  exact escape_no_delim content.toList d hd

/-- Node P2: a text child of an SVG element is escaped, whatever the element is. No delimiter
character survives, under an SVG `style` or `script` too. -/
theorem renderIn_text_no_delim_of_svg (raw : Bool) (name content : String) (d : Char)
    (hd : isDelim d = true) :
    d ∉ renderIn (PrintState.step ⟨.svg, raw⟩ name) (.text content) := by
  rw [renderIn_text]
  exact escape_no_delim content.toList d hd

theorem renderAttr_value_no_quote (attr : String × String) :
    '"' ∉ escapeAttr attr.2.toList := escapeAttr_no_delim attr.2.toList _ (by decide)

/-! ## The printer is not injective on `RawNode` -/

theorem renderChars_not_injective :
    ∃ a b : RawNode, a ≠ b ∧ renderChars a = renderChars b :=
  ⟨.text "&", .entity "amp", fun h => RawNode.noConfusion h, by decide⟩

theorem renderCharsList_not_injective :
    ∃ a b : List RawNode, a ≠ b ∧ renderCharsList a = renderCharsList b :=
  ⟨[.text "a", .text "b"], [.text "ab"], by simp, by decide⟩

/-! ## Well-formed trees -/

/-- The characters a markup name is made of. -/
def nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == ':' || c == '_'

def nameOk (s : String) : Bool := !s.toList.isEmpty && s.toList.all nameChar

theorem nameOk_markupName : ∀ t : Tag, (t.markupName.elim true nameOk) = true :=
  forall_tag_of_all (fun t => t.markupName.elim true nameOk) (by decide)

theorem nameOk_of_markupName {t : Tag} {m : String} (h : t.markupName = some m) :
    nameOk m = true := by
  have ht := nameOk_markupName t
  rw [h] at ht
  exact ht

theorem nameChar_ne {c d : Char} (h : nameChar c = true) (hd : nameChar d = false) : c ≠ d := by
  intro he
  rw [he, hd] at h
  exact Bool.noConfusion h

def startsMarkup : RawNode → Bool
  | .element _ _ _ => true
  | .comment _ => true
  | .text _ => false
  | .entity _ => false

def textFollowOk : RawNode → List RawNode → Bool
  | .text _, node :: _ => startsMarkup node
  | .text _, [] => true
  | _, _ => true

/-- The children a raw-text element may have for the decoder to invert the
printer: none, or one nonempty text run free of `<`. -/
def rawChildrenOk : List RawNode → Bool
  | [] => true
  | [.text content] => !content.toList.isEmpty && content.toList.all (· != '<')
  | _ => false

mutual

/-- The trees the decoder below inverts, at a print state. -/
def wfIn (s : PrintState) : RawNode → Bool
  | .element name attrs children =>
      nameOk name && attrs.all (fun attr => nameOk attr.1) &&
        (if voidIn s.ns name then children.isEmpty
         else if rawIn s.ns name then rawChildrenOk children
         else wfAllIn (s.step name) children)
  | .text content => !content.toList.isEmpty
  | .entity _ => false
  | .comment content => content.toList.all (· != '>')

def wfAllIn (s : PrintState) : List RawNode → Bool
  | [] => true
  | node :: rest => wfIn s node && wfAllIn s rest && textFollowOk node rest

end

/-- The trees the decoder inverts, from the root of an HTML tree. -/
def wf (node : RawNode) : Bool := wfIn .root node

def wfList (nodes : List RawNode) : Bool := wfAllIn .root nodes

/-! ## Scanning -/

/-- The longest prefix whose characters satisfy `p`, and the rest. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if p c then
        let tail := spanChars p rest
        (c :: tail.1, tail.2)
      else ([], c :: rest)

/-- A scan stops exactly where the next character fails the predicate. -/
theorem spanChars_append {p : Char → Bool} {l rest : List Char}
    (hl : ∀ c ∈ l, p c = true) (hr : ∀ c t, rest = c :: t → p c = false) :
    spanChars p (l ++ rest) = (l, rest) := by
  induction l with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c t => simp [spanChars, hr c t rfl]
  | cons c t ih =>
    have hc : p c = true := hl c (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx]))
    simp [spanChars, hc, ih']

/-! ## The decoder for the printer's own output

`decodeNodeIn?` accepts the sublanguage `renderIn` emits and nothing else.
It is not an HTML parser (ruling HP-8). The `Nat` argument is a recursion
budget; `weight` always suffices. The `Ns` argument is the namespace of the
node, which decides the void rule and the raw-text rule as the printer does. -/

mutual

/-- The decoding budget of a node. -/
def weight : RawNode → Nat
  | .element _ attrs children => 1 + attrs.length + weightList children
  | .text _ => 1
  | .entity _ => 1
  | .comment _ => 1

/-- The decoding budget of a forest. -/
def weightList : List RawNode → Nat
  | [] => 1
  | node :: rest => 1 + weight node + weightList rest

end

/-- The characters that end a markup name. -/
def isNameChar (c : Char) : Bool := c != ' ' && c != '/' && c != '>'

/-- Strip a literal prefix, or fail. Every literal the decoder expects is
consumed through this function, so that both its success and its failure
reduce by `simp`. -/
def afterPrefix : List Char → List Char → Option (List Char)
  | [], l => some l
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then afterPrefix ps cs else none

/-- A literal prefix is stripped from the list it was prepended to. -/
theorem afterPrefix_append (p l : List Char) : afterPrefix p (p ++ l) = some l := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [afterPrefix, ih]

/-- The attribute list of a start tag: repeated ` name="value"` until `>`. -/
def decodeAttrs : Nat → List Char → Option (List (String × String) × List Char)
  | 0, l => some ([], l)
  | fuel + 1, l =>
      match afterPrefix [' '] l with
      | none => some ([], l)
      | some tail =>
          let scanned := spanChars (fun c => c != '=') tail
          match afterPrefix ['=', '"'] scanned.2 with
          | none => none
          | some tail₁ =>
              let value := spanChars (fun c => c != '"') tail₁
              match afterPrefix ['"'] value.2 with
              | none => none
              | some tail₂ =>
                  match decodeAttrs fuel tail₂ with
                  | none => none
                  | some (attrs, tail₃) =>
                      some ((String.ofList scanned.1, String.ofList (unescape value.1)) :: attrs, tail₃)

/-- The closing tag `</name>` at the head of the input, or fail. -/
def decodeClose (name : List Char) : List Char → Option (List Char)
  | l =>
      match afterPrefix ['<', '/'] l with
      | none => none
      | some tail =>
          let closing := spanChars (fun c => c != '>') tail
          match afterPrefix ['>'] closing.2 with
          | none => none
          | some tail₁ => if closing.1 = name then some tail₁ else none

mutual

/-- One node of the printer's output in a namespace, and what follows it. -/
def decodeNodeIn? : Nat → Ns → List Char → Option (RawNode × List Char)
  | 0, _, _ => none
  | fuel + 1, ns, l =>
      match afterPrefix ['<', '!', '-', '-'] l with
      | some tail =>
          let scanned := spanChars (fun c => c != '>') tail
          match afterPrefix ['>'] scanned.2 with
          | none => none
          | some tail₁ => some (.comment (String.ofList scanned.1.dropLast.dropLast), tail₁)
      | none =>
          match afterPrefix ['<'] l with
          | some tail =>
              let name := spanChars isNameChar tail
              match decodeAttrs fuel name.2 with
              | none => none
              | some (attrs, tail₁) =>
                  match afterPrefix ['>'] tail₁ with
                  | none => none
                  | some tail₂ =>
                      if voidIn ns (String.ofList name.1) then
                        some (.element (String.ofList name.1) attrs [], tail₂)
                      else if rawIn ns (String.ofList name.1) then
                        let raw := spanChars (fun c => c != '<') tail₂
                        match decodeClose name.1 raw.2 with
                        | none => none
                        | some tail₃ =>
                            some (.element (String.ofList name.1) attrs
                              (if raw.1.isEmpty then [] else [.text (String.ofList raw.1)]), tail₃)
                      else
                        match decodeNodesIn? fuel (ns.step (String.ofList name.1)) tail₂ with
                        | none => none
                        | some (children, tail₃) =>
                            match decodeClose name.1 tail₃ with
                            | none => none
                            | some tail₄ => some (.element (String.ofList name.1) attrs children, tail₄)
          | none =>
              let scanned := spanChars (fun c => c != '<') l
              if scanned.1.isEmpty then none
              else some (.text (String.ofList (unescape scanned.1)), scanned.2)

/-- The children of an element in a namespace: nodes until the closing tag or the end. -/
def decodeNodesIn? : Nat → Ns → List Char → Option (List RawNode × List Char)
  | 0, _, _ => none
  | fuel + 1, ns, l =>
      match afterPrefix ['<', '/'] l with
      | some tail => some ([], '<' :: '/' :: tail)
      | none =>
          if l.isEmpty then some ([], l)
          else
            match decodeNodeIn? fuel ns l with
            | none => none
            | some (node, tail) =>
                match decodeNodesIn? fuel ns tail with
                | none => none
                | some (nodes, tail₁) => some (node :: nodes, tail₁)

end

/-- One node of the printer's output from the root of an HTML tree, and what follows it. -/
def decodeNode? (fuel : Nat) (l : List Char) : Option (RawNode × List Char) :=
  decodeNodeIn? fuel .html l

def decode? (l : List Char) : Option (RawNode × List Char) := decodeNode? l.length l

/-! ## The lemmas the round trip runs on -/

/-- The empty prefix consumes nothing. -/
theorem afterPrefix_nil (l : List Char) : afterPrefix [] l = some l := rfl

/-- A matching first character is consumed. -/
theorem afterPrefix_cons_self (c : Char) (ps l : List Char) :
    afterPrefix (c :: ps) (c :: l) = afterPrefix ps l := by simp [afterPrefix]

/-- A literal prefix fails as soon as its first character does. -/
theorem afterPrefix_head_ne {c : Char} {ps l r : List Char} (hl : l ≠ [])
    (h : ∀ x ∈ l, x ≠ c) : afterPrefix (c :: ps) (l ++ r) = none := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d t =>
    have hcd : ¬ c = d := fun hc => (h d (by simp)) hc.symm
    simp [afterPrefix, hcd]

/-- A `nameOk` name is a nonempty run of `nameChar`s. -/
theorem nameOk_facts {s : String} (h : nameOk s = true) :
    s.toList ≠ [] ∧ ∀ x ∈ s.toList, nameChar x = true := by
  simp only [nameOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact h

/-- A markup name is scanned in full: none of its characters ends a name. -/
theorem nameChar_isNameChar {c : Char} (h : nameChar c = true) : isNameChar c = true := by
  simp only [isNameChar, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> exact nameChar_ne h (by decide)

/-- The rendering of an attribute list either is empty or begins with the
space that separates the first attribute from the tag name. -/
theorem renderAttrs_head_not_name (attrs : List (String × String)) {r : List Char}
    (hr : ∀ c t, r = c :: t → isNameChar c = false) :
    ∀ c t, renderAttrs attrs ++ r = c :: t → isNameChar c = false := by
  cases attrs with
  | nil => simpa [renderAttrs] using hr
  | cons a as =>
    intro c t hct
    simp only [renderAttrs, List.flatMap_cons, renderAttr, List.cons_append] at hct
    have hc : c = ' ' := by injection hct with h _; exact h.symm
    subst hc
    decide

/-- A node whose rendering begins with `<`, at any state. -/
theorem renderIn_markup_head (s : PrintState) {node : RawNode} (h : startsMarkup node = true) :
    ∃ t, renderIn s node = '<' :: t := by
  cases node with
  | element name attrs children =>
    rw [renderIn_element]
    by_cases hv : voidIn s.ns name = true
    · rw [if_pos hv]
      exact ⟨_, rfl⟩
    · rw [if_neg hv]
      exact ⟨_, rfl⟩
  | comment content => exact ⟨_, renderIn_comment s content⟩
  | text content => simp [startsMarkup] at h
  | entity name => simp [startsMarkup] at h

/-- Every node costs at least one unit of decoding budget. -/
theorem one_le_weight (node : RawNode) : 1 ≤ weight node := by
  cases node <;> simp only [weight] <;> omega

/-- Every forest costs at least one unit of decoding budget. -/
theorem one_le_weightList (nodes : List RawNode) : 1 ≤ weightList nodes := by
  cases nodes <;> simp only [weightList] <;> omega

/-! ## The attribute list decodes -/

/-- The attribute decoder inverts the printer on names spelled from
`nameChar`, whenever what follows the list is the `>` that ends a start
tag. -/
theorem decodeAttrs_render : ∀ (attrs : List (String × String)) (fuel : Nat) (rest : List Char),
    attrs.all (fun attr => nameOk attr.1) = true → attrs.length ≤ fuel →
    (∃ t, rest = '>' :: t) →
    decodeAttrs fuel (renderAttrs attrs ++ rest) = some (attrs, rest) := by
  intro attrs
  induction attrs with
  | nil =>
    intro fuel rest _ _ hrest
    cases fuel with
    | zero => simp [decodeAttrs, renderAttrs]
    | succ f =>
      obtain ⟨t, rfl⟩ := hrest
      simp [decodeAttrs, renderAttrs, afterPrefix]
  | cons a as ih =>
    intro fuel rest hall hlen hrest
    cases fuel with
    | zero => simp at hlen
    | succ f =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hname, hnil⟩ := nameOk_facts hall.1
      have hlen' : as.length ≤ f := by simpa using hlen
      have ihs := ih f rest hall.2 hlen' hrest
      have hinput : renderAttrs (a :: as) ++ rest
          = ' ' :: (a.1.toList ++ ('=' :: '"'
              :: (escapeAttr a.2.toList ++ ('"' :: (renderAttrs as ++ rest))))) := by
        simp [renderAttrs, renderAttr]
      have hspan₁ : spanChars (fun c => c != '=')
            (a.1.toList ++ ('=' :: '"' :: (escapeAttr a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))))
          = (a.1.toList, '=' :: '"' :: (escapeAttr a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))) :=
        spanChars_append (fun x hx => by simpa using nameChar_ne (hnil x hx) (by decide))
          (fun c t hct => by injection hct with h _; subst h; decide)
      have hspan₂ : spanChars (fun c => c != '"')
            (escapeAttr a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))
          = (escapeAttr a.2.toList, '"' :: (renderAttrs as ++ rest)) :=
        spanChars_append
          (fun x hx => by simpa using escapeAttr_mem_ne (d := '"') (by decide) hx)
          (fun c t hct => by injection hct with h _; subst h; decide)
      rw [hinput, decodeAttrs, afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [hspan₁]
      dsimp only
      rw [afterPrefix_cons_self, afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [hspan₂]
      dsimp only
      rw [afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [ihs]
      dsimp only
      simp [unescape_escapeAttr]

/-- A literal prefix fails on a different first character. -/
theorem afterPrefix_cons_ne {c d : Char} (h : ¬ c = d) (ps l : List Char) :
    afterPrefix (c :: ps) (d :: l) = none := by simp [afterPrefix, h]

/-- A nonempty literal prefix fails on the empty list. -/
theorem afterPrefix_nil_right (c : Char) (ps : List Char) : afterPrefix (c :: ps) [] = none := rfl

/-- The closing tag decodes after any well-spelled name. -/
theorem decodeClose_render {name : String} (h : nameOk name = true) (rest : List Char) :
    decodeClose name.toList (renderClose name ++ rest) = some rest := by
  obtain ⟨_, hall⟩ := nameOk_facts h
  have hspan : spanChars (fun c => c != '>') (name.toList ++ ('>' :: rest)) = (name.toList, '>' :: rest) :=
    spanChars_append (fun x hx => by simpa using nameChar_ne (hall x hx) (by decide))
      (fun c t hct => by injection hct with h _; subst h; decide)
  have hinput : renderClose name ++ rest = '<' :: '/' :: (name.toList ++ ('>' :: rest)) := by
    simp [renderClose]
  rw [hinput, decodeClose, afterPrefix_cons_self, afterPrefix_cons_self, afterPrefix_nil]
  dsimp only
  rw [hspan]
  dsimp only
  rw [afterPrefix_cons_self, afterPrefix_nil]
  simp

/-- A well-formed node renders to something. -/
theorem renderIn_ne_nil (s : PrintState) {node : RawNode} (h : wfIn s node = true) :
    renderIn s node ≠ [] := by
  cases node with
  | element name attrs children =>
    by_cases hv : voidIn s.ns name = true <;> simp [renderIn_element, hv]
  | text content =>
    have hne : content.toList ≠ [] := by simpa [wfIn] using h
    rw [renderIn_text]
    cases s.raw with
    | false => simpa using escape_ne_nil hne
    | true => simpa using hne
  | entity name => simp [wfIn] at h
  | comment content => simp [renderIn_comment]

/-- No well-formed node's rendering begins with a closing tag, where text is escaped. -/
theorem afterPrefix_close_ne (s : PrintState) (hs : s.raw = false) {node : RawNode}
    (h : wfIn s node = true) (r : List Char) :
    afterPrefix ['<', '/'] (renderIn s node ++ r) = none := by
  cases node with
  | element name attrs children =>
    simp only [wfIn, Bool.and_eq_true] at h
    obtain ⟨hnnil, hnall⟩ := nameOk_facts h.1.1
    have hne : ∀ x ∈ name.toList, x ≠ '/' := fun x hx => nameChar_ne (hnall x hx) (by decide)
    by_cases hv : voidIn s.ns name = true
    · have : renderIn s (RawNode.element name attrs children) ++ r
          = '<' :: (name.toList ++ (renderAttrs attrs ++ (['>'] ++ r))) := by
        simp [renderIn_element, hv]
      rw [this, afterPrefix_cons_self]
      exact afterPrefix_head_ne hnnil hne
    · have : renderIn s (RawNode.element name attrs children) ++ r
          = '<' :: (name.toList ++ (renderAttrs attrs
              ++ ('>' :: (renderAllIn (s.step name) children ++ renderClose name ++ r)))) := by
        simp [renderIn_element, hv]
      rw [this, afterPrefix_cons_self]
      exact afterPrefix_head_ne hnnil hne
  | text content =>
    have hne : content.toList ≠ [] := by simpa [wfIn] using h
    have : renderIn s (RawNode.text content) ++ r = escape content.toList ++ r := by
      simp [renderIn_text, hs]
    rw [this]
    exact afterPrefix_head_ne (escape_ne_nil hne)
      (fun x hx => escape_mem_ne (d := '<') (by decide) hx)
  | entity name => simp [wfIn] at h
  | comment content =>
    have : renderIn s (RawNode.comment content) ++ r
        = '<' :: ('!' :: ('-' :: '-' :: (content.toList ++ ['-', '-', '>'] ++ r))) := by
      simp [renderIn_comment]
    rw [this, afterPrefix_cons_self, afterPrefix_cons_ne (by decide)]

/-- The children of a raw-text element render to a run free of `<`, and back. -/
theorem rawChildrenOk_facts (ns : Ns) {children : List RawNode} (h : rawChildrenOk children = true) :
    (∀ x ∈ renderAllIn ⟨ns, true⟩ children, x ≠ '<') ∧
    (if (renderAllIn ⟨ns, true⟩ children).isEmpty then ([] : List RawNode)
      else [RawNode.text (String.ofList (renderAllIn ⟨ns, true⟩ children))]) = children := by
  match children, h with
  | [], _ => simp [renderAllIn_nil]
  | [.text content], h =>
    simp only [rawChildrenOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, bne_iff_ne, ne_eq] at h
    have hrun : renderAllIn ⟨ns, true⟩ [RawNode.text content] = content.toList := by
      simp [renderAllIn_cons, renderAllIn_nil, renderIn_text]
    rw [hrun]
    refine ⟨fun x hx => h.2 x hx, ?_⟩
    simp [List.isEmpty_iff, h.1]

/-! ## The round trip -/

/-- Node P1: the decoder inverts the printer on every well-formed tree, at every state whose
text is escaped. The tree may hold SVG subtrees. -/
theorem decode_render : ∀ fuel : Nat,
    (∀ (s : PrintState) (node : RawNode) (rest : List Char), s.raw = false →
        wfIn s node = true → weight node ≤ fuel →
        (∀ content, node = .text content → (rest = [] ∨ ∃ t, rest = '<' :: t)) →
        decodeNodeIn? fuel s.ns (renderIn s node ++ rest) = some (node, rest))
      ∧ (∀ (s : PrintState) (nodes : List RawNode) (rest : List Char), s.raw = false →
        wfAllIn s nodes = true → weightList nodes ≤ fuel →
        (rest = [] ∨ ∃ t, rest = '<' :: '/' :: t) →
        decodeNodesIn? fuel s.ns (renderAllIn s nodes ++ rest) = some (nodes, rest)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro s node _ _ _ hweight _
      have := one_le_weight node
      omega
    · intro s nodes _ _ _ hweight _
      have := one_le_weightList nodes
      omega
  | succ f ih =>
    refine ⟨?_, ?_⟩
    · intro s node rest hs hwf hweight hrest
      cases node with
      | entity name => simp [wfIn] at hwf
      | text content =>
        have hne : content.toList ≠ [] := by simpa [wfIn] using hwf
        have hesc : escape content.toList ≠ [] := escape_ne_nil hne
        have hrest' := hrest content rfl
        have hspan : spanChars (fun c => c != '<') (escape content.toList ++ rest)
            = (escape content.toList, rest) :=
          spanChars_append (fun x hx => by simpa using escape_mem_ne (d := '<') (by decide) hx)
            (fun c t hct => by
              rcases hrest' with rfl | ⟨t', rfl⟩
              · exact absurd hct (by simp)
              · injection hct with h _; subst h; decide)
        have hinput : renderIn s (RawNode.text content) ++ rest
            = escape content.toList ++ rest := by simp [renderIn_text, hs]
        rw [hinput, decodeNodeIn?,
          afterPrefix_head_ne hesc (fun x hx => escape_mem_ne (d := '<') (by decide) hx)]
        dsimp only
        rw [afterPrefix_head_ne hesc (fun x hx => escape_mem_ne (d := '<') (by decide) hx)]
        dsimp only
        rw [hspan]
        dsimp only
        rw [if_neg (by simpa using hesc)]
        simp [unescape_escape]
      | comment content =>
        have hall : ∀ x ∈ content.toList, x ≠ '>' := by
          simp only [wfIn, List.all_eq_true, bne_iff_ne, ne_eq] at hwf
          exact hwf
        have hspan : spanChars (fun c => c != '>')
              ((content.toList ++ ['-', '-']) ++ ('>' :: rest))
            = (content.toList ++ ['-', '-'], '>' :: rest) :=
          spanChars_append
            (fun x hx => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with hx | (rfl | rfl)
              · simpa using hall x hx
              · decide
              · decide)
            (fun c t hct => by injection hct with h _; subst h; decide)
        have hdrop : (content.toList ++ ['-', '-']).dropLast.dropLast = content.toList := by
          rw [show content.toList ++ ['-', '-'] = (content.toList ++ ['-']) ++ ['-'] from by simp]
          rw [List.dropLast_concat, List.dropLast_concat]
        have hinput : renderIn s (RawNode.comment content) ++ rest
            = ['<', '!', '-', '-'] ++ ((content.toList ++ ['-', '-']) ++ ('>' :: rest)) := by
          simp [renderIn_comment]
        rw [hinput, decodeNodeIn?, afterPrefix_append]
        dsimp only
        rw [hspan]
        dsimp only
        rw [afterPrefix_cons_self, afterPrefix_nil]
        dsimp only
        rw [hdrop]
        simp
      | element name attrs children =>
        simp only [wfIn, Bool.and_eq_true] at hwf
        obtain ⟨⟨hname, hattrs⟩, hchildren⟩ := hwf
        obtain ⟨hnnil, hnall⟩ := nameOk_facts hname
        simp only [weight] at hweight
        have hlenattrs : attrs.length ≤ f := by
          have := one_le_weightList children
          omega
        have hwchildren : weightList children ≤ f := by omega
        have hnameSpan : ∀ r : List Char, (∀ c t, r = c :: t → isNameChar c = false) →
            spanChars isNameChar (name.toList ++ (renderAttrs attrs ++ r))
              = (name.toList, renderAttrs attrs ++ r) := fun r hr =>
          spanChars_append (fun x hx => nameChar_isNameChar (hnall x hx))
            (renderAttrs_head_not_name attrs hr)
        have hofList : String.ofList name.toList = name := by simp
        by_cases hv : voidIn s.ns name = true
        · have hnil : children = [] := by
            rw [if_pos hv] at hchildren
            simpa using hchildren
          have hinput : renderIn s (RawNode.element name attrs children) ++ rest
              = '<' :: (name.toList ++ (renderAttrs attrs ++ ('>' :: rest))) := by
            simp [renderIn_element, hv]
          rw [hinput, decodeNodeIn?, afterPrefix_cons_self,
            afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hnameSpan _ (fun c t hct => by injection hct with h _; subst h; decide)]
          dsimp only
          rw [decodeAttrs_render attrs f ('>' :: rest) hattrs hlenattrs ⟨rest, rfl⟩]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hofList, if_pos hv]
          simp [hnil]
        · rw [if_neg hv] at hchildren
          by_cases hr : rawIn s.ns name = true
          · rw [if_pos hr] at hchildren
            have hstep : s.step name = ⟨s.ns.step name, true⟩ := by
              simp only [PrintState.step, hr]
            obtain ⟨hraw, hback⟩ := rawChildrenOk_facts (s.ns.step name) hchildren
            have hinput : renderIn s (RawNode.element name attrs children) ++ rest
                = '<' :: (name.toList ++ (renderAttrs attrs
                    ++ ('>' :: (renderAllIn ⟨s.ns.step name, true⟩ children
                      ++ (renderClose name ++ rest))))) := by
              simp [renderIn_element, hv, hstep]
            have hspanRaw : spanChars (fun c => c != '<')
                  (renderAllIn ⟨s.ns.step name, true⟩ children ++ (renderClose name ++ rest))
                = (renderAllIn ⟨s.ns.step name, true⟩ children, renderClose name ++ rest) :=
              spanChars_append (fun x hx => by simpa using hraw x hx)
                (fun c t hct => by simp [renderClose] at hct; obtain ⟨h, _⟩ := hct; subst h; decide)
            rw [hinput, decodeNodeIn?, afterPrefix_cons_self,
              afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))]
            dsimp only
            rw [afterPrefix_cons_self, afterPrefix_nil]
            dsimp only
            rw [hnameSpan _ (fun c t hct => by injection hct with h _; subst h; decide)]
            dsimp only
            rw [decodeAttrs_render attrs f _ hattrs hlenattrs ⟨_, rfl⟩]
            dsimp only
            rw [afterPrefix_cons_self, afterPrefix_nil]
            dsimp only
            rw [hofList, if_neg hv, if_pos hr]
            rw [hspanRaw]
            dsimp only
            rw [decodeClose_render hname]
            dsimp only
            rw [hback]
          · rw [if_neg hr] at hchildren
            have hrf : rawIn s.ns name = false := Bool.eq_false_iff.mpr hr
            have hinput : renderIn s (RawNode.element name attrs children) ++ rest
                = '<' :: (name.toList ++ (renderAttrs attrs
                    ++ ('>' :: (renderAllIn (s.step name) children ++ (renderClose name ++ rest))))) := by
              simp [renderIn_element, hv]
            have hkids : decodeNodesIn? f (s.ns.step name)
                  (renderAllIn (s.step name) children ++ (renderClose name ++ rest))
                = some (children, renderClose name ++ rest) :=
              ih.2 (s.step name) children (renderClose name ++ rest) hrf hchildren hwchildren
                (Or.inr ⟨name.toList ++ ('>' :: rest), by simp [renderClose]⟩)
            rw [hinput, decodeNodeIn?, afterPrefix_cons_self,
              afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))]
            dsimp only
            rw [afterPrefix_cons_self, afterPrefix_nil]
            dsimp only
            rw [hnameSpan _ (fun c t hct => by injection hct with h _; subst h; decide)]
            dsimp only
            rw [decodeAttrs_render attrs f _ hattrs hlenattrs ⟨_, rfl⟩]
            dsimp only
            rw [afterPrefix_cons_self, afterPrefix_nil]
            dsimp only
            rw [hofList, if_neg hv, if_neg hr]
            rw [hkids]
            dsimp only
            rw [decodeClose_render hname]
    · intro s nodes rest hs hwf hweight hrest
      cases nodes with
      | nil =>
        rcases hrest with rfl | ⟨t, rfl⟩
        · rw [show renderAllIn s [] ++ ([] : List Char) = [] from by simp [renderAllIn_nil],
            decodeNodesIn?]
          rfl
        · rw [show renderAllIn s [] ++ ('<' :: '/' :: t) = ['<', '/'] ++ t from by
              simp [renderAllIn_nil],
            decodeNodesIn?, afterPrefix_append]
      | cons node tail =>
        simp only [wfAllIn, Bool.and_eq_true] at hwf
        obtain ⟨⟨hnode, htail⟩, hfollow⟩ := hwf
        simp only [weightList] at hweight
        have hwn : weight node ≤ f := by
          have := one_le_weightList tail
          omega
        have hwt : weightList tail ≤ f := by
          have := one_le_weight node
          omega
        have htext : ∀ content, node = .text content →
            (renderAllIn s tail ++ rest = []
              ∨ ∃ t, renderAllIn s tail ++ rest = '<' :: t) := by
          intro content hcontent
          cases tail with
          | nil =>
            rcases hrest with rfl | ⟨t, rfl⟩
            · exact Or.inl (by simp [renderAllIn_nil])
            · exact Or.inr ⟨'/' :: t, by simp [renderAllIn_nil]⟩
          | cons head' tail' =>
            subst hcontent
            simp only [textFollowOk] at hfollow
            obtain ⟨u, hu⟩ := renderIn_markup_head s hfollow
            exact Or.inr ⟨u ++ (renderAllIn s tail' ++ rest), by
              simp [renderAllIn_cons, hu]⟩
        have hnode' := ih.1 s node (renderAllIn s tail ++ rest) hs hnode hwn htext
        have htail' := ih.2 s tail rest hs htail hwt hrest
        have hinput : renderAllIn s (node :: tail) ++ rest
            = renderIn s node ++ (renderAllIn s tail ++ rest) := by
          simp [renderAllIn_cons]
        rw [hinput, decodeNodesIn?, afterPrefix_close_ne s hs hnode]
        dsimp only
        rw [if_neg (by
          simp only [List.isEmpty_iff]
          exact List.append_ne_nil_of_left_ne_nil (renderIn_ne_nil s hnode) _)]
        rw [hnode']
        dsimp only
        rw [htail']

theorem decodeNode?_renderChars {node : RawNode} (hwf : wf node = true) (fuel : Nat)
    (hfuel : weight node ≤ fuel) (rest : List Char)
    (hrest : ∀ content, node = .text content → (rest = [] ∨ ∃ t, rest = '<' :: t)) :
    decodeNode? fuel (renderChars node ++ rest) = some (node, rest) :=
  (decode_render fuel).1 .root node rest rfl hwf hfuel hrest

theorem decodeNode?_render {node : RawNode} (hwf : wf node = true) :
    decodeNode? (weight node) (renderChars node) = some (node, []) := by
  have h := (decode_render (weight node)).1 .root node [] rfl hwf (Nat.le_refl _)
    (fun _ _ => Or.inl rfl)
  rw [List.append_nil] at h
  exact h

/-- Node P3: the serializer is injective on the sublanguage `wf` names, with SVG subtrees or
without. -/
theorem renderChars_injective_of_wf {a b : RawNode} (ha : wf a = true) (hb : wf b = true)
    (h : renderChars a = renderChars b) : a = b := by
  have hfa := (decode_render (weight a + weight b)).1 .root a [] rfl ha (by omega)
    (fun _ _ => Or.inl rfl)
  have hfb := (decode_render (weight a + weight b)).1 .root b [] rfl hb (by omega)
    (fun _ _ => Or.inl rfl)
  have h' : renderIn .root a = renderIn .root b := h
  rw [h'] at hfa
  have heq : (some (a, []) : Option (RawNode × List Char)) = some (b, []) := hfa.symm.trans hfb
  simpa using heq

theorem render_injective_of_wf {a b : RawNode} (ha : wf a = true) (hb : wf b = true)
    (h : render a = render b) : a = b :=
  renderChars_injective_of_wf ha hb (by rw [← toList_render, ← toList_render, h])

end Whatwg.Html.Print

namespace Whatwg.Html

def Element.render {t : Schema.Tag} {ctx : Content.Ctx} (e : Element t ctx) : String :=
  Print.render e.toRaw

def Element.renderDoc {t : Schema.Tag} {ctx : Content.Ctx} (e : Element t ctx) : String :=
  Print.renderDoc e.toRaw

def Child.render {ctx : Content.Ctx} (c : Child ctx) : String := Print.render c.raw

theorem Element.render_eq {t : Schema.Tag} {ctx : Content.Ctx} (e : Element t ctx) :
    e.render = Print.render e.toRaw := rfl

theorem Child.render_eq {ctx : Content.Ctx} (c : Child ctx) :
    c.render = Print.render c.raw := rfl

end Whatwg.Html
