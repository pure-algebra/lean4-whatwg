/-!
# Whatwg.Html.Schema.Condition

The attribute conditions the HTML Standard puts on a category (slice H7.3,
ruling HP-13): "If the element has an href attribute: Interactive content.",
"If the type attribute is not in the Hidden state: Interactive content.".
`Condition.holds` decides one over an element's raw attributes; a condition
this module does not read (a children-based one, "allowed in the body") is
`always`, the conservative reading. The keyword value is compared ASCII
case-insensitively, as the standard compares it; attribute names exactly.
-/

namespace Whatwg.Html.Schema

/-- An attribute condition on a category. -/
inductive Condition where
  /-- The category holds unconditionally, or the sentence is not read. -/
  | always
  /-- The element has one of the named attributes. -/
  | hasAny (names : List String)
  /-- The named attribute is absent or its value is not the keyword. -/
  | attrNot (name value : String)
  deriving DecidableEq, Repr, Inhabited

namespace Condition

/-- ASCII lower case, character by character. -/
def lower (s : String) : List Char := s.toList.map Char.toLower

/-- The value of an attribute by name. Names are compared exactly: every
producer in this library spells them in lower case, and folding both sides
cost more kernel time than the condition itself (performance review §4.1). -/
def lookup (attrs : List (String × String)) (name : String) : Option String :=
  (attrs.find? fun p => p.1 == name).map (·.2)

/-- The condition holds of the attributes. -/
def holds (c : Condition) (attrs : List (String × String)) : Bool :=
  match c with
  | .always => true
  | .hasAny names => names.any fun n => (lookup attrs n).isSome
  | .attrNot name value =>
    match lookup attrs name with
    | none => true
    | some v => lower v != lower value

end Condition
end Whatwg.Html.Schema
