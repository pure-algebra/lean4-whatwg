/-!
# Whatwg.Html.Print.Xml.Productions

Owner: the productions of XML 1.0 that the XML serialization cites (slice S9 of
`docs/SVG-PACKAGE-PLAN.md`; ruling SV-42; debt D105 of ruling R-S22). The algorithm of DOM
Parsing and Serialization asks, under "require well-formed", that a local name matches the
production `Name` and that a value, a text and a comment hold characters of the production
`Char`, and it cites both from XML 1.0.

The authority is Extensible Markup Language (XML) 1.0 (Fifth Edition), the W3C Recommendation of
26 November 2008, sealed at `vendor/w3c-xml-20081126/REC-xml-20081126.html`. Four productions
are transcribed, each alternative in the order the document writes it:

- `[2] Char`, section 2.2: `isChar`;
- `[4] NameStartChar` and `[4a] NameChar`, section 2.3: `isNameStartChar` and `isNameChar`;
- `[5] Name ::= NameStartChar (NameChar)*`, section 2.3: `isName`.

The gate `lake exe whatwg_xmlproductions` (`WhatwgGates/XmlProductions.lean`) reads the three
character productions from the sealed bytes and compares each with its function here at every
code point from U+0000 to U+10FFFF. It reads `[5]` as written above and compares `isName` with
that reading at short texts.

This module has no import, so the gate links it alone.

What this module does not claim: any other production of XML 1.0. A document, an element, an
attribute value and a comment have productions there, and none is transcribed. `isChar` is the
production of the fifth edition: it admits U+0085 and the other characters that the edition's
note discourages.

Copyright (c) 2008 World Wide Web Consortium. This file includes material derived from
Extensible Markup Language (XML) 1.0 (Fifth Edition),
https://www.w3.org/TR/2008/REC-xml-20081126/, under the W3C Document License,
https://www.w3.org/copyright/document-license-2023/
-/

namespace Whatwg.Html.Print.Xml

/-- The code point of the character is in the closed range. -/
def between (lo hi : Nat) (c : Char) : Bool := decide (lo ≤ c.toNat) && decide (c.toNat ≤ hi)

/-- The production `[2] Char` of XML 1.0: a tab, a line feed, a carriage return, and every
code point from U+0020 but the surrogates, U+FFFE and U+FFFF. -/
def isChar (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\r' || between 0x20 0xD7FF c || between 0xE000 0xFFFD c ||
    between 0x10000 0x10FFFF c

/-- The production `[4] NameStartChar`. -/
def isNameStartChar (c : Char) : Bool :=
  c == ':' || between 0x41 0x5A c || c == '_' || between 0x61 0x7A c || between 0xC0 0xD6 c ||
    between 0xD8 0xF6 c || between 0xF8 0x2FF c || between 0x370 0x37D c ||
    between 0x37F 0x1FFF c || between 0x200C 0x200D c || between 0x2070 0x218F c ||
    between 0x2C00 0x2FEF c || between 0x3001 0xD7FF c || between 0xF900 0xFDCF c ||
    between 0xFDF0 0xFFFD c || between 0x10000 0xEFFFF c

/-- The production `[4a] NameChar`. -/
def isNameChar (c : Char) : Bool :=
  isNameStartChar c || c == '-' || c == '.' || between 0x30 0x39 c || between 0xB7 0xB7 c ||
    between 0x300 0x36F c || between 0x203F 0x2040 c

/-- The production `[5] Name`: a `NameStartChar`, and then any number of `NameChar`. -/
def isName : List Char → Bool
  | [] => false
  | c :: rest => isNameStartChar c && rest.all isNameChar

end Whatwg.Html.Print.Xml
