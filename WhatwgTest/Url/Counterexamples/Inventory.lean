import Gates.UrlInventory

/-!
Independent URL inventory review regressions, frozen before repair.
Stable witnesses: `URL-INV-CE-001`, `URL-INV-CE-002`, and `URL-INV-CE-003`.
Attack record: `test/counterexamples/url/INVENTORY.md`.

These are finite executable tooling probes, not URL semantic theorems or arbitrary-source laws.
The frozen base battery in `WhatwgTest.Url.InventoryContract` remains unchanged.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.Counterexamples.Inventory

#check (@Gates.UrlInventory.scan : ByteArray → Except String (Array Gates.UrlInventory.Entry))

open Gates.UrlInventory

private def views (src : String) : Option (Array (Kind × String × String × String)) := do
  let rows ← (scan src.toUTF8).toOption
  if !rows.all (fun row ↦ row.b < row.e && row.e ≤ src.toUTF8.size) then none
  else some (rows.map (fun row ↦
    (row.kind, row.label, row.section, String.fromUTF8! (src.toUTF8.extract row.b row.e))))

-- URL-INV-CE-001: only lt has alternatives; the entire normalized for value is the owner.
private def commaOwnerSource := "<dfn for='URL,URLSearchParams' lt=x>x</dfn>"
#guard views commaOwnerSource ==
  some #[(.definition, "URL,URLSearchParams/x", "", commaOwnerSource)]

-- URL-INV-CE-002: ASCII form feed is whitespace in class tokens and visible text.
private def formFeed : String := String.singleton (Char.ofNat 12)
private def formFeedIdlSource :=
  "<pre class='idl" ++ formFeed ++ "example'>\ninterface Example {\n  stringifier;\n};\n</pre>"
#guard views formFeedIdlSource == some #[
  (.idl, "interface Example {", "", "interface Example {"),
  (.idl, "stringifier;", "", "stringifier;")]

private def formFeedProseSource := "<p>a" ++ formFeed ++ "b"
#guard views formFeedProseSource == some #[(.prose, "a b", "", formFeedProseSource)]

-- URL-INV-CE-003: xmp content is raw text, including raw IDL angle brackets and fake markup.
private def rawIdlMember := "iterable<USVString, USVString>;"
private def rawIdlSource :=
  "<xmp class=idl>\ninterface Example {\n  " ++ rawIdlMember ++ "\n};\n</xmp>"
#guard views rawIdlSource == some #[
  (.idl, "interface Example {", "", "interface Example {"),
  (.idl, rawIdlMember, "", rawIdlMember)]

private def uppercaseCloseIdlSource :=
  "<xmp class=idl>\ninterface Example {\n  " ++ rawIdlMember ++ "\n};\n</XMP>"
#guard views uppercaseCloseIdlSource == some #[
  (.idl, "interface Example {", "", "interface Example {"),
  (.idl, rawIdlMember, "", rawIdlMember)]
#guard views "<xmp><dfn id=fake>fake</dfn></xmp>" == some #[]

end WhatwgTest.Url.Counterexamples.Inventory
