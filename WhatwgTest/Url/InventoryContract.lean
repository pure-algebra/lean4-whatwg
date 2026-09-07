import Gates.UrlInventory

/-!
Breaker-owned U2a finite executable probes, frozen before the scanner implementation.
Contract: `test/contracts/url-inventory.contract.md`.
Surface and label authority: `docs/URL-INVENTORY-INTERFACE.md`.

These `#guard` probes check lexical source tooling on the displayed finite inputs. They are
neither a theorem about arbitrary source nor URL semantic or specification-coverage evidence.
Every helper is private; production names in the signature ascriptions are fully qualified.
-/

set_option autoImplicit false

namespace WhatwgTest.Url.InventoryContract

#check (@Gates.UrlInventory.tokenize :
  ByteArray → Except String (Array Gates.UrlInventory.Token))
#check (@Gates.UrlInventory.checkPartition : Nat → Array Gates.UrlInventory.Token → Bool)
#check (@Gates.UrlInventory.scan : ByteArray → Except String (Array Gates.UrlInventory.Entry))

open Gates.UrlInventory

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def token (kind : TokenKind) (b e : Nat) : Token := { kind, b, e }

-- Projection checks every emitted span's bounds before exposing its exact source bytes.
private def views (src : String) : Option (Array (Kind × String × String × String)) := do
  let rows ← (scan src.toUTF8).toOption
  if !rows.all (fun row ↦ row.b < row.e && row.e ≤ src.toUTF8.size) then none
  else some (rows.map (fun row ↦
    (row.kind, row.label, row.section, String.fromUTF8! (src.toUTF8.extract row.b row.e))))

-- URL-INV-P01: exact byte partition, including every boundary refusal.
#guard checkPartition 0 #[]
#guard !(checkPartition 1 #[])
#guard checkPartition 5 #[token .text 0 2, token .comment 2 5]
#guard !(checkPartition 5 #[token .text 1 5])
#guard !(checkPartition 5 #[token .text 0 2, token .tag 3 5])
#guard !(checkPartition 5 #[token .text 0 3, token .tag 2 5])
#guard !(checkPartition 5 #[token .text 0 0, token .text 0 5])
#guard !(checkPartition 5 #[token .text 0 3, token .tag 3 2, token .text 2 5])
#guard !(checkPartition 5 #[token .text 0 6])
#guard !(checkPartition 5 #[token .text 0 4])
#guard (tokenize ByteArray.empty).toOption == some #[]
#guard views "" == some #[]

-- URL-INV-P02: quoted '>' and all attribute forms; offsets count UTF-8 bytes.
private def quoteOpen := "<dfn id=\"a>b\" for='URL' lt=host ignored>"
private def quoteSource := quoteOpen ++ "é</dfn>"

#guard match tokenize quoteSource.toUTF8 with
  | .error _ => false
  | .ok ts =>
    ts.size == 3 && checkPartition quoteSource.toUTF8.size ts &&
    (ts[0]!).kind == .tag && (ts[0]!).b == 0 &&
    (ts[0]!).e == quoteOpen.toUTF8.size && (ts[0]!).name == "dfn" &&
    !(ts[0]!).closing && !(ts[0]!).selfClosing &&
    (ts[0]!).attrs.size == 4 &&
    (ts[0]!).attrs.contains ("id", "a>b") && (ts[0]!).attrs.contains ("for", "URL") &&
    (ts[0]!).attrs.contains ("lt", "host") && (ts[0]!).attrs.contains ("ignored", "") &&
    (ts[1]!).kind == .text && (ts[1]!).b == quoteOpen.toUTF8.size &&
    (ts[1]!).e == quoteOpen.toUTF8.size + 2 &&
    (ts[2]!).kind == .tag && (ts[2]!).name == "dfn" && (ts[2]!).closing &&
    (ts[2]!).b == quoteOpen.toUTF8.size + 2 && (ts[2]!).e == quoteSource.toUTF8.size

#guard views quoteSource == some #[(.definition, "a>b", "", quoteSource)]
#guard match tokenize "<br data-x='a>b' />".toUTF8 with
  | .error _ => false
  | .ok ts => ts.size == 1 && (ts[0]!).kind == .tag && (ts[0]!).name == "br" &&
    (ts[0]!).selfClosing && !(ts[0]!).closing &&
    (ts[0]!).attrs == #[("data-x", "a>b")] && checkPartition 19 ts

-- URL-INV-P03: fake definitions in comments remain one comment token and emit no candidate.
private def fakeComment := "<!-- <dfn id=fake>fake</dfn> > -->"
private def realDefinition := "<dfn id=real>real</dfn>"
#guard match tokenize fakeComment.toUTF8 with
  | .error _ => false
  | .ok ts => ts == #[token .comment 0 fakeComment.toUTF8.size]
#guard views (fakeComment ++ realDefinition) ==
  some #[(.definition, "real", "", realDefinition)]

-- URL-INV-P04: balanced nested divs; algorithm spans include all nested containers.
private def innerDefinition := "<dfn id=i>inner</dfn>"
private def innerAlgorithm := "<div algorithm=inner>" ++ innerDefinition ++ "</div>"
private def outerDefinition := "<dfn id=o>outer</dfn>"
private def outerAlgorithm :=
  "<div algorithm=outer>" ++ outerDefinition ++ "<div>" ++ innerAlgorithm ++ "</div></div>"
#guard views outerAlgorithm == some #[
  (.algorithm, "outer", "", outerAlgorithm),
  (.definition, "o", "", outerDefinition),
  (.algorithm, "inner", "", innerAlgorithm),
  (.definition, "i", "", innerDefinition)]

private def idAlgorithm := "<div algorithm id=alg><dfn id=term>word</dfn></div>"
#guard views idAlgorithm == some #[
  (.algorithm, "alg", "", idAlgorithm),
  (.definition, "term", "", "<dfn id=term>word</dfn>")]
private def firstDefinition := "<dfn for=URL lt='parse|parse a URL'>other</dfn>"
private def firstDefinitionAlgorithm := "<div algorithm>" ++ firstDefinition ++ "</div>"
#guard views firstDefinitionAlgorithm == some #[
  (.algorithm, "URL/parse", "", firstDefinitionAlgorithm),
  (.definition, "URL/parse", "", firstDefinition)]

-- URL-INV-P05: ignored and parameter dfns, owner prefix, alternatives and visible markup.
private def ignoredDefinition := "<dfn ignored for=URL lt='host|URL host'>other</dfn>"
private def parameterDefinition :=
  "<dfn for=parser data-dfn-type=argument><var>input</var>  value\n</dfn>"
private def emptyOwnerDefinition := "<dfn for='' lt='bare|alternative'>other</dfn>"
#guard views (ignoredDefinition ++ parameterDefinition ++ emptyOwnerDefinition) == some #[
  (.definition, "URL/host", "", ignoredDefinition),
  (.definition, "parser/input value", "", parameterDefinition),
  (.definition, "bare", "", emptyOwnerDefinition)]

-- URL-INV-P06: structural and lexical errors cannot silently become a partial inventory.
#guard failed (tokenize "<dfn id='unterminated>word</dfn>".toUTF8)
#guard failed (tokenize "<dfn id=>word</dfn>".toUTF8)
#guard failed (tokenize "<dfn id=x".toUTF8)
#guard failed (tokenize "<!-- unfinished".toUTF8)
#guard failed (tokenize (ByteArray.mk #[0xC3, 0x28]))
#guard failed (scan (ByteArray.mk #[0xC3, 0x28]))
#guard failed (scan "<dfn id=x>unclosed".toUTF8)
#guard failed (scan "<div algorithm=a><dfn id=x>x</dfn>".toUTF8)
#guard failed (scan "<table><tr><td>x</td></tr>".toUTF8)
#guard failed (scan "<ul><li>x</li>".toUTF8)
#guard failed (scan "<h2 id=x>unclosed".toUTF8)

-- URL-INV-P07: IDL headers/members preserve extended attributes and multiline source spans.
private def idlHeader := "[Exposed=(Window,Worker)]\ninterface URL {"
private def idlConstructor := "constructor(USVString input);"
private def idlStatic := "[NewObject]\n  static URL parse(\n    USVString input);"
private def idlStringifier := "stringifier attribute USVString href;"
private def idlIterable := "iterable&lt;\n    USVString, USVString>;"
private def idlSource :=
  "<pre class='example idl'>\n  " ++ idlHeader ++ "\n  " ++ idlConstructor ++ "\n  " ++
  idlStatic ++ "\n  " ++ idlStringifier ++ "\n  " ++ idlIterable ++ "\n};\n</pre>"
#guard views idlSource == some #[
  (.idl, "[Exposed=(Window,Worker)] interface URL {", "", idlHeader),
  (.idl, idlConstructor, "", idlConstructor),
  (.idl, "[NewObject] static URL parse( USVString input);", "", idlStatic),
  (.idl, idlStringifier, "", idlStringifier),
  (.idl, "iterable&lt; USVString, USVString>;", "", idlIterable)]

-- URL-INV-P08: xmp participates in IDL; class membership is token-based, not substring-based.
private def xmpSource :=
  "<xmp class='idl example'>\ninterface URLSearchParams {\n  stringifier;\n};\n</xmp>"
#guard views xmpSource == some #[
  (.idl, "interface URLSearchParams {", "", "interface URLSearchParams {"),
  (.idl, "stringifier;", "", "stringifier;")]
#guard views "<pre class=notidl>\ninterface Hidden {\n  stringifier;\n};\n</pre>" == some #[]

-- URL-INV-P09: delimited members are retained; unsupported top-level or unfinished IDL fails.
#guard views "<pre class=idl>\ninterface Example {\n  futureMember;\n};\n</pre>" ==
  some #[(.idl, "interface Example {", "", "interface Example {"),
    (.idl, "futureMember;", "", "futureMember;")]
#guard failed (scan "<pre class=idl>\ndictionary Unsupported {\n};\n</pre>".toUTF8)
#guard failed (scan "<pre class=idl>\nstringifier;\n</pre>".toUTF8)
#guard failed (scan "<pre class=idl>\ninterface URL\n</pre>".toUTF8)
#guard failed (scan "<pre class=idl>\ninterface URL {\n  stringifier\n};\n</pre>".toUTF8)
#guard failed (scan "<pre class=idl>\ninterface URL {\n  stringifier;\n</pre>".toUTF8)
#guard failed (scan "<pre class=idl>\ninterface URL {\n  stringifier;\n};".toUTF8)
#guard failed (scan "<xmp class=idl>\ninterface URL {\n  stringifier;\n};".toUTF8)

-- URL-INV-P10: optional paragraph boundaries and heading section changes are lexical spans.
private def firstHeading := "<h2 id=first>First <em>section</em></h2>"
private def untitledHeading := "<h3>A &amp; B</h3>"
private def proseSource :=
  firstHeading ++ "<p>A <em>B</em><p>C</p>" ++ untitledHeading ++ "<dfn id=t>T</dfn>"
#guard views proseSource == some #[
  (.heading, "First section", "first", firstHeading),
  (.prose, "A B", "first", "<p>A <em>B</em>"),
  (.prose, "C", "first", "<p>C</p>"),
  (.heading, "A &amp; B", "", untitledHeading),
  (.definition, "t", "", "<dfn id=t>T</dfn>")]
#guard views "<p>tail" == some #[(.prose, "tail", "", "<p>tail")]
#guard views "<div algorithm=x><p>one</div>" == some #[
  (.algorithm, "x", "", "<div algorithm=x><p>one</div>"),
  (.prose, "one", "", "<p>one")]

-- URL-INV-P11: tables and all three list kinds include full balanced nested containers.
private def collectionHeading := "<h2 id=collections>Collections</h2>"
private def tableSource := "<table><tr><td>x</td></tr></table>"
private def unorderedSource := "<ul><li>two</li></ul>"
private def orderedSource := "<ol><li>one" ++ unorderedSource ++ "</li></ol>"
private def definitionListSource := "<dl><dt>term</dt><dd>value</dd></dl>"
#guard views (collectionHeading ++ tableSource ++ orderedSource ++ definitionListSource) ==
  some #[
    (.heading, "Collections", "collections", collectionHeading),
    (.table, "table", "collections", tableSource),
    (.list, "ol", "collections", orderedSource),
    (.list, "ul", "collections", unorderedSource),
    (.list, "dl", "collections", definitionListSource)]

end WhatwgTest.Url.InventoryContract
