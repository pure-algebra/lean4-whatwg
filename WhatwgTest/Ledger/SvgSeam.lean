import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `SVG-PG-SEAM`

The ten edges of `docs/SVG-SEAM-DAG.md` (`test/contracts/graph-ledger.contract.md`; ruling
R-W6). The graph opened at slice S3b of `docs/SVG-PACKAGE-PLAN.md`, when the checker first
admitted a tree that holds `svg`. Every ground names a theorem, a declaration or a module of
the built tree, and each open item is a slice of that plan or a named gap.

The fence is the eleven modules of `Whatwg/Svg/` that declare a constant and are no value
grammar: the ten of the schema and the position, and `Value/Attribute`, which says which
grammar judges which attribute. The value grammars are the leaf `SVG-LF-GRAMMAR`. The seam's
own modules are under `Whatwg/Html/` and stay with the unrouted prefix `Whatwg.Html` (debt
D57): this entry cites their theorems and does not fence them.

No edge is closed. Rulings R-S4, R-S9 to R-S14, R-S16, R-S17 and R-S19 of `COORDINATION.md`
name this graph and change no edge's status, so the entry acknowledges the ten.
-/

namespace WhatwgTest.Ledger
open Gates.Ledger

/-- The assurance graph of the admission of SVG content in an HTML tree. -/
def svgSeam : Graph where
  id := "SVG-PG-SEAM"
  document := "docs/SVG-SEAM-DAG.md"
  fence := [`Whatwg.Svg.Data.Universe, `Whatwg.Svg.Data.Mask, `Whatwg.Svg.Data.NameTable,
    `Whatwg.Svg.Schema.Tags, `Whatwg.Svg.Schema.Categories, `Whatwg.Svg.Schema.Attributes,
    `Whatwg.Svg.Schema.ContentModel, `Whatwg.Svg.Schema.Readings, `Whatwg.Svg.Schema.Universe,
    `Whatwg.Svg.Content.Context, `Whatwg.Svg.Value.Attribute]
  acknowledged := ["R-S4", "R-S9", "R-S10", "R-S11", "R-S12", "R-S13", "R-S14", "R-S16", "R-S17", "R-S19"]
  edges := {
    identity := {
      status := .requiredOpen
      remaining := [
        .named "the declaration records of `Whatwg.Svg`: no record names each declaration's owner and anchor yet"]
      grounds := [.declarations [`Whatwg.Svg.Schema.Tag, `Whatwg.Svg.Schema.Attr,
        `Whatwg.Svg.Schema.Category, `Whatwg.Svg.Schema.AttrCategory, `Whatwg.Svg.Schema.Tag.digest]]
      note := "`lake exe whatwg_svgdefinitions` checks each sealed file's digest and regenerates the four projections and the four schema modules without a byte of drift; each element's entry carries its span digest." }
    construction := {
      status := .requiredOpen
      remaining := [
        .named "the context-indexed typed tree `Element` has no SVG element: an SVG subtree is an `SvgNode`, whose values are right by their types and whose structure is one obligation of `validIn` on its raw tree (debt D83)"]
      grounds := [.declarations [`Whatwg.Svg.Data.Universe, `Whatwg.Svg.Data.Mask,
        `Whatwg.Svg.Data.NameTable, `Whatwg.Svg.Content.Ctx, `Whatwg.Svg.Content.Ctx.child,
        `Whatwg.Html.Content.Pos, `Whatwg.Html.Content.Pos.child, `Whatwg.Svg.Value.AttrValue,
        `Whatwg.Html.SvgAttr, `Whatwg.Html.SvgNode, `Whatwg.Html.SvgNode.toRaw,
        `Whatwg.Html.SvgNode.ofRaw?]]
      note := "A set is a mask over a finite universe, a name table is a writer with a checked guess, and a position is a sum of the HTML position and the SVG position; `RawNode` is unchanged. A typed SVG node stands beside it: its attribute holds a value of the type the table gives, and `toRaw` writes the raw tree." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "a sentence of an SVG chapter that narrows a content model is not read, apart from the four readings of ruling SV-4",
        .named "`validIn` reads no SVG value: the value judgment `valuesOk` is a second algebra of the walk, beside the checker (ruling SV-30)",
        .named "an attribute with no kind in the table of `Whatwg/Svg/Value/Attribute.lean` takes any text: the lists of `x`, `y`, `dx` and `dy` on `text`, whose chapter is not sealed (debt D96), a colour, a paint and a URL are not judged",
        .named "a geometry property that must not be negative is refused when it is: the sealed chapter treats it as the initial value with no error state (ruling SV-35)",
        .named "the check of a length refuses some values that SVG admits: a unit the sealed table does not name, `calc()`, a CSS comment and a CSS escape (ruling SV-31)",
        .debt "D57"]
      grounds := [.declarations [`Whatwg.Html.Content.check, `Whatwg.Html.Content.validIn,
        `Whatwg.Html.Content.Pos.elementOk, `Whatwg.Svg.Content.Ctx.admits,
        `Whatwg.Svg.Content.boundsOk, `Whatwg.Svg.Content.attrOk, `Whatwg.Svg.Value.ValueKind,
        `Whatwg.Svg.Value.kindOf, `Whatwg.Svg.Value.valueOk, `Whatwg.Svg.Value.explainValue,
        `Whatwg.Html.Content.valuesWalk, `Whatwg.Html.Content.valuesOk]]
      note := "`validIn` is the run of the Boolean algebra `check` from an HTML position, and `valuesOk` the run of `valuesWalk` over the namespace alone; the HTML checker's own fidelity to the standard is the HTML package's open edge." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "node V3c holds for a deterministic description alone: path data, `points`, `viewBox` and `transform` are not deterministic by design, their language is that of the rule `Greedy` (ruling SV-33), and a text of the bare expression that the reader refuses is in each grammar's battery",
        .named "the offset of a refused value is not proved local: no theorem says that every text with that prefix is refused (debt D94)"]
      grounds := [.theorems [`Whatwg.Svg.Data.Universe.forall_of_all,
        `Whatwg.Svg.Data.Mask.mem_union, `Whatwg.Svg.Data.Mask.mem_inter,
        `Whatwg.Svg.Data.Mask.mem_diff, `Whatwg.Svg.Data.Mask.mem_ofList,
        `Whatwg.Svg.Schema.Tag.model_tags, `Whatwg.Svg.Schema.Tag.model_text,
        `Whatwg.Svg.Schema.Tag.attrs_eq, `Whatwg.Svg.Content.Ctx.child_model_mem,
        `Whatwg.Svg.Content.Ctx.child_admitsText, `Whatwg.Html.Walk.fusion,
        `Whatwg.Html.Walk.transport, `Whatwg.Html.Content.Pos.child_ns,
        `Whatwg.Html.Content.Pos.excl_le_child, `Whatwg.Html.Content.Pos.elementOk_antitone,
        `Whatwg.Html.Content.validIn_element_eq, `Whatwg.Html.Content.validIn_unknown,
        `Whatwg.Html.Content.validIn_svg, `Whatwg.Html.Content.no_svg_tag_breaks_out,
        `Whatwg.Html.Walk.relate, `Whatwg.Html.Content.Pos.isNone_refuse?,
        `Whatwg.Html.Content.explain_none_iff, `Whatwg.Html.Content.explainAt_path,
        `Whatwg.Html.Print.decode_render, `Whatwg.Html.Print.renderIn_text_no_delim_of_svg,
        `Whatwg.Html.Content.isNone_explainValuesAt, `Whatwg.Html.Content.explainValues_none_iff,
        `Whatwg.Html.Content.check_valueText, `Whatwg.Html.Content.valueOkByName_valueText,
        `Whatwg.Svg.Value.explainValue_eq_none_iff,
        `Whatwg.Svg.Value.explainValueByName_eq_none_iff, `Whatwg.Html.SvgNode.valuesAt_toRaw,
        `Whatwg.Html.SvgNode.valuesOk_toRaw, `Whatwg.Html.SvgNode.explainValues_toRaw,
        `Whatwg.Html.readValue_valueTextOf, `Whatwg.Html.SvgNode.ofRaw?_toRaw]]
      note := "The nodes U1, B1, K1, W1, W2, T2, X1, X2, C1, C2, C3, C4, N3, P1 and P2 of the plan's section 6 are proved; C3 is the walk's fusion law at `Option.isNone`, and C4 its induction law. V4 is the same fusion law at the value judgment, V5 says that the text of a typed value passes its attribute's check with no evaluation, and V6 that the located refusal of a value is absent exactly when the value passes. V7 is the connector: the raw tree of every typed tree passes the value judgment. P4 says that the raw tree of a placed typed tree reads back as the tree." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "no gate compares a transcribed grammar with the productions of its sealed chapter (debt D95)"]
      grounds := [.theorems [`Whatwg.Svg.Value.valueOk_print, `Whatwg.Svg.Value.valueOkByName_chars,
        `Whatwg.Svg.Data.NameTable.read_exact,
        `Whatwg.Svg.Data.NameTable.read_chars, `Whatwg.Svg.Schema.Tag.ofChars?_chars,
        `Whatwg.Svg.Schema.Tag.ofChars?_exact, `Whatwg.Svg.Schema.Attr.ofChars?_chars,
        `Whatwg.Svg.Schema.Attr.ofChars?_exact, `Whatwg.Html.Content.restore_tag,
        `Whatwg.Html.Content.restore_attr, `Whatwg.Html.Print.decodeNode?_render,
        `Whatwg.Html.Print.renderChars_injective_of_wf, `Whatwg.Html.Print.render_injective_of_wf]]
      note := "The two name tables are exact embeddings (N1), the tree construction's tables restore every schema name from its lower-case form (N2), and the printer is an exact embedding of the well-formed trees, with SVG subtrees or without (P1, P3). Each name that the table gives a kind admits the text of every typed value of that kind (V2 at the table); the grammars themselves are the leaf `SVG-LF-GRAMMAR`." }
    counterexamples := {
      status := .requiredOpen
      remaining := [
        .named "no register row: the controls of the batteries under `WhatwgTest/Svg` and of `WhatwgTest/Html/Svg.lean` are not registered counterexamples"] }
    bridges := {
      status := .requiredOpen
      remaining := [
        .named "a host observation that a browser parses a printed tree back to the tree: none is recorded, and no parser exists in this package"] }
    targets := {
      status := .notApplicable
      note := "The graph emits no target code; the text the printer writes is under the representation edge." }
    trust := {
      status := .requiredOpen
      remaining := [.named "the structure of an SVG subtree that `html!` builds is one kernel evaluation of `validIn` on its raw tree, not a proof composed from its nodes (debt D83)"]
      grounds := [.modules [`Whatwg.Svg.Data.Universe, `Whatwg.Svg.Data.Mask,
        `Whatwg.Svg.Data.NameTable, `Whatwg.Svg.Schema.Universe, `Whatwg.Svg.Content.Context,
        `Whatwg.Svg.Value.Attribute, `Whatwg.Html.Svg, `Whatwg.Html.Node.Walk,
        `Whatwg.Html.Schema.Foreign, `Whatwg.Html.Content.Explain, `Whatwg.Html.Content.Values,
        `Whatwg.Html.Print.Render, `Whatwg.Html.Node.Svg, `Whatwg.Html.Node.SvgRead,
        `Whatwg.Html.Syntax.Elaborator, `WhatwgTest.Svg.Schema, `WhatwgTest.Svg.Context,
        `WhatwgTest.Html.Svg, `WhatwgTest.Html.Explain, `WhatwgTest.Html.SvgPrint,
        `WhatwgTest.Html.SvgMarkup, `WhatwgTest.Html.SvgValues, `WhatwgTest.Html.SvgNode,
        `WhatwgTest.Html.SvgRead], .gate .build]
      note := "Every module of `Whatwg.Svg` is under the strict ceiling, `propext` and `Quot.sound` only, with no exact exception; the seam's modules are under the ceiling of ruling R-11." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "a census of SVG 2 and a coverage denominator: none exists, and no coverage is claimed"] } }

end WhatwgTest.Ledger
