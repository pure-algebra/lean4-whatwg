import WhatwgGates.Ledger.Model

/-!
# Ledger entry of `SVG-PG-SEAM`

The ten edges of `docs/SVG-SEAM-DAG.md` (`test/contracts/graph-ledger.contract.md`; ruling
R-W6). The graph opened at slice S3b of `docs/SVG-PACKAGE-PLAN.md`, when the checker first
admitted a tree that holds `svg`. Every ground names a theorem, a declaration or a module of
the built tree, and each open item is a slice of that plan or a named gap.

The fence is the ten modules of `Whatwg/Svg/` that declare a constant. The seam's own three
modules are under `Whatwg/Html/` and stay with the unrouted prefix `Whatwg.Html` (debt D57):
this entry cites their theorems and does not fence them.

No edge is closed. Rulings R-S4, R-S9, R-S10 and R-S11 of `COORDINATION.md` name this graph
and change no edge's status, so the entry acknowledges the four.
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
    `Whatwg.Svg.Content.Context]
  acknowledged := ["R-S4", "R-S9", "R-S10", "R-S11"]
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
        .named "the `html!` term and the typed tree build no SVG subtree (slice S3e)"]
      grounds := [.declarations [`Whatwg.Svg.Data.Universe, `Whatwg.Svg.Data.Mask,
        `Whatwg.Svg.Data.NameTable, `Whatwg.Svg.Content.Ctx, `Whatwg.Svg.Content.Ctx.child,
        `Whatwg.Html.Content.Pos, `Whatwg.Html.Content.Pos.child]]
      note := "A set is a mask over a finite universe, a name table is a writer with a checked guess, and a position is a sum of the HTML position and the SVG position; `RawNode` is unchanged." }
    semantics := {
      status := .requiredOpen
      remaining := [
        .named "a sentence of an SVG chapter that narrows a content model is not read, apart from the four readings of ruling SV-4",
        .named "an attribute's value is not judged (slice S4)",
        .debt "D57"]
      grounds := [.declarations [`Whatwg.Html.Content.check, `Whatwg.Html.Content.validIn,
        `Whatwg.Html.Content.Pos.elementOk, `Whatwg.Svg.Content.Ctx.admits,
        `Whatwg.Svg.Content.boundsOk, `Whatwg.Svg.Content.attrOk]]
      note := "`validIn` is the run of the Boolean algebra `check` from an HTML position; the HTML checker's own fidelity to the standard is the HTML package's open edge." }
    laws := {
      status := .requiredOpen
      remaining := [
        .named "the decoder inverts the printer on a well-formed tree that holds SVG (slice S3d)"]
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
        `Whatwg.Html.Content.explain_none_iff, `Whatwg.Html.Content.explainAt_path]]
      note := "The nodes U1, B1, K1, W1, W2, T2, X1, X2, C1, C2, C3, C4 and N3 of the plan's section 6 are proved; C3 is the walk's fusion law at `Option.isNone`, and C4 its induction law." }
    representation := {
      status := .requiredOpen
      remaining := [
        .named "the printer as an exact embedding of well-formed trees that hold SVG (slice S3d)",
        .named "the value grammars and their retractions (slice S4)"]
      grounds := [.theorems [`Whatwg.Svg.Data.NameTable.read_exact,
        `Whatwg.Svg.Data.NameTable.read_chars, `Whatwg.Svg.Schema.Tag.ofChars?_chars,
        `Whatwg.Svg.Schema.Tag.ofChars?_exact, `Whatwg.Svg.Schema.Attr.ofChars?_chars,
        `Whatwg.Svg.Schema.Attr.ofChars?_exact, `Whatwg.Html.Content.restore_tag,
        `Whatwg.Html.Content.restore_attr]]
      note := "The two name tables are exact embeddings (N1), and the tree construction's tables restore every schema name from its lower-case form (N2)." }
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
      note := "The graph emits no target code; the text the printer writes is slice S3d, under the representation edge." }
    trust := {
      status := .requiredOpen
      remaining := [.named "the modules of slices S3d to S4, which do not exist yet"]
      grounds := [.modules [`Whatwg.Svg.Data.Universe, `Whatwg.Svg.Data.Mask,
        `Whatwg.Svg.Data.NameTable, `Whatwg.Svg.Schema.Universe, `Whatwg.Svg.Content.Context,
        `Whatwg.Html.Svg, `Whatwg.Html.Node.Walk, `Whatwg.Html.Schema.Foreign,
        `Whatwg.Html.Content.Explain, `WhatwgTest.Svg.Schema, `WhatwgTest.Svg.Context,
        `WhatwgTest.Html.Svg, `WhatwgTest.Html.Explain], .gate .build]
      note := "Every module of `Whatwg.Svg` is under the strict ceiling, `propext` and `Quot.sound` only, with no exact exception; the seam's modules are under the ceiling of ruling R-11." }
    coverage := {
      status := .requiredOpen
      remaining := [
        .named "a census of SVG 2 and a coverage denominator: none exists, and no coverage is claimed"] } }

end WhatwgTest.Ledger
