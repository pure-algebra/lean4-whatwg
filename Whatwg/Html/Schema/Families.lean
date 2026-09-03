import Whatwg.Html.Schema.Tags

/-!
# Whatwg.Html.Schema.Families

Every named content set of `html_types.mli` reachable from an element's
content model, expanded through row-type inheritance into a
constructor-dispatch membership function, and the `ContentSet` index over
them.

Authored source since 2026-09-06. First transcribed at slice H2 (2026-09-03)
from TyXML 4.6.0 (`ocsigen/tyxml` commit
`d2916535536f2134bad7793a598ba5b7327cae41`: `html_types.mli`, `html_sigs.mli`,
`html_f.ml`) by a generator retired together with the TyXML pin; the HTML
Standard (`SPEC-MANIFEST.md`) is the sole authority, and every departure of
this transcription from it is recorded in `Whatwg.Html.Content.Divergence`.
Edited by hand under ordinary review.
Data and derived instances only: no proof lives here.
-/

namespace Whatwg.Html.Schema

/-- `colgroup_content_fun` (`html_types.mli` line 1946): 1 of 115 tags. -/
def Sets.colgroup_content_fun : Tag → Bool
  | .col => true
  | _ => false

/-- `core_flow5` (`html_types.mli` line 926): 74 of 115 tags. -/
def Sets.core_flow5 : Tag → Bool
  | .abbr | .address | .article | .aside | .b | .bdo | .blockquote | .br
  | .button | .cite | .code | .command | .datalist | .details | .dfn | .dialog
  | .div | .dl | .em | .embed | .fieldset | .figure | .footer | .form
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .header | .hgroup
  | .hr | .i | .iframe | .img | .img_interactive | .input | .kbd | .keygen
  | .label | .main | .mark | .menu | .meter | .nav | .ol | .output
  | .p | .pcdata | .picture | .pre | .progress | .q | .ruby | .samp
  | .script | .«section» | .select | .small | .span | .strong | .style | .sub
  | .sup | .svg | .table | .template | .textarea | .time | .u | .ul
  | .var | .wbr => true
  | _ => false

/-- `core_flow5_without_interactive` (`html_types.mli` line 945): 70 of 115 tags. -/
def Sets.core_flow5_without_interactive : Tag → Bool
  | .abbr | .address | .article | .aside | .b | .bdo | .blockquote | .br
  | .button | .cite | .code | .command | .datalist | .dfn | .dialog | .div
  | .dl | .em | .fieldset | .figure | .footer | .form | .h1 | .h2
  | .h3 | .h4 | .h5 | .h6 | .header | .hgroup | .hr | .i
  | .img | .input | .kbd | .keygen | .label | .main | .mark | .menu
  | .meter | .nav | .ol | .output | .p | .pcdata | .picture | .pre
  | .progress | .q | .ruby | .samp | .script | .«section» | .select | .small
  | .span | .strong | .style | .sub | .sup | .svg | .table | .template
  | .textarea | .time | .u | .ul | .var | .wbr => true
  | _ => false

/-- `core_flow5_without_media` (`html_types.mli` line 981): 74 of 115 tags. -/
def Sets.core_flow5_without_media : Tag → Bool
  | .abbr | .address | .article | .aside | .b | .bdo | .blockquote | .br
  | .button | .cite | .code | .command | .datalist | .details | .dfn | .dialog
  | .div | .dl | .em | .embed | .fieldset | .figure | .footer | .form
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .header | .hgroup
  | .hr | .i | .iframe | .img | .img_interactive | .input | .kbd | .keygen
  | .label | .main | .mark | .menu | .meter | .nav | .ol | .output
  | .p | .pcdata | .picture | .pre | .progress | .q | .ruby | .samp
  | .script | .«section» | .select | .small | .span | .strong | .style | .sub
  | .sup | .svg | .table | .template | .textarea | .time | .u | .ul
  | .var | .wbr => true
  | _ => false

/-- `core_flow5_without_noscript` (`html_types.mli` line 963): 74 of 115 tags. -/
def Sets.core_flow5_without_noscript : Tag → Bool
  | .abbr | .address | .article | .aside | .b | .bdo | .blockquote | .br
  | .button | .cite | .code | .command | .datalist | .details | .dfn | .dialog
  | .div | .dl | .em | .embed | .fieldset | .figure | .footer | .form
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .header | .hgroup
  | .hr | .i | .iframe | .img | .img_interactive | .input | .kbd | .keygen
  | .label | .main | .mark | .menu | .meter | .nav | .ol | .output
  | .p | .pcdata | .picture | .pre | .progress | .q | .ruby | .samp
  | .script | .«section» | .select | .small | .span | .strong | .style | .sub
  | .sup | .svg | .table | .template | .textarea | .time | .u | .ul
  | .var | .wbr => true
  | _ => false

/-- `core_phrasing` (`html_types.mli` line 536): 43 of 115 tags. -/
def Sets.core_phrasing : Tag → Bool
  | .abbr | .b | .bdo | .br | .button | .cite | .code | .command
  | .datalist | .dfn | .em | .embed | .i | .iframe | .img | .img_interactive
  | .input | .kbd | .keygen | .label | .mark | .meter | .output | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .sub | .sup | .svg | .template | .textarea | .time
  | .u | .var | .wbr => true
  | _ => false

/-- `core_phrasing_without_interactive` (`html_types.mli` line 615): 33 of 115 tags. -/
def Sets.core_phrasing_without_interactive : Tag → Bool
  | .abbr | .b | .bdo | .br | .cite | .code | .command | .datalist
  | .dfn | .em | .i | .img | .kbd | .mark | .meter | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .small | .span
  | .strong | .sub | .sup | .svg | .template | .time | .u | .var
  | .wbr => true
  | _ => false

/-- `core_phrasing_without_media` (`html_types.mli` line 651): 43 of 115 tags. -/
def Sets.core_phrasing_without_media : Tag → Bool
  | .abbr | .b | .bdo | .br | .button | .cite | .code | .command
  | .datalist | .dfn | .em | .embed | .i | .iframe | .img | .img_interactive
  | .input | .kbd | .keygen | .label | .mark | .meter | .output | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .sub | .sup | .svg | .template | .textarea | .time
  | .u | .var | .wbr => true
  | _ => false

/-- `core_phrasing_without_noscript` (`html_types.mli` line 576): 43 of 115 tags. -/
def Sets.core_phrasing_without_noscript : Tag → Bool
  | .abbr | .b | .bdo | .br | .button | .cite | .code | .command
  | .datalist | .dfn | .em | .embed | .i | .iframe | .img | .img_interactive
  | .input | .kbd | .keygen | .label | .mark | .meter | .output | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .sub | .sup | .svg | .template | .textarea | .time
  | .u | .var | .wbr => true
  | _ => false

/-- `dl_content_fun` (`html_types.mli` line 1484): 2 of 115 tags. -/
def Sets.dl_content_fun : Tag → Bool
  | .dd | .dt => true
  | _ => false

/-- `flow5` (`html_types.mli` line 1019): 86 of 115 tags. -/
def Sets.flow5 : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .audio | .audio_interactive | .b
  | .bdo | .blockquote | .br | .button | .canvas | .cite | .code | .command
  | .datalist | .del | .details | .dfn | .dialog | .div | .dl | .em
  | .embed | .fieldset | .figure | .footer | .form | .h1 | .h2 | .h3
  | .h4 | .h5 | .h6 | .header | .hgroup | .hr | .i | .iframe
  | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label | .main
  | .map | .mark | .menu | .meter | .nav | .noscript | .object | .object_interactive
  | .ol | .output | .p | .pcdata | .picture | .pre | .progress | .q
  | .ruby | .samp | .script | .«section» | .select | .small | .span | .strong
  | .style | .sub | .sup | .svg | .table | .template | .textarea | .time
  | .u | .ul | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `flow5_without_form` (`html_types.mli` line 1126): 85 of 115 tags. -/
def Sets.flow5_without_form : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .audio | .audio_interactive | .b
  | .bdo | .blockquote | .br | .button | .canvas | .cite | .code | .command
  | .datalist | .del | .details | .dfn | .dialog | .div | .dl | .em
  | .embed | .fieldset | .figure | .footer | .h1 | .h2 | .h3 | .h4
  | .h5 | .h6 | .header | .hgroup | .hr | .i | .iframe | .img
  | .img_interactive | .input | .ins | .kbd | .keygen | .label | .main | .map
  | .mark | .menu | .meter | .nav | .noscript | .object | .object_interactive | .ol
  | .output | .p | .pcdata | .picture | .pre | .progress | .q | .ruby
  | .samp | .script | .«section» | .select | .small | .span | .strong | .style
  | .sub | .sup | .svg | .table | .template | .textarea | .time | .u
  | .ul | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `flow5_without_header_footer` (`html_types.mli` line 1072): 84 of 115 tags. -/
def Sets.flow5_without_header_footer : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .audio | .audio_interactive | .b
  | .bdo | .blockquote | .br | .button | .canvas | .cite | .code | .command
  | .datalist | .del | .details | .dfn | .dialog | .div | .dl | .em
  | .embed | .fieldset | .figure | .form | .h1 | .h2 | .h3 | .h4
  | .h5 | .h6 | .hgroup | .hr | .i | .iframe | .img | .img_interactive
  | .input | .ins | .kbd | .keygen | .label | .main | .map | .mark
  | .menu | .meter | .nav | .noscript | .object | .object_interactive | .ol | .output
  | .p | .pcdata | .picture | .pre | .progress | .q | .ruby | .samp
  | .script | .«section» | .select | .small | .span | .strong | .style | .sub
  | .sup | .svg | .table | .template | .textarea | .time | .u | .ul
  | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `flow5_without_interactive` (`html_types.mli` line 1000): 78 of 115 tags. -/
def Sets.flow5_without_interactive : Tag → Bool
  | .abbr | .address | .article | .aside | .audio | .b | .bdo | .blockquote
  | .br | .button | .canvas | .cite | .code | .command | .datalist | .del
  | .dfn | .dialog | .div | .dl | .em | .fieldset | .figure | .footer
  | .form | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .header
  | .hgroup | .hr | .i | .img | .input | .ins | .kbd | .keygen
  | .label | .main | .map | .mark | .menu | .meter | .nav | .noscript
  | .object | .ol | .output | .p | .pcdata | .picture | .pre | .progress
  | .q | .ruby | .samp | .script | .«section» | .select | .small | .span
  | .strong | .style | .sub | .sup | .svg | .table | .template | .textarea
  | .time | .u | .ul | .var | .video | .wbr => true
  | _ => false

/-- `flow5_without_interactive_header_footer` (`html_types.mli` line 1046): 76 of 115 tags. -/
def Sets.flow5_without_interactive_header_footer : Tag → Bool
  | .abbr | .address | .article | .aside | .audio | .b | .bdo | .blockquote
  | .br | .button | .canvas | .cite | .code | .command | .datalist | .del
  | .dfn | .dialog | .div | .dl | .em | .fieldset | .figure | .form
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .hgroup | .hr
  | .i | .img | .input | .ins | .kbd | .keygen | .label | .main
  | .map | .mark | .menu | .meter | .nav | .noscript | .object | .ol
  | .output | .p | .pcdata | .picture | .pre | .progress | .q | .ruby
  | .samp | .script | .«section» | .select | .small | .span | .strong | .style
  | .sub | .sup | .svg | .table | .template | .textarea | .time | .u
  | .ul | .var | .video | .wbr => true
  | _ => false

/-- `flow5_without_media` (`html_types.mli` line 1014): 82 of 115 tags. -/
def Sets.flow5_without_media : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .b | .bdo | .blockquote
  | .br | .button | .canvas | .cite | .code | .command | .datalist | .del
  | .details | .dfn | .dialog | .div | .dl | .em | .embed | .fieldset
  | .figure | .footer | .form | .h1 | .h2 | .h3 | .h4 | .h5
  | .h6 | .header | .hgroup | .hr | .i | .iframe | .img | .img_interactive
  | .input | .ins | .kbd | .keygen | .label | .main | .map | .mark
  | .menu | .meter | .nav | .noscript | .object | .object_interactive | .ol | .output
  | .p | .pcdata | .picture | .pre | .progress | .q | .ruby | .samp
  | .script | .«section» | .select | .small | .span | .strong | .style | .sub
  | .sup | .svg | .table | .template | .textarea | .time | .u | .ul
  | .var | .wbr => true
  | _ => false

/-- `flow5_without_noscript` (`html_types.mli` line 1007): 85 of 115 tags. -/
def Sets.flow5_without_noscript : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .audio | .audio_interactive | .b
  | .bdo | .blockquote | .br | .button | .canvas | .cite | .code | .command
  | .datalist | .del | .details | .dfn | .dialog | .div | .dl | .em
  | .embed | .fieldset | .figure | .footer | .form | .h1 | .h2 | .h3
  | .h4 | .h5 | .h6 | .header | .hgroup | .hr | .i | .iframe
  | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label | .main
  | .map | .mark | .menu | .meter | .nav | .object | .object_interactive | .ol
  | .output | .p | .pcdata | .picture | .pre | .progress | .q | .ruby
  | .samp | .script | .«section» | .select | .small | .span | .strong | .style
  | .sub | .sup | .svg | .table | .template | .textarea | .time | .u
  | .ul | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `flow5_without_sectioning_heading_header_footer` (`html_types.mli` line 1170): 73 of 115 tags. -/
def Sets.flow5_without_sectioning_heading_header_footer : Tag → Bool
  | .a | .abbr | .address | .audio | .audio_interactive | .b | .bdo | .blockquote
  | .br | .button | .canvas | .cite | .code | .command | .datalist | .del
  | .details | .dfn | .dialog | .div | .dl | .em | .embed | .fieldset
  | .figure | .form | .hr | .i | .iframe | .img | .img_interactive | .input
  | .ins | .kbd | .keygen | .label | .main | .map | .mark | .menu
  | .meter | .noscript | .object | .object_interactive | .ol | .output | .p | .pcdata
  | .picture | .pre | .progress | .q | .ruby | .samp | .script | .select
  | .small | .span | .strong | .style | .sub | .sup | .svg | .table
  | .template | .textarea | .time | .u | .ul | .var | .video | .video_interactive
  | .wbr => true
  | _ => false

/-- `flow5_without_sectioning_heading_header_footer_address` (`html_types.mli` line 1146): 72 of 115 tags. -/
def Sets.flow5_without_sectioning_heading_header_footer_address : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .blockquote | .br
  | .button | .canvas | .cite | .code | .command | .datalist | .del | .details
  | .dfn | .dialog | .div | .dl | .em | .embed | .fieldset | .figure
  | .form | .hr | .i | .iframe | .img | .img_interactive | .input | .ins
  | .kbd | .keygen | .label | .main | .map | .mark | .menu | .meter
  | .noscript | .object | .object_interactive | .ol | .output | .p | .pcdata | .picture
  | .pre | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .style | .sub | .sup | .svg | .table | .template
  | .textarea | .time | .u | .ul | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `flow5_without_table` (`html_types.mli` line 1026): 85 of 115 tags. -/
def Sets.flow5_without_table : Tag → Bool
  | .a | .abbr | .address | .article | .aside | .audio | .audio_interactive | .b
  | .bdo | .blockquote | .br | .button | .canvas | .cite | .code | .command
  | .datalist | .del | .details | .dfn | .dialog | .div | .dl | .em
  | .embed | .fieldset | .figure | .footer | .form | .h1 | .h2 | .h3
  | .h4 | .h5 | .h6 | .header | .hgroup | .hr | .i | .iframe
  | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label | .main
  | .map | .mark | .menu | .meter | .nav | .noscript | .object | .object_interactive
  | .ol | .output | .p | .pcdata | .picture | .pre | .progress | .q
  | .ruby | .samp | .script | .«section» | .select | .small | .span | .strong
  | .style | .sub | .sup | .svg | .template | .textarea | .time | .u
  | .ul | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `formassociated` (`html_types.mli` line 425): 10 of 115 tags. -/
def Sets.formassociated : Tag → Bool
  | .button | .fieldset | .input | .keygen | .label | .meter | .output | .progress
  | .select | .textarea => true
  | _ => false

/-- `formatblock` (`html_types.mli` line 406): 18 of 115 tags. -/
def Sets.formatblock : Tag → Bool
  | .address | .article | .aside | .blockquote | .div | .footer | .h1 | .h2
  | .h3 | .h4 | .h5 | .h6 | .header | .hgroup | .nav | .p
  | .pre | .«section» => true
  | _ => false

/-- `heading` (`html_types.mli` line 394): 7 of 115 tags. -/
def Sets.heading : Tag → Bool
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 | .hgroup => true
  | _ => false

/-- `hgroup_content_fun` (`html_types.mli` line 1346): 6 of 115 tags. -/
def Sets.hgroup_content_fun : Tag → Bool
  | .h1 | .h2 | .h3 | .h4 | .h5 | .h6 => true
  | _ => false

/-- `html_content_fun` (`html_types.mli` line 1190): 2 of 115 tags. -/
def Sets.html_content_fun : Tag → Bool
  | .body | .head => true
  | _ => false

/-- `iframe_content_fun` (`html_types.mli` line 1767): 1 of 115 tags. -/
def Sets.iframe_content_fun : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `labelable` (`html_types.mli` line 402): 8 of 115 tags. -/
def Sets.labelable : Tag → Bool
  | .button | .input | .keygen | .meter | .output | .progress | .select | .textarea => true
  | _ => false

/-- `labelable_without_interactive` (`html_types.mli` line 404): 2 of 115 tags. -/
def Sets.labelable_without_interactive : Tag → Bool
  | .meter | .progress => true
  | _ => false

/-- `listed` (`html_types.mli` line 423): 7 of 115 tags. -/
def Sets.listed : Tag → Bool
  | .button | .fieldset | .input | .keygen | .output | .select | .textarea => true
  | _ => false

/-- `metadata_without_title` (`html_types.mli` line 496): 8 of 115 tags. -/
def Sets.metadata_without_title : Tag → Bool
  | .base | .command | .link | .«meta» | .noscript | .script | .style | .template => true
  | _ => false

/-- `notag` (`html_types.mli` line 1182): 0 of 115 tags. -/
def Sets.notag : Tag → Bool := fun _ => false

/-- `ol_content_fun` (`html_types.mli` line 1440): 1 of 115 tags. -/
def Sets.ol_content_fun : Tag → Bool
  | .li => true
  | _ => false

/-- `optgroup_content_fun` (`html_types.mli` line 2176): 1 of 115 tags. -/
def Sets.optgroup_content_fun : Tag → Bool
  | .option => true
  | _ => false

/-- `option_content_fun` (`html_types.mli` line 2185): 1 of 115 tags. -/
def Sets.option_content_fun : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `phrasing` (`html_types.mli` line 711): 55 of 115 tags. -/
def Sets.phrasing : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .embed | .i | .iframe | .img | .img_interactive | .input | .ins | .kbd
  | .keygen | .label | .map | .mark | .meter | .noscript | .object | .object_interactive
  | .output | .pcdata | .picture | .progress | .q | .ruby | .samp | .script
  | .select | .small | .span | .strong | .sub | .sup | .svg | .template
  | .textarea | .time | .u | .var | .video | .video_interactive | .wbr => true
  | _ => false

/-- `phrasing_without_dfn` (`html_types.mli` line 730): 51 of 115 tags. -/
def Sets.phrasing_without_dfn : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .em | .i
  | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label | .map
  | .mark | .meter | .noscript | .object | .object_interactive | .output | .pcdata | .picture
  | .progress | .q | .ruby | .samp | .script | .select | .small | .span
  | .strong | .sub | .sup | .template | .textarea | .time | .u | .var
  | .video | .video_interactive | .wbr => true
  | _ => false

/-- `phrasing_without_interactive` (`html_types.mli` line 704): 41 of 115 tags. -/
def Sets.phrasing_without_interactive : Tag → Bool
  | .abbr | .audio | .b | .bdo | .br | .canvas | .cite | .code
  | .command | .datalist | .del | .dfn | .em | .i | .img | .ins
  | .kbd | .map | .mark | .meter | .noscript | .object | .pcdata | .picture
  | .progress | .q | .ruby | .samp | .script | .small | .span | .strong
  | .sub | .sup | .svg | .template | .time | .u | .var | .video
  | .wbr => true
  | _ => false

/-- `phrasing_without_label` (`html_types.mli` line 768): 51 of 115 tags. -/
def Sets.phrasing_without_label : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .i | .img | .img_interactive | .input | .ins | .kbd | .keygen | .map
  | .mark | .meter | .noscript | .object | .object_interactive | .output | .pcdata | .picture
  | .progress | .q | .ruby | .samp | .script | .select | .small | .span
  | .strong | .sub | .sup | .template | .textarea | .time | .u | .var
  | .video | .video_interactive | .wbr => true
  | _ => false

/-- `phrasing_without_media` (`html_types.mli` line 696): 51 of 115 tags. -/
def Sets.phrasing_without_media : Tag → Bool
  | .a | .abbr | .b | .bdo | .br | .button | .canvas | .cite
  | .code | .command | .datalist | .del | .dfn | .em | .embed | .i
  | .iframe | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label
  | .map | .mark | .meter | .noscript | .object | .object_interactive | .output | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .sub | .sup | .svg | .template | .textarea | .time
  | .u | .var | .wbr => true
  | _ => false

/-- `phrasing_without_meter` (`html_types.mli` line 885): 51 of 115 tags. -/
def Sets.phrasing_without_meter : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .i | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label
  | .map | .mark | .noscript | .object | .object_interactive | .output | .pcdata | .picture
  | .progress | .q | .ruby | .samp | .script | .select | .small | .span
  | .strong | .sub | .sup | .template | .textarea | .time | .u | .var
  | .video | .video_interactive | .wbr => true
  | _ => false

/-- `phrasing_without_noscript` (`html_types.mli` line 691): 11 of 115 tags. -/
def Sets.phrasing_without_noscript : Tag → Bool
  | .a | .audio | .audio_interactive | .canvas | .del | .ins | .map | .object
  | .object_interactive | .video | .video_interactive => true
  | _ => false

/-- `phrasing_without_progress` (`html_types.mli` line 806): 51 of 115 tags. -/
def Sets.phrasing_without_progress : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .i | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label
  | .map | .mark | .meter | .noscript | .object | .object_interactive | .output | .pcdata
  | .picture | .q | .ruby | .samp | .script | .select | .small | .span
  | .strong | .sub | .sup | .template | .textarea | .time | .u | .var
  | .video | .video_interactive | .wbr => true
  | _ => false

/-- `phrasing_without_time` (`html_types.mli` line 847): 51 of 115 tags. -/
def Sets.phrasing_without_time : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .i | .img | .img_interactive | .input | .ins | .kbd | .keygen | .label
  | .map | .mark | .meter | .noscript | .object | .object_interactive | .output | .pcdata
  | .picture | .progress | .q | .ruby | .samp | .script | .select | .small
  | .span | .strong | .sub | .sup | .template | .textarea | .u | .var
  | .video | .video_interactive | .wbr => true
  | _ => false

/-- `picture_content_fun` (`html_types.mli` line 2328): 3 of 115 tags. -/
def Sets.picture_content_fun : Tag → Bool
  | .script | .source | .template => true
  | _ => false

/-- `resetable` (`html_types.mli` line 398): 5 of 115 tags. -/
def Sets.resetable : Tag → Bool
  | .input | .keygen | .output | .select | .textarea => true
  | _ => false

/-- `rp` (`html_types.mli` line 1510): 1 of 115 tags. -/
def Sets.rp : Tag → Bool
  | .rp => true
  | _ => false

/-- `rt` (`html_types.mli` line 1515): 1 of 115 tags. -/
def Sets.rt : Tag → Bool
  | .rt => true
  | _ => false

/-- `ruby_content_fun` (`html_types.mli` line 1522): 57 of 115 tags. -/
def Sets.ruby_content_fun : Tag → Bool
  | .a | .abbr | .audio | .audio_interactive | .b | .bdo | .br | .button
  | .canvas | .cite | .code | .command | .datalist | .del | .dfn | .em
  | .embed | .i | .iframe | .img | .img_interactive | .input | .ins | .kbd
  | .keygen | .label | .map | .mark | .meter | .noscript | .object | .object_interactive
  | .output | .pcdata | .picture | .progress | .q | .rp | .rt | .ruby
  | .samp | .script | .select | .small | .span | .strong | .sub | .sup
  | .svg | .template | .textarea | .time | .u | .var | .video | .video_interactive
  | .wbr => true
  | _ => false

/-- `script` (`html_types.mli` line 2294): 1 of 115 tags. -/
def Sets.script : Tag → Bool
  | .script => true
  | _ => false

/-- `script_content_fun` (`html_types.mli` line 2303): 1 of 115 tags. -/
def Sets.script_content_fun : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `sectioning` (`html_types.mli` line 396): 4 of 115 tags. -/
def Sets.sectioning : Tag → Bool
  | .article | .aside | .nav | .«section» => true
  | _ => false

/-- `select_content_fun` (`html_types.mli` line 2156): 2 of 115 tags. -/
def Sets.select_content_fun : Tag → Bool
  | .optgroup | .option => true
  | _ => false

/-- `source` (`html_types.mli` line 1875): 1 of 115 tags. -/
def Sets.source : Tag → Bool
  | .source => true
  | _ => false

/-- `style_content_fun` (`html_types.mli` line 2290): 1 of 115 tags. -/
def Sets.style_content_fun : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `submitable` (`html_types.mli` line 400): 5 of 115 tags. -/
def Sets.submitable : Tag → Bool
  | .button | .input | .keygen | .select | .textarea => true
  | _ => false

/-- `table_content_fun` (`html_types.mli` line 1928): 1 of 115 tags. -/
def Sets.table_content_fun : Tag → Bool
  | .tr => true
  | _ => false

/-- `tablex_content_fun` (`html_types.mli` line 1937): 1 of 115 tags. -/
def Sets.tablex_content_fun : Tag → Bool
  | .tbody => true
  | _ => false

/-- `tbody_content_fun` (`html_types.mli` line 1973): 1 of 115 tags. -/
def Sets.tbody_content_fun : Tag → Bool
  | .tr => true
  | _ => false

/-- `template` (`html_types.mli` line 2306): 1 of 115 tags. -/
def Sets.template : Tag → Bool
  | .template => true
  | _ => false

/-- `textarea_content` (`html_types.mli` line 2123): 1 of 115 tags. -/
def Sets.textarea_content : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `tfoot_content_fun` (`html_types.mli` line 1982): 1 of 115 tags. -/
def Sets.tfoot_content_fun : Tag → Bool
  | .tr => true
  | _ => false

/-- `thead_content_fun` (`html_types.mli` line 1964): 1 of 115 tags. -/
def Sets.thead_content_fun : Tag → Bool
  | .tr => true
  | _ => false

/-- `title_content_fun` (`html_types.mli` line 1247): 1 of 115 tags. -/
def Sets.title_content_fun : Tag → Bool
  | .pcdata => true
  | _ => false

/-- `tr_content_fun` (`html_types.mli` line 2009): 2 of 115 tags. -/
def Sets.tr_content_fun : Tag → Bool
  | .td | .th => true
  | _ => false

/-- `transparent` (`html_types.mli` line 440): 12 of 115 tags. -/
def Sets.transparent : Tag → Bool
  | .a | .audio | .audio_interactive | .canvas | .del | .ins | .map | .noscript
  | .object | .object_interactive | .video | .video_interactive => true
  | _ => false

/-- `transparent_without_interactive` (`html_types.mli` line 456): 8 of 115 tags. -/
def Sets.transparent_without_interactive : Tag → Bool
  | .audio | .canvas | .del | .ins | .map | .noscript | .object | .video => true
  | _ => false

/-- `transparent_without_media` (`html_types.mli` line 483): 8 of 115 tags. -/
def Sets.transparent_without_media : Tag → Bool
  | .a | .canvas | .del | .ins | .map | .noscript | .object | .object_interactive => true
  | _ => false

/-- `transparent_without_noscript` (`html_types.mli` line 468): 11 of 115 tags. -/
def Sets.transparent_without_noscript : Tag → Bool
  | .a | .audio | .audio_interactive | .canvas | .del | .ins | .map | .object
  | .object_interactive | .video | .video_interactive => true
  | _ => false

/-- `ul_content_fun` (`html_types.mli` line 1457): 1 of 115 tags. -/
def Sets.ul_content_fun : Tag → Bool
  | .li => true
  | _ => false

/-- A named content set, by its TyXML type name. -/
inductive ContentSet where
  | colgroup_content_fun | core_flow5 | core_flow5_without_interactive | core_flow5_without_media | core_flow5_without_noscript | core_phrasing | core_phrasing_without_interactive | core_phrasing_without_media
  | core_phrasing_without_noscript | dl_content_fun | flow5 | flow5_without_form | flow5_without_header_footer | flow5_without_interactive | flow5_without_interactive_header_footer | flow5_without_media
  | flow5_without_noscript | flow5_without_sectioning_heading_header_footer | flow5_without_sectioning_heading_header_footer_address | flow5_without_table | formassociated | formatblock | heading | hgroup_content_fun
  | html_content_fun | iframe_content_fun | labelable | labelable_without_interactive | listed | metadata_without_title | notag | ol_content_fun
  | optgroup_content_fun | option_content_fun | phrasing | phrasing_without_dfn | phrasing_without_interactive | phrasing_without_label | phrasing_without_media | phrasing_without_meter
  | phrasing_without_noscript | phrasing_without_progress | phrasing_without_time | picture_content_fun | resetable | rp | rt | ruby_content_fun
  | script | script_content_fun | sectioning | select_content_fun | source | style_content_fun | submitable | table_content_fun
  | tablex_content_fun | tbody_content_fun | template | textarea_content | tfoot_content_fun | thead_content_fun | title_content_fun | tr_content_fun
  | transparent | transparent_without_interactive | transparent_without_media | transparent_without_noscript | ul_content_fun
  deriving DecidableEq, Repr, Inhabited

/-- Every content set, in constructor order. -/
def ContentSet.all : List ContentSet :=
  [.colgroup_content_fun, .core_flow5, .core_flow5_without_interactive, .core_flow5_without_media, .core_flow5_without_noscript, .core_phrasing, .core_phrasing_without_interactive, .core_phrasing_without_media,
   .core_phrasing_without_noscript, .dl_content_fun, .flow5, .flow5_without_form, .flow5_without_header_footer, .flow5_without_interactive, .flow5_without_interactive_header_footer, .flow5_without_media,
   .flow5_without_noscript, .flow5_without_sectioning_heading_header_footer, .flow5_without_sectioning_heading_header_footer_address, .flow5_without_table, .formassociated, .formatblock, .heading, .hgroup_content_fun,
   .html_content_fun, .iframe_content_fun, .labelable, .labelable_without_interactive, .listed, .metadata_without_title, .notag, .ol_content_fun,
   .optgroup_content_fun, .option_content_fun, .phrasing, .phrasing_without_dfn, .phrasing_without_interactive, .phrasing_without_label, .phrasing_without_media, .phrasing_without_meter,
   .phrasing_without_noscript, .phrasing_without_progress, .phrasing_without_time, .picture_content_fun, .resetable, .rp, .rt, .ruby_content_fun,
   .script, .script_content_fun, .sectioning, .select_content_fun, .source, .style_content_fun, .submitable, .table_content_fun,
   .tablex_content_fun, .tbody_content_fun, .template, .textarea_content, .tfoot_content_fun, .thead_content_fun, .title_content_fun, .tr_content_fun,
   .transparent, .transparent_without_interactive, .transparent_without_media, .transparent_without_noscript, .ul_content_fun]

/-- The TyXML type name of the set. -/
def ContentSet.tyxmlName : ContentSet → String
  | .colgroup_content_fun => "colgroup_content_fun"
  | .core_flow5 => "core_flow5"
  | .core_flow5_without_interactive => "core_flow5_without_interactive"
  | .core_flow5_without_media => "core_flow5_without_media"
  | .core_flow5_without_noscript => "core_flow5_without_noscript"
  | .core_phrasing => "core_phrasing"
  | .core_phrasing_without_interactive => "core_phrasing_without_interactive"
  | .core_phrasing_without_media => "core_phrasing_without_media"
  | .core_phrasing_without_noscript => "core_phrasing_without_noscript"
  | .dl_content_fun => "dl_content_fun"
  | .flow5 => "flow5"
  | .flow5_without_form => "flow5_without_form"
  | .flow5_without_header_footer => "flow5_without_header_footer"
  | .flow5_without_interactive => "flow5_without_interactive"
  | .flow5_without_interactive_header_footer => "flow5_without_interactive_header_footer"
  | .flow5_without_media => "flow5_without_media"
  | .flow5_without_noscript => "flow5_without_noscript"
  | .flow5_without_sectioning_heading_header_footer => "flow5_without_sectioning_heading_header_footer"
  | .flow5_without_sectioning_heading_header_footer_address => "flow5_without_sectioning_heading_header_footer_address"
  | .flow5_without_table => "flow5_without_table"
  | .formassociated => "formassociated"
  | .formatblock => "formatblock"
  | .heading => "heading"
  | .hgroup_content_fun => "hgroup_content_fun"
  | .html_content_fun => "html_content_fun"
  | .iframe_content_fun => "iframe_content_fun"
  | .labelable => "labelable"
  | .labelable_without_interactive => "labelable_without_interactive"
  | .listed => "listed"
  | .metadata_without_title => "metadata_without_title"
  | .notag => "notag"
  | .ol_content_fun => "ol_content_fun"
  | .optgroup_content_fun => "optgroup_content_fun"
  | .option_content_fun => "option_content_fun"
  | .phrasing => "phrasing"
  | .phrasing_without_dfn => "phrasing_without_dfn"
  | .phrasing_without_interactive => "phrasing_without_interactive"
  | .phrasing_without_label => "phrasing_without_label"
  | .phrasing_without_media => "phrasing_without_media"
  | .phrasing_without_meter => "phrasing_without_meter"
  | .phrasing_without_noscript => "phrasing_without_noscript"
  | .phrasing_without_progress => "phrasing_without_progress"
  | .phrasing_without_time => "phrasing_without_time"
  | .picture_content_fun => "picture_content_fun"
  | .resetable => "resetable"
  | .rp => "rp"
  | .rt => "rt"
  | .ruby_content_fun => "ruby_content_fun"
  | .script => "script"
  | .script_content_fun => "script_content_fun"
  | .sectioning => "sectioning"
  | .select_content_fun => "select_content_fun"
  | .source => "source"
  | .style_content_fun => "style_content_fun"
  | .submitable => "submitable"
  | .table_content_fun => "table_content_fun"
  | .tablex_content_fun => "tablex_content_fun"
  | .tbody_content_fun => "tbody_content_fun"
  | .template => "template"
  | .textarea_content => "textarea_content"
  | .tfoot_content_fun => "tfoot_content_fun"
  | .thead_content_fun => "thead_content_fun"
  | .title_content_fun => "title_content_fun"
  | .tr_content_fun => "tr_content_fun"
  | .transparent => "transparent"
  | .transparent_without_interactive => "transparent_without_interactive"
  | .transparent_without_media => "transparent_without_media"
  | .transparent_without_noscript => "transparent_without_noscript"
  | .ul_content_fun => "ul_content_fun"

/-- Membership, dispatching to the set's own function. -/
def ContentSet.contains : ContentSet → Tag → Bool
  | .colgroup_content_fun, t => Sets.colgroup_content_fun t
  | .core_flow5, t => Sets.core_flow5 t
  | .core_flow5_without_interactive, t => Sets.core_flow5_without_interactive t
  | .core_flow5_without_media, t => Sets.core_flow5_without_media t
  | .core_flow5_without_noscript, t => Sets.core_flow5_without_noscript t
  | .core_phrasing, t => Sets.core_phrasing t
  | .core_phrasing_without_interactive, t => Sets.core_phrasing_without_interactive t
  | .core_phrasing_without_media, t => Sets.core_phrasing_without_media t
  | .core_phrasing_without_noscript, t => Sets.core_phrasing_without_noscript t
  | .dl_content_fun, t => Sets.dl_content_fun t
  | .flow5, t => Sets.flow5 t
  | .flow5_without_form, t => Sets.flow5_without_form t
  | .flow5_without_header_footer, t => Sets.flow5_without_header_footer t
  | .flow5_without_interactive, t => Sets.flow5_without_interactive t
  | .flow5_without_interactive_header_footer, t => Sets.flow5_without_interactive_header_footer t
  | .flow5_without_media, t => Sets.flow5_without_media t
  | .flow5_without_noscript, t => Sets.flow5_without_noscript t
  | .flow5_without_sectioning_heading_header_footer, t => Sets.flow5_without_sectioning_heading_header_footer t
  | .flow5_without_sectioning_heading_header_footer_address, t => Sets.flow5_without_sectioning_heading_header_footer_address t
  | .flow5_without_table, t => Sets.flow5_without_table t
  | .formassociated, t => Sets.formassociated t
  | .formatblock, t => Sets.formatblock t
  | .heading, t => Sets.heading t
  | .hgroup_content_fun, t => Sets.hgroup_content_fun t
  | .html_content_fun, t => Sets.html_content_fun t
  | .iframe_content_fun, t => Sets.iframe_content_fun t
  | .labelable, t => Sets.labelable t
  | .labelable_without_interactive, t => Sets.labelable_without_interactive t
  | .listed, t => Sets.listed t
  | .metadata_without_title, t => Sets.metadata_without_title t
  | .notag, t => Sets.notag t
  | .ol_content_fun, t => Sets.ol_content_fun t
  | .optgroup_content_fun, t => Sets.optgroup_content_fun t
  | .option_content_fun, t => Sets.option_content_fun t
  | .phrasing, t => Sets.phrasing t
  | .phrasing_without_dfn, t => Sets.phrasing_without_dfn t
  | .phrasing_without_interactive, t => Sets.phrasing_without_interactive t
  | .phrasing_without_label, t => Sets.phrasing_without_label t
  | .phrasing_without_media, t => Sets.phrasing_without_media t
  | .phrasing_without_meter, t => Sets.phrasing_without_meter t
  | .phrasing_without_noscript, t => Sets.phrasing_without_noscript t
  | .phrasing_without_progress, t => Sets.phrasing_without_progress t
  | .phrasing_without_time, t => Sets.phrasing_without_time t
  | .picture_content_fun, t => Sets.picture_content_fun t
  | .resetable, t => Sets.resetable t
  | .rp, t => Sets.rp t
  | .rt, t => Sets.rt t
  | .ruby_content_fun, t => Sets.ruby_content_fun t
  | .script, t => Sets.script t
  | .script_content_fun, t => Sets.script_content_fun t
  | .sectioning, t => Sets.sectioning t
  | .select_content_fun, t => Sets.select_content_fun t
  | .source, t => Sets.source t
  | .style_content_fun, t => Sets.style_content_fun t
  | .submitable, t => Sets.submitable t
  | .table_content_fun, t => Sets.table_content_fun t
  | .tablex_content_fun, t => Sets.tablex_content_fun t
  | .tbody_content_fun, t => Sets.tbody_content_fun t
  | .template, t => Sets.template t
  | .textarea_content, t => Sets.textarea_content t
  | .tfoot_content_fun, t => Sets.tfoot_content_fun t
  | .thead_content_fun, t => Sets.thead_content_fun t
  | .title_content_fun, t => Sets.title_content_fun t
  | .tr_content_fun, t => Sets.tr_content_fun t
  | .transparent, t => Sets.transparent t
  | .transparent_without_interactive, t => Sets.transparent_without_interactive t
  | .transparent_without_media, t => Sets.transparent_without_media t
  | .transparent_without_noscript, t => Sets.transparent_without_noscript t
  | .ul_content_fun, t => Sets.ul_content_fun t

/-- The transparent payloads of `colgroup_content_fun`: 0 of 115 tags carry one. -/
def Payloads.colgroup_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_flow5`: 0 of 115 tags carry one. -/
def Payloads.core_flow5 : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_flow5_without_interactive`: 0 of 115 tags carry one. -/
def Payloads.core_flow5_without_interactive : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_flow5_without_media`: 0 of 115 tags carry one. -/
def Payloads.core_flow5_without_media : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_flow5_without_noscript`: 0 of 115 tags carry one. -/
def Payloads.core_flow5_without_noscript : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_phrasing`: 0 of 115 tags carry one. -/
def Payloads.core_phrasing : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_phrasing_without_interactive`: 0 of 115 tags carry one. -/
def Payloads.core_phrasing_without_interactive : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_phrasing_without_media`: 0 of 115 tags carry one. -/
def Payloads.core_phrasing_without_media : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `core_phrasing_without_noscript`: 0 of 115 tags carry one. -/
def Payloads.core_phrasing_without_noscript : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `dl_content_fun`: 0 of 115 tags carry one. -/
def Payloads.dl_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `flow5`: 12 of 115 tags carry one. -/
def Payloads.flow5 : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_form`: 12 of 115 tags carry one. -/
def Payloads.flow5_without_form : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_header_footer`: 12 of 115 tags carry one. -/
def Payloads.flow5_without_header_footer : Tag → Option ContentSet
  | .a => some .flow5_without_interactive_header_footer
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_interactive`: 8 of 115 tags carry one. -/
def Payloads.flow5_without_interactive : Tag → Option ContentSet
  | .noscript => some .flow5_without_noscript
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .canvas => some .flow5
  | .map => some .flow5
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_interactive_header_footer`: 8 of 115 tags carry one. -/
def Payloads.flow5_without_interactive_header_footer : Tag → Option ContentSet
  | .noscript => some .flow5_without_noscript
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .canvas => some .flow5
  | .map => some .flow5
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_media`: 8 of 115 tags carry one. -/
def Payloads.flow5_without_media : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .ins => some .flow5
  | .del => some .flow5
  | .map => some .flow5
  | .canvas => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | _ => none

/-- The transparent payloads of `flow5_without_noscript`: 11 of 115 tags carry one. -/
def Payloads.flow5_without_noscript : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .ins => some .flow5
  | .del => some .flow5
  | .canvas => some .flow5
  | .map => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .video => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio_interactive => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_sectioning_heading_header_footer`: 12 of 115 tags carry one. -/
def Payloads.flow5_without_sectioning_heading_header_footer : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_sectioning_heading_header_footer_address`: 12 of 115 tags carry one. -/
def Payloads.flow5_without_sectioning_heading_header_footer_address : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `flow5_without_table`: 12 of 115 tags carry one. -/
def Payloads.flow5_without_table : Tag → Option ContentSet
  | .a => some .flow5_without_interactive
  | .noscript => some .flow5_without_noscript
  | .canvas => some .flow5
  | .map => some .flow5
  | .ins => some .flow5
  | .del => some .flow5
  | .object => some .flow5
  | .object_interactive => some .flow5
  | .audio_interactive => some .flow5_without_media
  | .video_interactive => some .flow5_without_media
  | .audio => some .flow5_without_media
  | .video => some .flow5_without_media
  | _ => none

/-- The transparent payloads of `formassociated`: 0 of 115 tags carry one. -/
def Payloads.formassociated : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `formatblock`: 0 of 115 tags carry one. -/
def Payloads.formatblock : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `heading`: 0 of 115 tags carry one. -/
def Payloads.heading : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `hgroup_content_fun`: 0 of 115 tags carry one. -/
def Payloads.hgroup_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `html_content_fun`: 0 of 115 tags carry one. -/
def Payloads.html_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `iframe_content_fun`: 0 of 115 tags carry one. -/
def Payloads.iframe_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `labelable`: 0 of 115 tags carry one. -/
def Payloads.labelable : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `labelable_without_interactive`: 0 of 115 tags carry one. -/
def Payloads.labelable_without_interactive : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `listed`: 0 of 115 tags carry one. -/
def Payloads.listed : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `metadata_without_title`: 0 of 115 tags carry one. -/
def Payloads.metadata_without_title : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `notag`: 0 of 115 tags carry one. -/
def Payloads.notag : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `ol_content_fun`: 0 of 115 tags carry one. -/
def Payloads.ol_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `optgroup_content_fun`: 0 of 115 tags carry one. -/
def Payloads.optgroup_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `option_content_fun`: 0 of 115 tags carry one. -/
def Payloads.option_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `phrasing`: 12 of 115 tags carry one. -/
def Payloads.phrasing : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing
  | .map => some .phrasing
  | .ins => some .phrasing
  | .del => some .phrasing
  | .object => some .phrasing
  | .object_interactive => some .phrasing
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_dfn`: 12 of 115 tags carry one. -/
def Payloads.phrasing_without_dfn : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing_without_dfn
  | .map => some .phrasing_without_dfn
  | .ins => some .phrasing_without_dfn
  | .del => some .phrasing_without_dfn
  | .object => some .phrasing_without_dfn
  | .object_interactive => some .phrasing_without_dfn
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_interactive`: 8 of 115 tags carry one. -/
def Payloads.phrasing_without_interactive : Tag → Option ContentSet
  | .noscript => some .phrasing_without_noscript
  | .ins => some .phrasing
  | .del => some .phrasing
  | .object => some .phrasing
  | .canvas => some .phrasing
  | .map => some .phrasing
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_label`: 12 of 115 tags carry one. -/
def Payloads.phrasing_without_label : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing_without_label
  | .map => some .phrasing_without_label
  | .ins => some .phrasing_without_label
  | .del => some .phrasing_without_label
  | .object => some .phrasing_without_label
  | .object_interactive => some .phrasing_without_label
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_media`: 8 of 115 tags carry one. -/
def Payloads.phrasing_without_media : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .ins => some .phrasing
  | .del => some .phrasing
  | .map => some .phrasing
  | .canvas => some .phrasing
  | .object => some .phrasing
  | .object_interactive => some .phrasing
  | _ => none

/-- The transparent payloads of `phrasing_without_meter`: 12 of 115 tags carry one. -/
def Payloads.phrasing_without_meter : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing_without_meter
  | .map => some .phrasing_without_meter
  | .ins => some .phrasing_without_meter
  | .del => some .phrasing_without_meter
  | .object => some .phrasing_without_meter
  | .object_interactive => some .phrasing_without_meter
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_noscript`: 11 of 115 tags carry one. -/
def Payloads.phrasing_without_noscript : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .ins => some .phrasing
  | .del => some .phrasing
  | .canvas => some .phrasing
  | .map => some .phrasing
  | .object => some .phrasing
  | .object_interactive => some .phrasing
  | .video => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio_interactive => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_progress`: 12 of 115 tags carry one. -/
def Payloads.phrasing_without_progress : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing_without_progress
  | .map => some .phrasing_without_progress
  | .ins => some .phrasing_without_progress
  | .del => some .phrasing_without_progress
  | .object => some .phrasing_without_progress
  | .object_interactive => some .phrasing_without_progress
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `phrasing_without_time`: 12 of 115 tags carry one. -/
def Payloads.phrasing_without_time : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing_without_time
  | .map => some .phrasing_without_time
  | .ins => some .phrasing_without_time
  | .del => some .phrasing_without_time
  | .object => some .phrasing_without_time
  | .object_interactive => some .phrasing_without_time
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `picture_content_fun`: 0 of 115 tags carry one. -/
def Payloads.picture_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `resetable`: 0 of 115 tags carry one. -/
def Payloads.resetable : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `rp`: 0 of 115 tags carry one. -/
def Payloads.rp : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `rt`: 0 of 115 tags carry one. -/
def Payloads.rt : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `ruby_content_fun`: 12 of 115 tags carry one. -/
def Payloads.ruby_content_fun : Tag → Option ContentSet
  | .a => some .phrasing_without_interactive
  | .noscript => some .phrasing_without_noscript
  | .canvas => some .phrasing
  | .map => some .phrasing
  | .ins => some .phrasing
  | .del => some .phrasing
  | .object => some .phrasing
  | .object_interactive => some .phrasing
  | .audio_interactive => some .phrasing_without_media
  | .video_interactive => some .phrasing_without_media
  | .audio => some .phrasing_without_media
  | .video => some .phrasing_without_media
  | _ => none

/-- The transparent payloads of `script`: 0 of 115 tags carry one. -/
def Payloads.script : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `script_content_fun`: 0 of 115 tags carry one. -/
def Payloads.script_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `sectioning`: 0 of 115 tags carry one. -/
def Payloads.sectioning : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `select_content_fun`: 0 of 115 tags carry one. -/
def Payloads.select_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `source`: 0 of 115 tags carry one. -/
def Payloads.source : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `style_content_fun`: 0 of 115 tags carry one. -/
def Payloads.style_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `submitable`: 0 of 115 tags carry one. -/
def Payloads.submitable : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `table_content_fun`: 0 of 115 tags carry one. -/
def Payloads.table_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `tablex_content_fun`: 0 of 115 tags carry one. -/
def Payloads.tablex_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `tbody_content_fun`: 0 of 115 tags carry one. -/
def Payloads.tbody_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `template`: 0 of 115 tags carry one. -/
def Payloads.template : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `textarea_content`: 0 of 115 tags carry one. -/
def Payloads.textarea_content : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `tfoot_content_fun`: 0 of 115 tags carry one. -/
def Payloads.tfoot_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `thead_content_fun`: 0 of 115 tags carry one. -/
def Payloads.thead_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `title_content_fun`: 0 of 115 tags carry one. -/
def Payloads.title_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `tr_content_fun`: 0 of 115 tags carry one. -/
def Payloads.tr_content_fun : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `transparent`: 0 of 115 tags carry one. -/
def Payloads.transparent : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `transparent_without_interactive`: 0 of 115 tags carry one. -/
def Payloads.transparent_without_interactive : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `transparent_without_media`: 0 of 115 tags carry one. -/
def Payloads.transparent_without_media : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `transparent_without_noscript`: 0 of 115 tags carry one. -/
def Payloads.transparent_without_noscript : Tag → Option ContentSet
  | _ => none

/-- The transparent payloads of `ul_content_fun`: 0 of 115 tags carry one. -/
def Payloads.ul_content_fun : Tag → Option ContentSet
  | _ => none

/-- TyXML's transparent rule: the content set the payload of a transparent
tag assigns to that element's children when it appears in the given set
(`` `A of flow5_without_interactive `` inside `flow5`, so a link in flow
context may not contain interactive content). `none` when the set names the
tag without a content-set payload (ruling HP-4). Dispatches to the set's
own `Payloads` function, as `contains` does to `Sets`, so that reducing one
lookup instantiates a matcher of one set's rows rather than of all 69 sets'
rows at once; the child-set resolver of the typed tree is reduced by the
elaborator at every element node. -/
def ContentSet.transparentPayload : ContentSet → Tag → Option ContentSet
  | .colgroup_content_fun, t => Payloads.colgroup_content_fun t
  | .core_flow5, t => Payloads.core_flow5 t
  | .core_flow5_without_interactive, t => Payloads.core_flow5_without_interactive t
  | .core_flow5_without_media, t => Payloads.core_flow5_without_media t
  | .core_flow5_without_noscript, t => Payloads.core_flow5_without_noscript t
  | .core_phrasing, t => Payloads.core_phrasing t
  | .core_phrasing_without_interactive, t => Payloads.core_phrasing_without_interactive t
  | .core_phrasing_without_media, t => Payloads.core_phrasing_without_media t
  | .core_phrasing_without_noscript, t => Payloads.core_phrasing_without_noscript t
  | .dl_content_fun, t => Payloads.dl_content_fun t
  | .flow5, t => Payloads.flow5 t
  | .flow5_without_form, t => Payloads.flow5_without_form t
  | .flow5_without_header_footer, t => Payloads.flow5_without_header_footer t
  | .flow5_without_interactive, t => Payloads.flow5_without_interactive t
  | .flow5_without_interactive_header_footer, t => Payloads.flow5_without_interactive_header_footer t
  | .flow5_without_media, t => Payloads.flow5_without_media t
  | .flow5_without_noscript, t => Payloads.flow5_without_noscript t
  | .flow5_without_sectioning_heading_header_footer, t => Payloads.flow5_without_sectioning_heading_header_footer t
  | .flow5_without_sectioning_heading_header_footer_address, t => Payloads.flow5_without_sectioning_heading_header_footer_address t
  | .flow5_without_table, t => Payloads.flow5_without_table t
  | .formassociated, t => Payloads.formassociated t
  | .formatblock, t => Payloads.formatblock t
  | .heading, t => Payloads.heading t
  | .hgroup_content_fun, t => Payloads.hgroup_content_fun t
  | .html_content_fun, t => Payloads.html_content_fun t
  | .iframe_content_fun, t => Payloads.iframe_content_fun t
  | .labelable, t => Payloads.labelable t
  | .labelable_without_interactive, t => Payloads.labelable_without_interactive t
  | .listed, t => Payloads.listed t
  | .metadata_without_title, t => Payloads.metadata_without_title t
  | .notag, t => Payloads.notag t
  | .ol_content_fun, t => Payloads.ol_content_fun t
  | .optgroup_content_fun, t => Payloads.optgroup_content_fun t
  | .option_content_fun, t => Payloads.option_content_fun t
  | .phrasing, t => Payloads.phrasing t
  | .phrasing_without_dfn, t => Payloads.phrasing_without_dfn t
  | .phrasing_without_interactive, t => Payloads.phrasing_without_interactive t
  | .phrasing_without_label, t => Payloads.phrasing_without_label t
  | .phrasing_without_media, t => Payloads.phrasing_without_media t
  | .phrasing_without_meter, t => Payloads.phrasing_without_meter t
  | .phrasing_without_noscript, t => Payloads.phrasing_without_noscript t
  | .phrasing_without_progress, t => Payloads.phrasing_without_progress t
  | .phrasing_without_time, t => Payloads.phrasing_without_time t
  | .picture_content_fun, t => Payloads.picture_content_fun t
  | .resetable, t => Payloads.resetable t
  | .rp, t => Payloads.rp t
  | .rt, t => Payloads.rt t
  | .ruby_content_fun, t => Payloads.ruby_content_fun t
  | .script, t => Payloads.script t
  | .script_content_fun, t => Payloads.script_content_fun t
  | .sectioning, t => Payloads.sectioning t
  | .select_content_fun, t => Payloads.select_content_fun t
  | .source, t => Payloads.source t
  | .style_content_fun, t => Payloads.style_content_fun t
  | .submitable, t => Payloads.submitable t
  | .table_content_fun, t => Payloads.table_content_fun t
  | .tablex_content_fun, t => Payloads.tablex_content_fun t
  | .tbody_content_fun, t => Payloads.tbody_content_fun t
  | .template, t => Payloads.template t
  | .textarea_content, t => Payloads.textarea_content t
  | .tfoot_content_fun, t => Payloads.tfoot_content_fun t
  | .thead_content_fun, t => Payloads.thead_content_fun t
  | .title_content_fun, t => Payloads.title_content_fun t
  | .tr_content_fun, t => Payloads.tr_content_fun t
  | .transparent, t => Payloads.transparent t
  | .transparent_without_interactive, t => Payloads.transparent_without_interactive t
  | .transparent_without_media, t => Payloads.transparent_without_media t
  | .transparent_without_noscript, t => Payloads.transparent_without_noscript t
  | .ul_content_fun, t => Payloads.ul_content_fun t

end Whatwg.Html.Schema
