import Whatwg.Html.Syntax.Elaborator

/-!
# WhatwgTest.Html.SvgBenchmark

The cost bound of slice S6 of `docs/SVG-PACKAGE-PLAN.md` (ruling SV-36): a picture of 100
`rect` elements with eight attributes each, written through `html!`. The picture is the shape
that lean4-effect4's picture writer emits for a chart of filled boxes.

Before slice S6 the kernel checked the structure of such a subtree by running the checker over
its written names. It now evaluates `SvgNode.okIn` over the typed tree, which reads tags and
keys. Measured on this pin, on one PC:

| Obligation | Kernel time, 100 elements | Kernel time, 300 elements |
| --- | --- | --- |
| `validIn` of the raw tree: the checker over the written names (before S6) | 2.44 s | 8.06 s |
| `okIn` of the typed tree, with the law `SvgNode.validIn_of_okIn` (S6) | 0.05 s | 0.16 s |

In the units of `maxHeartbeats`, a thousand heartbeats, by bisection on the 100 elements:

| What is bounded | Fails at | Passes at | Bound set here |
| --- | --- | --- | --- |
| the whole declaration below: elaboration and the kernel's check of `okIn` | 80 | 90 | 200 |
| the old obligation alone, `validIn Ctx.flow pic.raw = true` by the kernel | 1600 | 3200 | not pinned |

The option's default is 200000 of these units. The bound carries a margin so that ordinary
variation between machines does not turn the gate red.

Reading. A name costs the kernel some milliseconds to decode, because a string is a byte array
with a proof, and the checker decodes each name several times. A tag and a key are constructors
and a mask test is one shift, so `okIn` costs about half a millisecond for an element with
eight attributes.

These are finite probes about this picture, not a theorem about the elaborator.
-/

namespace WhatwgTest.Html.SvgBenchmark

open Whatwg.Html
open Whatwg.Html.Content (Ctx)

set_option maxHeartbeats 200 in
noncomputable example : Child Ctx.flow :=
  html! <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 400">
    <rect class="e4-fill-a" x="0" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k0" />
    <rect class="e4-fill-a" x="1" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k1" />
    <rect class="e4-fill-a" x="2" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k2" />
    <rect class="e4-fill-a" x="3" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k3" />
    <rect class="e4-fill-a" x="4" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k4" />
    <rect class="e4-fill-a" x="5" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k5" />
    <rect class="e4-fill-a" x="6" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k6" />
    <rect class="e4-fill-a" x="7" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k7" />
    <rect class="e4-fill-a" x="8" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k8" />
    <rect class="e4-fill-a" x="9" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k9" />
    <rect class="e4-fill-a" x="10" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k10" />
    <rect class="e4-fill-a" x="11" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k11" />
    <rect class="e4-fill-a" x="12" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k12" />
    <rect class="e4-fill-a" x="13" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k13" />
    <rect class="e4-fill-a" x="14" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k14" />
    <rect class="e4-fill-a" x="15" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k15" />
    <rect class="e4-fill-a" x="16" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k16" />
    <rect class="e4-fill-a" x="17" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k17" />
    <rect class="e4-fill-a" x="18" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k18" />
    <rect class="e4-fill-a" x="19" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k19" />
    <rect class="e4-fill-a" x="20" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k20" />
    <rect class="e4-fill-a" x="21" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k21" />
    <rect class="e4-fill-a" x="22" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k22" />
    <rect class="e4-fill-a" x="23" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k23" />
    <rect class="e4-fill-a" x="24" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k24" />
    <rect class="e4-fill-a" x="25" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k25" />
    <rect class="e4-fill-a" x="26" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k26" />
    <rect class="e4-fill-a" x="27" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k27" />
    <rect class="e4-fill-a" x="28" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k28" />
    <rect class="e4-fill-a" x="29" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k29" />
    <rect class="e4-fill-a" x="30" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k30" />
    <rect class="e4-fill-a" x="31" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k31" />
    <rect class="e4-fill-a" x="32" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k32" />
    <rect class="e4-fill-a" x="33" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k33" />
    <rect class="e4-fill-a" x="34" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k34" />
    <rect class="e4-fill-a" x="35" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k35" />
    <rect class="e4-fill-a" x="36" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k36" />
    <rect class="e4-fill-a" x="37" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k37" />
    <rect class="e4-fill-a" x="38" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k38" />
    <rect class="e4-fill-a" x="39" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k39" />
    <rect class="e4-fill-a" x="40" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k40" />
    <rect class="e4-fill-a" x="41" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k41" />
    <rect class="e4-fill-a" x="42" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k42" />
    <rect class="e4-fill-a" x="43" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k43" />
    <rect class="e4-fill-a" x="44" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k44" />
    <rect class="e4-fill-a" x="45" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k45" />
    <rect class="e4-fill-a" x="46" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k46" />
    <rect class="e4-fill-a" x="47" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k47" />
    <rect class="e4-fill-a" x="48" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k48" />
    <rect class="e4-fill-a" x="49" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k49" />
    <rect class="e4-fill-a" x="50" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k50" />
    <rect class="e4-fill-a" x="51" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k51" />
    <rect class="e4-fill-a" x="52" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k52" />
    <rect class="e4-fill-a" x="53" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k53" />
    <rect class="e4-fill-a" x="54" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k54" />
    <rect class="e4-fill-a" x="55" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k55" />
    <rect class="e4-fill-a" x="56" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k56" />
    <rect class="e4-fill-a" x="57" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k57" />
    <rect class="e4-fill-a" x="58" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k58" />
    <rect class="e4-fill-a" x="59" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k59" />
    <rect class="e4-fill-a" x="60" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k60" />
    <rect class="e4-fill-a" x="61" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k61" />
    <rect class="e4-fill-a" x="62" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k62" />
    <rect class="e4-fill-a" x="63" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k63" />
    <rect class="e4-fill-a" x="64" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k64" />
    <rect class="e4-fill-a" x="65" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k65" />
    <rect class="e4-fill-a" x="66" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k66" />
    <rect class="e4-fill-a" x="67" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k67" />
    <rect class="e4-fill-a" x="68" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k68" />
    <rect class="e4-fill-a" x="69" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k69" />
    <rect class="e4-fill-a" x="70" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k70" />
    <rect class="e4-fill-a" x="71" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k71" />
    <rect class="e4-fill-a" x="72" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k72" />
    <rect class="e4-fill-a" x="73" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k73" />
    <rect class="e4-fill-a" x="74" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k74" />
    <rect class="e4-fill-a" x="75" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k75" />
    <rect class="e4-fill-a" x="76" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k76" />
    <rect class="e4-fill-a" x="77" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k77" />
    <rect class="e4-fill-a" x="78" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k78" />
    <rect class="e4-fill-a" x="79" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k79" />
    <rect class="e4-fill-a" x="80" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k80" />
    <rect class="e4-fill-a" x="81" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k81" />
    <rect class="e4-fill-a" x="82" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k82" />
    <rect class="e4-fill-a" x="83" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k83" />
    <rect class="e4-fill-a" x="84" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k84" />
    <rect class="e4-fill-a" x="85" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k85" />
    <rect class="e4-fill-a" x="86" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k86" />
    <rect class="e4-fill-a" x="87" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k87" />
    <rect class="e4-fill-a" x="88" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k88" />
    <rect class="e4-fill-a" x="89" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k89" />
    <rect class="e4-fill-a" x="90" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k90" />
    <rect class="e4-fill-a" x="91" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k91" />
    <rect class="e4-fill-a" x="92" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k92" />
    <rect class="e4-fill-a" x="93" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k93" />
    <rect class="e4-fill-a" x="94" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k94" />
    <rect class="e4-fill-a" x="95" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k95" />
    <rect class="e4-fill-a" x="96" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k96" />
    <rect class="e4-fill-a" x="97" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k97" />
    <rect class="e4-fill-a" x="98" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k98" />
    <rect class="e4-fill-a" x="99" y="20" width="30" height="160" fill="var(--ink)" fill-opacity="0.8" data-key="k99" />
  </svg>

end WhatwgTest.Html.SvgBenchmark
