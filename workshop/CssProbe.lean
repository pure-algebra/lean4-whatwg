import Whatwg.Html.Node.SvgMotion
import Whatwg.Html.Print.Picture
import Whatwg.Svg.Geometry.Outline

/-! A probe of the CSS that the picture kit writes: a step that one number scrubs, and the rule
of reduced motion. Since slice S22 the kit builds the tree of CSS and the text is the writer's of
that tree; the pages and the two files are, byte for byte, those that slice S17 wrote. Run it
from the repository root after `lake build`:

    lake env lean workshop/CssProbe.lean

It writes eight pages and two files beside them into the directory `out`. No module imports this
file, and no gate reads its output.

The step has a thing for each kind of change: a box that moves, a box that fades, a line that
draws itself by an easing that passes its end, two boxes that grow by one change under one
easing, and two lines that change their shape. The first of those lines has the same subpaths
at both ends, and the second starts a subpath at one end where it goes on at the other.

- `scrub-var.html`: the step paused and scrubbed by `--t`, with `--t: 400` on the root of the
  picture; beside it the step opened at the literal moment 400 and paused, and the kit's own
  still picture of that moment. The first two must compute the same styles.
- `scrub-literal.html`: the step opened at the literal moment 400 and paused, and the kit's
  still picture.
- `scrub-slider.html`: the scrubbed step under a slider that sets the one property.
- `reduced-always.html`: the step running, with the rule of reduced motion outside any `@media`,
  so that its effect shows with no setting; beside it the kit's still picture of the step's end.
  The two must compute the same styles at once.
- `reduced-media.html`: the same with the rule in `@media (prefers-reduced-motion: reduce)`. The
  page says whether the query matches where it is opened.

Each page reads the computed styles of its pictures with a small script and prints them side by
side, with the greatest difference. The script draws nothing: every picture is the kit's markup
and CSS as written.

Three more pages are of a page's policy (the consumer's ask W11 of
`docs/research/2026-10-12-whatwg-requests.md`). The consumer's site is served with
`Content-Security-Policy: default-src 'self'`, which refuses a `style` element, a `style`
attribute and a script that is inline, and takes a sheet and a script of the page's own origin
(from memory of that policy).

- `policy-inline.html`: the step the inline way, with no policy. It moves.
- `policy-linked.html`: the step by the sheet, with no policy: the page links `policy.css`, and
  the picture holds no `style`. It moves. Under it the same step by the sheet with the rule of
  reduced motion outside any `@media`: the rule must stand over the rules of the things, and
  the picture must show the step's end at once.
- `policy.html`: the policy, as a `meta` element, and three pictures: the inline one, which must
  stand still; the linked one, which must move; and a linked one that `--t` scrubs, whose
  property a rule of the file sets to 400 and a slider then sets through the object model.
- `policy.css`: the rules of the three steps by the sheet in one file, kept apart by their
  stems, after the page's own rules. `policy.js`: the script of the three pages, which fills a table of
  what each thing computes and listens to the slider.

Nothing of these three pages was opened in a browser by the seat that wrote them. -/

open Whatwg.Html
open Whatwg.Svg.Schema (Tag)
open Whatwg.Svg.Scene
open Whatwg.Svg.Value
open Whatwg.Css.Syntax (Prelude)

/-- Where the pages are written. -/
def out : System.FilePath := "docs/research/2026-10-12-motion-probe"

/-- lean4-effect4's critically damped spring. -/
def settle : Easing :=
  .stops [0, 54, 171, 306, 438, 555, 654, 734, 799, 849, 888, 918, 941, 958, 970, 980, 986, 992,
    995, 998, 1000]

/-- lean4-effect4's underdamped spring. -/
def spring : Easing :=
  .stops [0, 59, 195, 363, 531, 681, 804, 898, 964, 1007, 1032, 1043, 1045, 1041, 1034, 1026,
    1019, 1012, 1007, 1003, 1000]

/-- A line of two segments, before and after: the same subpaths at both ends. -/
def edgeFrom : List ICubic :=
  [⟨⟨20, 150⟩, ⟨40, 130⟩, ⟨60, 130⟩, ⟨80, 150⟩⟩, ⟨⟨80, 150⟩, ⟨100, 170⟩, ⟨120, 170⟩, ⟨140, 150⟩⟩]

def edgeTo : List ICubic :=
  [⟨⟨20, 160⟩, ⟨40, 180⟩, ⟨60, 180⟩, ⟨80, 160⟩⟩, ⟨⟨80, 160⟩, ⟨100, 140⟩, ⟨120, 140⟩, ⟨140, 160⟩⟩]

/-- A line of two segments that is in two parts before, with ten units between them, and in one
part after. -/
def gapFrom : List ICubic :=
  [⟨⟨190, 150⟩, ⟨210, 130⟩, ⟨230, 130⟩, ⟨250, 150⟩⟩, ⟨⟨260, 150⟩, ⟨280, 170⟩, ⟨300, 170⟩, ⟨320, 150⟩⟩]

def gapTo : List ICubic :=
  [⟨⟨190, 160⟩, ⟨210, 180⟩, ⟨230, 180⟩, ⟨255, 160⟩⟩, ⟨⟨255, 160⟩, ⟨280, 140⟩, ⟨300, 140⟩, ⟨320, 160⟩⟩]

/-- The step: a track for each kind of change. -/
def step : Motion String :=
  [⟨"a", .shift ⟨-60, 0⟩ 0, { duration := 450, ease := settle }⟩,
    ⟨"b", .fade 1000 0, { duration := 600, ease := Easing.cubicIn }⟩,
    ⟨"r", .reveal 0 1000, { delay := 100, duration := 400, ease := Easing.backOut }⟩,
    ⟨"c", .grow 0 1000, { delay := 300, duration := 300, ease := spring }⟩,
    ⟨"d", .grow 0 1000, { delay := 600, duration := 300, ease := spring }⟩,
    ⟨"e", .morph edgeFrom edgeTo, { duration := 600, ease := settle }⟩,
    ⟨"f", .morph gapFrom gapTo, { duration := 600, ease := settle }⟩]

/-- How the step is played: 1600 ms, so that an eye can follow it. -/
def play : Play := { step := 1600 }

/-- The moment that the still pages show. -/
def moment : Nat := 400

def ink : Rgb := .ofNat 0xf3f4f6
def ground : Rgb := .ofNat 0x14110d

/-- A thing of the picture: its key, its own declarations, and its element under the attributes
that a step gives it. -/
structure Thing where
  key : String
  own : Css.Decls
  node : ({t : Tag} → List (SvgAttr t)) → SvgNode

def boxThing (key : String) (x y : Int) (own : Css.Decls := []) : Thing :=
  { key := key, own := own
    node := fun more =>
      Svg.box (.ofSize ⟨x, y⟩ 60 28) ([.fill (.rgb ink)] ++ SvgAttr.dataKey? key ++ more) }

def toCubic (c : ICubic) : Cubic :=
  ⟨⟨c.p0.x, c.p0.y⟩, ⟨c.p1.x, c.p1.y⟩, ⟨c.p2.x, c.p2.y⟩, ⟨c.p3.x, c.p3.y⟩⟩

def lineThing (key : String) (segments : List ICubic) : Thing :=
  { key := key, own := []
    node := fun more =>
      Svg.cubics (segments.map toCubic)
        ([.fill .none, .stroke (.rgb ink), .strokeWidth 3] ++ SvgAttr.dataKey? key ++ more) }

/-- The things as the next picture has them. The box `b` has a style of its own. -/
def things : List Thing :=
  [boxThing "a" 100 20, boxThing "b" 20 70 [("cursor", "pointer")],
    lineThing "r" [⟨⟨200, 20⟩, ⟨200, 40⟩, ⟨200, 60⟩, ⟨200, 80⟩⟩],
    boxThing "c" 240 20, boxThing "d" 240 60, lineThing "e" edgeTo, lineThing "f" gapTo]

/-- A picture: its identifier, the declarations on its root, a sheet where it has one, and each
thing under the attributes that `attrs` gives its key and its own declarations. -/
def picture (id : String) (root : Css.Decls) (sheet : Option SvgNode)
    (attrs : String → Css.Decls → ({t : Tag} → List (SvgAttr t))) : SvgNode :=
  Svg.svg
    ([.ident id, .attr .width (.user (.ofNat 360)), .attr .height (.user (.ofNat 200)),
      .attr .viewBox (ViewBox.ofSize 360 200)] ++ SvgAttr.decls? root)
    (sheet.toList ++ Svg.box (.ofSize ⟨0, 0⟩ 360 200) [.fill (.rgb ground)] ::
      things.map fun th => th.node (attrs th.key th.own))

/-- The step under a `Play`, with its sheet where `sheet`. -/
def played (id : String) (p : Play) (root : Css.Decls := []) (sheet : Bool := true) : SvgNode :=
  picture id root (if sheet then some (step.sheetNode p) else none) fun key own =>
    Motion.attrs step key p own

/-- The kit's own still picture of a moment: each pose as a declaration, with no animation. -/
def still (id : String) (t : Nat) : SvgNode :=
  picture id [] none fun key own => Motion.attrsAt step key t play own

/-- What the kit reads of each thing at a moment, as text. -/
def readings (t : Nat) : String :=
  "\n".intercalate (things.map fun th => th.key ++ ": " ++ (step.frame th.key t).css)

/-- The script of a page: it reads computed styles and prints two pictures side by side. -/
def script : String := r#"<script>
const poses = ['translate', 'scale', 'opacity', 'stroke-dashoffset', 'd'];
const times = ['animation-duration', 'animation-delay'];
const number = /-?(?:\d+\.?\d*|\.\d+)(?:e[-+]?\d+)?/gi;
// The cubic segments of a path of the commands M and C, each with its start: two paths of the
// same segments compare as the same, wherever each starts a subpath.
function segments(s) {
  const found = [];
  const command = /([MC])([^MC]*)/g;
  let m, at = [0, 0];
  while ((m = command.exec(s)) !== null) {
    const n = (m[2].match(number) || []).map(Number);
    if (m[1] === 'M') at = [n[0], n[1]];
    else for (let i = 0; i + 5 < n.length; i += 6) {
      found.push(at[0], at[1], n[i], n[i + 1], n[i + 2], n[i + 3], n[i + 4], n[i + 5]);
      at = [n[i + 4], n[i + 5]];
    }
  }
  return found;
}
function numbers(p, s) {
  if (p === 'd') return segments(s);
  const n = (s.match(number) || []).map(Number);
  if (p === 'translate') return [n[0] || 0, n[1] || 0];
  if (p === 'scale') return n.length ? [n[0], n.length > 1 ? n[1] : n[0]] : [1, 1];
  return n;
}
function gap(p, a, b) {
  const x = numbers(p, a), y = numbers(p, b);
  if (x.length !== y.length) return Infinity;
  let g = 0;
  for (let i = 0; i < x.length; i++) g = Math.max(g, Math.abs(x[i] - y[i]));
  return g;
}
function read(id, props) {
  const found = {};
  for (const el of document.getElementById(id).querySelectorAll('[data-key]')) {
    const cs = getComputedStyle(el);
    found[el.dataset.key] = props.map(p => cs.getPropertyValue(p));
  }
  return found;
}
function compare(left, right, table, withTimes) {
  const props = withTimes ? poses.concat(times) : poses;
  const a = read(left, props), b = read(right, props);
  let worst = 0;
  let rows = '<tr><th>thing</th><th>property</th><th>' + left + '</th><th>' + right +
    '</th><th>difference</th></tr>';
  for (const key of Object.keys(a)) {
    props.forEach((p, i) => {
      const u = a[key][i], v = b[key] ? b[key][i] : '';
      const g = gap(p, u, v);
      worst = Math.max(worst, g);
      rows += '<tr><td>' + key + '</td><td>' + p + '</td><td>' + u + '</td><td>' + v +
        '</td><td>' + g.toFixed(4) + '</td></tr>';
    });
  }
  rows += '<tr><th colspan="4">greatest difference</th><th>' + worst.toFixed(4) + '</th></tr>';
  document.getElementById(table).innerHTML = rows;
}
function afterFrames(f) { requestAnimationFrame(() => requestAnimationFrame(f)); }
</script>
"#

def head (title : String) : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n<title>" ++ title ++ "</title>\n" ++
    "<style>body { background: #14110d; color: #f3f4f6; font-family: Georgia, serif } " ++
    "h1, h2 { font-weight: 400 } table { border-collapse: collapse; font: 12px Menlo, monospace } " ++
    "td, th { border: 1px solid #555; padding: 2px 6px; text-align: left; max-width: 28em; " ++
    "overflow-wrap: anywhere } pre { font: 12px Menlo, monospace }</style>\n" ++
    "<h1>" ++ title ++ "</h1>\n" ++ script

def shown (caption : String) (node : SvgNode) : String :=
  "<h2>" ++ caption ++ "</h2>\n" ++ node.render ++ "\n"

def kitText (t : Nat) : String :=
  "<h2>What the kit reads at the moment " ++ toString t ++ "</h2>\n<pre>" ++ readings t ++
    "</pre>\n"

/-- The step paused and scrubbed, with `--t` on the root of its picture. -/
def scrubbedNode (id : String) (sheet : Bool) : SvgNode :=
  played id play.scrubbed (play.scrubbed.at moment) sheet

/-- The step opened at the literal moment and paused. -/
def openedNode (id : String) (sheet : Bool) : SvgNode :=
  played id { play with opened := moment, paused := true } [] sheet

def scrubVar : String :=
  head "A step that one number scrubs" ++
    "<p>Three pictures of the moment " ++ toString moment ++ " of one step. The first is paused, " ++
    "and each delay is a <code>calc()</code> of the custom property <code>--t</code>, which the " ++
    "root of the picture sets to " ++ toString moment ++ ". The second is opened at the literal " ++
    "moment and paused. The third is the kit's own reading, with no animation. The first two " ++
    "must compute the same styles, their times included. The kit rounds down, so the third " ++
    "differs by less than one count of a place or of a dash, and by less than two thousandths " ++
    "of a size or of an opacity.</p>\n" ++
    shown "scrubbed: <code>--t: 400</code> on the root" (scrubbedNode "scrubbed" true) ++
    shown "opened: the literal moment 400" (openedNode "opened" false) ++
    shown "kit: the reading, with no animation" (still "kit" moment) ++
    "<h2>scrubbed and opened</h2>\n<table id=\"same\"></table>\n" ++
    "<h2>scrubbed and the kit's reading</h2>\n<table id=\"read\"></table>\n" ++ kitText moment ++
    "<script>afterFrames(() => { compare('scrubbed', 'opened', 'same', true); " ++
    "compare('scrubbed', 'kit', 'read', false); });</script>\n"

def scrubLiteral : String :=
  head "A step opened at a literal moment" ++
    "<p>The moment " ++ toString moment ++ " of the step of <code>scrub-var.html</code>, opened " ++
    "at the literal moment and paused, and the kit's own reading of it. The first column of " ++
    "this table must be the first column of the tables of that page.</p>\n" ++
    shown "opened: the literal moment 400" (openedNode "opened" true) ++
    shown "kit: the reading, with no animation" (still "kit" moment) ++
    "<h2>opened and the kit's reading</h2>\n<table id=\"read\"></table>\n" ++ kitText moment ++
    "<script>afterFrames(() => compare('opened', 'kit', 'read', true));</script>\n"

def scrubSlider : String :=
  head "A slider scrubs a step" ++
    "<p>The step is paused, and the slider sets the one custom property <code>--t</code> on the " ++
    "root of the picture, from 0 to 1000. No script touches a thing.</p>\n" ++
    "<p><input type=\"range\" min=\"0\" max=\"1000\" value=\"" ++ toString moment ++
    "\" style=\"width:360px\" oninput=\"document.getElementById('scrubbed').style.setProperty(" ++
    "'--t', this.value); document.getElementById('at').textContent = this.value\"> " ++
    "<span id=\"at\">" ++ toString moment ++ "</span></p>\n" ++
    shown "scrubbed" (scrubbedNode "scrubbed" true)

def reducedPage (title intro : String) (reduce : Reduce) : String :=
  head title ++ intro ++
    "<p id=\"status\"></p>\n" ++
    shown "running: the step, under the rule" (played "running" { play with reduce := reduce }) ++
    shown "kit: the reading of the step's end, with no animation" (still "kit" 1000) ++
    "<h2>running and the kit's reading of the end, when the page is loaded</h2>\n" ++
    "<table id=\"first\"></table>\n" ++
    "<h2>the same, two seconds later, when the step is over</h2>\n<table id=\"last\"></table>\n" ++
    kitText 1000 ++
    "<script>document.getElementById('status').textContent = " ++
    "'(prefers-reduced-motion: reduce) ' + (matchMedia('(prefers-reduced-motion: reduce)').matches " ++
    "? 'matches' : 'does not match') + ' where this page is opened.'; " ++
    "afterFrames(() => compare('running', 'kit', 'first', true)); " ++
    "setTimeout(() => compare('running', 'kit', 'last', false), 2000);</script>\n"

def reducedAlways : String :=
  reducedPage "Reduced motion, with no setting"
    ("<p>The step runs, and the sheet has the rule of reduced motion outside any " ++
      "<code>@media</code>: every animation of a marked thing has a duration and a delay of " ++
      "nothing. So the picture must show the step's end at once, and both tables must be the " ++
      "same, with no difference: the first also says that each duration and each delay " ++
      "computes to nothing.</p>\n") .always

def reducedMedia : String :=
  reducedPage "Reduced motion, where a reader asked for it"
    ("<p>The step runs, and the rule of reduced motion stands in " ++
      "<code>@media (prefers-reduced-motion: reduce)</code>. Where the query matches, the page " ++
      "is as <code>reduced-always.html</code>. Where it does not, the step plays: the first " ++
      "table shows the start and has differences, and the second has none.</p>\n") .asked

/-! ## A page's policy

The same step, the inline way and by the sheet, and a page that carries the policy
`default-src 'self'`. Under it nothing inline is taken: the pages have no `style` element of
their own, no `style` attribute and no script but a file. -/

/-- The step the inline way, under the stem `i`. -/
def inlinePlay : Play := { play with stem := "i" }

/-- The step by the sheet, under the stem `p`. -/
def linkedPlay : Play := { play with stem := "p", reach := .sheet }

/-- The step by the sheet, paused and scrubbed by `--t`, under the stem `q`. -/
def scrubPlay : Play := ({ play with stem := "q", reach := .sheet } : Play).scrubbed

/-- The step by the sheet with the rule of reduced motion outside any `@media`, under the stem
`r`: the rule must stand over the rules of the things, which are in the same file. -/
def reducedPlay : Play := { play with stem := "r", reach := .sheet, reduce := .always }

/-- The own declarations of the thing with a key. -/
def ownOf (key : String) : Css.Decls :=
  ((things.find? fun th => th.key == key).map Thing.own).getD []

/-- The page's own rules. Under the policy they cannot stand in a `style` element. A selector
is built, or read from its text; a declaration is a pair of texts. -/
def pageRules : Css.Sheet :=
  [.style (Prelude.type "body")
      [("background", "#14110d"), ("color", "#f3f4f6"), ("font-family", "Georgia, serif")],
    .style (.ofText "h1, h2") [("font-weight", "400")],
    .style (Prelude.type "table")
      [("border-collapse", "collapse"), ("font", "12px Menlo, monospace")],
    .style (.ofText "td, th")
      [("border", "1px solid #555"), ("padding", "2px 6px"), ("text-align", "left")],
    .style (Prelude.type "input") [("width", "360px")]]

/-- **The file**: the page's rules, the rules of the step by the sheet, the rules of the
scrubbed step, the rule that puts the scrubbed step at its moment, and the rules of the step
under the rule of reduced motion. Three steps in one sheet: their stems keep them apart. -/
def policySheet : Css.Sheet :=
  pageRules ++ step.rules linkedPlay ownOf ++ step.rules scrubPlay ownOf ++
    scrubPlay.atRule moment (Prelude.id "scrubbed") ++ step.rules reducedPlay ownOf

/-- The script of the three pages, as a file of the page's own origin. -/
def policyScript : String := r#"// What each thing of each picture computes.
// A page under the policy default-src 'self' runs this file, which is of its own origin, and
// runs no script that is inline.
function report() {
  const table = document.getElementById('computed');
  if (!table) return;
  let rows = '<tr><th>picture</th><th>thing</th><th>has a style attribute</th>' +
    '<th>animation-name</th><th>animation-duration</th><th>play state</th>' +
    '<th>animations</th></tr>';
  for (const svg of document.querySelectorAll('svg[id]')) {
    for (const el of svg.querySelectorAll('[data-key]')) {
      const cs = getComputedStyle(el);
      rows += '<tr><td>' + svg.id + '</td><td>' + el.dataset.key + '</td><td>' +
        (el.hasAttribute('style') ? 'yes' : 'no') + '</td><td>' +
        cs.getPropertyValue('animation-name') + '</td><td>' +
        cs.getPropertyValue('animation-duration') + '</td><td>' +
        cs.getPropertyValue('animation-play-state') + '</td><td>' +
        el.getAnimations().length + '</td></tr>';
    }
  }
  table.innerHTML = rows;
  const scrubbed = document.getElementById('scrubbed');
  const says = document.getElementById('says');
  if (scrubbed && says) {
    says.textContent = getComputedStyle(scrubbed).getPropertyValue('--t').trim();
  }
}
window.addEventListener('load', () => {
  requestAnimationFrame(() => requestAnimationFrame(report));
  const slider = document.getElementById('slider');
  const scrubbed = document.getElementById('scrubbed');
  if (slider && scrubbed) slider.addEventListener('input', () => {
    scrubbed.style.setProperty('--t', slider.value);
    report();
  });
});
"#

/-- The head of a page of the policy: the policy where `policy`, and the one sheet. Nothing in
it is inline. -/
def policyHead (title : String) (policy : Bool) : String :=
  "<!doctype html>\n<meta charset=\"utf-8\">\n" ++
    (if policy then
      "<meta http-equiv=\"Content-Security-Policy\" content=\"default-src 'self'\">\n"
    else "") ++
    "<title>" ++ title ++ "</title>\n<link rel=\"stylesheet\" href=\"policy.css\">\n" ++
    "<h1>" ++ title ++ "</h1>\n"

/-- The foot of a page of the policy: the table that the script fills, and the script. -/
def policyFoot : String :=
  "<h2>What each thing computes</h2>\n<table id=\"computed\"></table>\n" ++
    "<script src=\"policy.js\"></script>\n"

/-- The step the inline way: a `style` element in the picture, and a `style` on each thing. -/
def inlineNode : SvgNode := played "inline" inlinePlay

/-- The step by the sheet: the picture holds no `style`. -/
def linkedNode : SvgNode := played "linked" linkedPlay [] false

/-- The scrubbed step by the sheet: the property is set by a rule of the file. -/
def scrubLinkedNode : SvgNode := played "scrubbed" scrubPlay [] false

/-- The step by the sheet under the rule of reduced motion. -/
def reducedLinkedNode : SvgNode := played "reduced" reducedPlay [] false

def policyInline : String :=
  policyHead "A step, the inline way" false ++
    "<p>The step with its rules in a <code>style</code> element of the picture and its " ++
    "declarations in a <code>style</code> attribute of each thing. This page has no policy, " ++
    "and the step must move.</p>\n" ++ shown "inline" inlineNode ++ policyFoot

def policyLinked : String :=
  policyHead "A step, by the sheet" false ++
    "<p>The same step with every rule in the file <code>policy.css</code>, which the page " ++
    "links, and each thing named by <code>data-track</code>. The picture holds no " ++
    "<code>style</code>. This page has no policy, and the step must move as the inline one " ++
    "does.</p>\n" ++ shown "linked" linkedNode ++
    "<p>The same step by the sheet, with the rule of reduced motion outside any " ++
    "<code>@media</code>. The rule and the rules of the things are in the one file. Its two " ++
    "declarations are important, so it must stand over them: each thing must compute a " ++
    "duration of <code>0s</code>, and the picture must show the step's end at once, as " ++
    "<code>reduced-always.html</code> does the inline way.</p>\n" ++
    shown "reduced: must show the end at once" reducedLinkedNode ++ policyFoot

def policyPage : String :=
  policyHead "A step under a page's policy" true ++
    "<p>This page carries the policy <code>default-src 'self'</code>, as a <code>meta</code> " ++
    "element. The first picture is the step the inline way: its <code>style</code> element and " ++
    "its <code>style</code> attributes are refused, so it must stand still, every thing as it " ++
    "is drawn. The second is the step by the sheet, and must move. The third is the step by " ++
    "the sheet, paused, and scrubbed by <code>--t</code>: a rule of the file sets the property " ++
    "to " ++ toString moment ++ ", and the slider sets it through the object model, from a " ++
    "script that is a file of this page's origin.</p>\n" ++
    shown "inline: must stand still" inlineNode ++ shown "linked: must move" linkedNode ++
    "<h2>scrubbed: <code>--t</code> is <span id=\"says\"></span></h2>\n" ++
    "<p><input id=\"slider\" type=\"range\" min=\"0\" max=\"1000\" value=\"" ++ toString moment ++
    "\"></p>\n" ++ scrubLinkedNode.render ++ "\n" ++ policyFoot

/-- Whether the markup of a picture holds a `style`, as an element or as an attribute. -/
def holdsStyle (node : SvgNode) : Bool := (node.render.splitOn "style").length > 1
#eval [holdsStyle inlineNode, holdsStyle linkedNode, holdsStyle scrubLinkedNode,
  holdsStyle reducedLinkedNode]
#eval IO.println
  (step.rules linkedPlay ownOf ++ scrubPlay.atRule moment (Prelude.id "scrubbed")).css
#eval IO.println (step.rules play).css
#eval (policySheet.writable, policySheet.quiet)
#eval things.map fun th => (th.key, (step.frame th.key moment).css, (step.frame th.key 1000).css)
#eval do
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "scrub-var.html") scrubVar
  IO.FS.writeFile (out / "scrub-literal.html") scrubLiteral
  IO.FS.writeFile (out / "scrub-slider.html") scrubSlider
  IO.FS.writeFile (out / "reduced-always.html") reducedAlways
  IO.FS.writeFile (out / "reduced-media.html") reducedMedia
  IO.FS.writeFile (out / "policy-inline.html") policyInline
  IO.FS.writeFile (out / "policy-linked.html") policyLinked
  IO.FS.writeFile (out / "policy.html") policyPage
  IO.FS.writeFile (out / "policy.css") (policySheet.css ++ "\n")
  IO.FS.writeFile (out / "policy.js") policyScript
