import Whatwg.Css.Data.Pairs
import Whatwg.Css.Syntax.Tree
import Whatwg.Css.Syntax.Tokenize
import Whatwg.Css.Syntax.Serialize
import Whatwg.Css.Syntax.Laws
import Whatwg.Css.Syntax.Write
import Whatwg.Css.Syntax.Parse
import Whatwg.Css.Syntax.Readable
import Whatwg.Css.Syntax.Readable.Append
import Whatwg.Css.Syntax.Located
import Whatwg.Css.Syntax.Parse.Component
import Whatwg.Css.Syntax.Parse.Declaration
import Whatwg.Css.Syntax.Parse.Step
import Whatwg.Css.Syntax.Parse.Rule
import Whatwg.Css.Syntax.Parse.Laws
import Whatwg.Css.Syntax.Parse.Lines
import Whatwg.Css.Syntax.Build
import Whatwg.Css.Syntax.Build.Laws
import Whatwg.Css.Values.Definition
import Whatwg.Css.Values.Definition.Lex
import Whatwg.Css.Values.Definition.Laws
import Whatwg.Css.Values.Admits
import Whatwg.Css.Values.Admits.Laws

/-!
# Whatwg.Css

CSS adopted as data (`docs/CSS-PACKAGE-PLAN.md`). The authority is the sealed Bikeshed source of
each module under `vendor/w3c-csswg-drafts-50337328/`. At slice K1 the library holds what the
extractor writes for a later slice to read: `Whatwg/Css/Data/Pairs.lean`, the pairs of tokens
that CSS Syntax 3 says need a comment between them when they are serialized. The model of the
tokenizer, the writer of tokens and their round trip came with slice K2
(`Whatwg/Css/Syntax/`, graph `CSS-PG-SYNTAX`). Slice K3 gave the tree of tokens and component values
(`Whatwg/Css/Syntax/Tree.lean`) and the value definition syntax as data: its tree, one reader and
printer, and the interpreter that says which values a definition admits
(`Whatwg/Css/Values/`).
-/
