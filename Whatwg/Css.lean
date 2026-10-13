import Whatwg.Css.Data.Pairs

/-!
# Whatwg.Css

CSS adopted as data (`docs/CSS-PACKAGE-PLAN.md`). The authority is the sealed Bikeshed source of
each module under `vendor/w3c-csswg-drafts-50337328/`. At slice K1 the library holds what the
extractor writes for a later slice to read: `Whatwg/Css/Data/Pairs.lean`, the pairs of tokens
that CSS Syntax 3 says need a comment between them when they are serialized. The model of the
tokenizer and the reader of the value definition syntax come with slices K2 and K3.
-/
