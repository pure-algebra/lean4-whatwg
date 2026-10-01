import Whatwg.Signatures.Ecma262

/-!
# Whatwg.Signatures

`Effects.Signature` faces of this package's stateful layers. A face states one
layer's first-order operations and total step function as an effect of the
`effects` package (`pure-algebra/lean4-effects` at `a4ee7a1`, tag `v0.8.0`),
with a canonical handler, a lens handler into any state that holds the layer's
state, a sum handler beside a consumer's own signature, and the step-fold the
handlers agree with. A face is an adapter: its semantics is the layer's step,
which lives in the layer's own library and imports no `Effects` module.

The tree exists so that the data model never needs `effects` to build (ruling
R-W3): `Whatwg.Signatures` and every module under it form the Lake library
`WhatwgSignatures`, the one production library that imports `effects`. The
tree is not called `Whatwg.Effects`, because inside a namespace
`Whatwg.Effects.X` the name `Effects.Handler` would resolve to
`Whatwg.Effects.Handler` as soon as that existed.

Landed:

- `Whatwg/Signatures/Ecma262.lean` — promise slice Q5 (`PROMISE-PG-AGENT`,
  `test/contracts/promise-agent-q5.contract.md`): the ECMAScript agent of
  `Whatwg.Ecma262.Agent` as the signature `Whatwg.Signatures.Ecma262.signature`,
  with its canonical, lens and sum handlers, `run`, the four handler–step
  agreement laws, and "a promise resolved with" as a program. It imports
  `Effects.Algebra.Sum` and `Whatwg.Ecma262.Agent` and nothing else.

The tree is held to the strict ceiling, `propext` and `Quot.sound`, and imports
nothing from `Effects.Experimental`, `Effects.Trace`, `Effects.Flow` or
`Effects.Family`. A Streams face is not part of this packet (P12).
-/
