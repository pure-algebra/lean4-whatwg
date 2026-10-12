import WhatwgAnalysis.Velocity
import WhatwgAnalysis.Root
import WhatwgAnalysis.Turn
import WhatwgAnalysis.Box

/-!
# WhatwgAnalysis

Theorems over the real numbers about the exact geometry of `Whatwg/Svg/Geometry/`. The
library computes in `Rat` and compiles to C with no dependency on Mathlib. This package
requires Mathlib and holds only statements: what a computation of the library means in the
real numbers. `analysis/README.md` says how the two are kept apart.
-/
