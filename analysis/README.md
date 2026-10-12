# whatwg_analysis

Theorems over the real numbers about the exact geometry of `Whatwg/Svg/Geometry/`.

## Why this is a package of its own

The library computes: its definitions are in core Lean, run, and compile to C. It requires
Batteries and Aesop and nothing else, and it must stay that way.

Some things the library computes have a meaning that it cannot state, because the statement
is about real numbers: that a velocity is a derivative, that a rounded root encloses a square
root, that a rational rotation turns by an angle. Mathlib has the real numbers. This package
requires Mathlib and states those meanings, as theorems about the library's own definitions.

The two are kept apart by three rules.

1. **The library never names this package or Mathlib.** No file under `Whatwg/`, `WhatwgTest/`,
   `WhatwgGates/` or `whatwgbin/` imports anything from here, and the library's `lakefile.toml`
   does not mention it. An executable of the library links no Mathlib code.
2. **This package holds statements and no programs.** A definition here is `noncomputable`
   or is only a name for a formula of a theorem. Nothing here is called by the library.
3. **The seam is a cast.** The library's geometry is in `Rat`. A theorem here casts those
   numbers to `ℝ` and says what holds there. The definition that computes and the theorem
   about it are the same constant.

## How it is built

This directory is a Lake package with its own `lakefile.toml`, manifest and `.lake`
directory. It compiles the library modules that its theorems import from the library's own
sources (`srcDir = ".."`), into its own build tree: twenty modules today, the geometry and what it
stands on. So it always reads the sources as they are in the checkout, and it writes nothing
into the library's `.lake`.

```bash
lake -d analysis update      # once: fetches Mathlib at v4.33.1 and its prebuilt files
lake -d analysis build
```

The first command downloads several gigabytes into `analysis/.lake`, which git ignores.
Mathlib at `v4.33.1` pins Batteries and Aesop at the revisions the library pins, and uses the
same toolchain.

A package outside this repository that wants both would require the library and this package
by name. For that, this package would require the library in its lakefile and drop the
`WhatwgCore` library that reads its sources; nothing else changes.

## What is here

| Module | The library computes | This package proves |
| --- | --- | --- |
| `WhatwgAnalysis.Velocity` | `Cubic.pointAt`, `Cubic.velocity` | the velocity is the derivative of the point (`hasDerivAt_pointAt_x`, `hasDerivAt_pointAt_y`) |
| `WhatwgAnalysis.Root` | `sqrtDown`, `Vec.norm` | the computed root is within one unit of its last place below the real square root (`sqrtDown_le_sqrt`, `sqrt_lt_sqrtDown_succ`) |
| `WhatwgAnalysis.Turn` | `Affine.turn u` | it is the rotation by `2 * arctan u` (`apply_turn`) |
| `WhatwgAnalysis.Box` | `Cubic.box`, and the rounding of `Pen.cubic` | the box holds the segment at every real parameter from `0` to `1` (`box_holds_x`, `box_holds_y`); four control values moved by `δ` at most move the curve by `δ` at most (`bezier_near`) |

## What it is not

This package is outside the trust gates of the repository. Its theorems are checked by Lean's
kernel and depend on Mathlib's usual axioms (`propext`, `Classical.choice`, `Quot.sound`). No
gate of the repository builds it, and no claim of the library depends on it.
