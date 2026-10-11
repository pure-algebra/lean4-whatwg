# Seat SVG: the prompt

You are seat SVG in the lean4-whatwg repository on this PC.

- Work only in `C:\Users\kokok\Dev\lean4-whatwg-svg`, on branch `html/svg`. The branch already
  exists, and the dependency packages are already in `.lake/packages`.
- Read `AGENTS.md` and `COORDINATION.md` in full. Then read the brief,
  `docs/research/2026-10-11-svg-seat-brief.md`, which is your assignment.
- Do these slices, and stop after each one with the handoff that `AGENTS.md` names:
  - S0: merge `origin/html-h7` into `html/svg`;
  - S1: write `docs/SVG-PACKAGE-PLAN.md` and add the sealed svgwg pin;
  - S2: write the schema projection gate and its generated data;
  - S3: build the seam in `Whatwg/Html`;
  - S4: build the attribute value grammars.
- Commit by explicit paths. Add this prompt and the brief to your first commit.
- Never push: the owner pushes.
- Run one `lake` at a time. The shell is PowerShell.
- No slice waits for a breaker's packet (owner, 2026-10-11; ruling R-S1 of `COORDINATION.md`).
  Write the design of S3 and S4 into the plan at S1. Work to the standard of lean4-effect4's
  `AGENTS.md`.
