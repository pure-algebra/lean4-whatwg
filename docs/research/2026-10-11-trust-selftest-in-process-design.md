# The trust self-test judged in process

Status: design record of the self-test redesign seat, 2026-10-11, for debt D79
of ruling R-S5. The work was done on the branch `review/selftest-in-process`,
from `html/svg` at `ab1ed31`, in a worktree of its own, because seat SVG was
building in the `html/svg` worktree at the same time. Toolchain
`leanprover/lean4:v4.33.1`, Windows 11. Every time below was measured on that
tree by this seat; section 8 holds the receipt of the two runs. The frozen text
is addendum V2g of `test/contracts/trust-gate-hardening.contract.md`, and the
landing is ruling R-T1 of `COORDINATION.md`.

## 1. Decision

`lake exe whatwg_trustselftest` judges every row in one process and builds the
tree for none. It takes the built tree as it stands, imports it once with no
extension loaded, as the executable gate does, and hands the gate library's own
run a planted view for each row: the row's fixture text in place of a source,
its list entry in place of a configuration value, and, for a row whose finding
only a compiled declaration can cause, the plant compiled once by `lean` and
added to the imported tree. The one-plant-per-build run is unchanged and is
`lake exe whatwg_trustselftest --each`.

## 2. Where the eighteen minutes go

The one-plant run makes 92 rows and six controls. For each row it edits a copy
of the tree, runs `lake build` there and then `lake exe whatwg_trustgate`.
A plant in `Whatwg.lean` re-elaborates the umbrella, the gate module and the
test root; a plant in the configuration module also relinks the executable.
The gate's own work is a small part of each row: the executable takes about 4 s
on this tree, of which the import is 1.0 s, the token scan of 300 sources 1.4 s,
the axiom traversal 0.75 s and every other pass together under 0.3 s. The rest
of a row's 11 s is Lake, the elaborator and the linker.

## 3. Why not the batched commit

Commit `07fdb0e` of `review/w10-selftest-paring` keeps the two real judges and
cuts the builds from 93 to 22 by planting several rows in one tree. It reports
about three minutes, which is over the bound of R-S5. It also pays for sharing a
tree: 26 rows plant the same module, so it renames each plant by row and maps
the frozen fragments to the new names, and it needs a second mode,
`--attribution`, to show that no plant of a group prints another row's
fragment.

The in-process run needs neither. Each row has its own view, so each plant keeps
its frozen module name and every fragment is required as the contract spells it.
This design is therefore written beside that commit. It takes four things from
it: the flag name `--each`, the row filter `--rows`, the flush after each row,
and the copy that creates each directory once.

## 4. The four classes

A row's class says what its finding depends on.

| Class | Rows | What the row needs | In process |
| --- | --- | --- | --- |
| Text | 43 | the text of one source, the root or `lakefile.toml`, and the token table | the gate's run over the planted text |
| Configuration data | 6 | a list entry of the configuration | the gate's run over the planted configuration value |
| Compiled environment | 31 | a declaration, registration, token or extension entry in a built module | `lean` compiles the plant once; the gate's run over the tree with the plant imported |
| Real build | 12 | Lean's own refusal, a Lake trace, a build directory edited after the build, or the command itself | one `lean` run, one build of a one-module package, the freshness step over a planted build directory, or the narrow run |

Six of the 31 compiled rows are list checks whose entry names a planted
declaration or module, so they need both a planted configuration value and a
compiled plant.

Section 8 gives the measured time of each class in both runs.

## 5. How each class is judged

### The planted view

The harness applies a row's edits to texts in memory, with the functions the
one-plant run uses on its copy (`insertAfterAnchor`, `insertBeforeLine`), so an
anchor that is missing or repeated fails the row as before. Nothing is written
into the checkout. The view is the audited sources with the planted texts in
place, the planted configuration, and an environment.

The gate library's run was `Gates.Trust.runPasses`, which reads the sources
from disk. It is split: `runPassesOver` takes the project root, the source list
and a scan function, and `runPasses` calls it with the files on disk. Every pass
and their order are in `runPassesOver`, which both judges of the tree and the
self-test now call. The split changes no finding. It is the one change to the
gate library.

The host's reads are the executable's: the token table rebuilt from raw parser
entries, the raw scoped tokens, no root constants, and its own axiom traversal.
After the run of the passes the harness calls the executable's other steps that
a plant can reach: step 0 on the planted `lakefile.toml`, and step 5, the
extension allowlist.

### Text rows

The planted source is scanned with the token table of the built tree, and the
row's fragment must be among the findings. Unplanted sources are scanned once
for the whole run.

### Configuration rows

A list fixture is one or more lines of the form `⟨name, "reason"⟩ ::`. The
harness reads the entries with Lean's tokenizer and puts them at the head of the
list that the row's anchor names. It still inserts the fixture after the anchor
in the text of `WhatwgGates/TrustConfig.lean`, so the anchor is checked and the
planted source is scanned.

### Compiled rows

`lean` compiles each planted module directly, with the search path of the
loader and the options the trace of module `Whatwg` records. A compile takes
0.6 s for a plant that imports nothing and 1.9 s for one that imports the tree.
Rows that plant the same text at the same module share one compile. The run
makes 33 compiles, four at a time, in about 15 s beside the judging of the text
rows.

The environment is built without importing the tree again.
`Lean.importModulesCore` keeps its state, so the harness imports the tree once,
keeps that state, and for each row resumes from it with the plant's built file
given by path. Loading one plant takes about 5 ms and `finalizeImport` about
150 ms. A second full import in the same process would not do: the first one
holds every built file mapped at its base address, so the second would copy
about a gigabyte.

A plant appended to an existing module replaces that module. The state resumed
is then an earlier one, taken before that module and its importers were loaded.
Two modules are replaced by some row, `Whatwg` and
`WhatwgTest.Audit.AxiomGate`, and three modules import one of them.

A row whose plant adds a token changes the final token table, so every source is
scanned again for that row, as the gate would scan it. Four rows do.

### Real-build rows

- The plant Lean refuses (5 rows: `sorry` in the production tree and the four
  malformed literals). `lean` must refuse the planted module, with the row's
  fragment where it has one. The executable's expectation for these rows is that
  it stops at freshness, so the freshness step runs over the planted source
  beside the built file and must report the module stale.
- A build option (V2e-O1 to V2e-O3). The harness writes a package that holds
  the package table's compile options and the `Whatwg` library table of the
  real `lakefile.toml`, with the fixture after the frozen anchor, and one empty
  module `Whatwg`. Lake builds it in about 2 s, and step 2 of the executable
  reads the trace Lake wrote. A control builds the same package with no plant
  and requires no finding.
- A tree edited after the build (V2e-F1 and V2e-F2). The freshness step runs
  over a directory that holds the module's source, trace and built file as the
  row leaves them.
- The two narrow runs are run as they are, in the checkout: 6 s and 3 s.

One task runs every `lake` process in turn, beside the judging: the executable
gate over the unmodified tree, the four packages and the two narrow runs, 18 s
together.

### The in-tree command

The in-process judge is the library with the executable's reads. The in-tree
command adds two reads of its own: the constants the root has declared, and the
check that its own elaborator ran the gate command. Two rows name a fragment
that comes from one of them, V2c-R1 and V2c-M03. For those two the harness also
elaborates the planted root with `lean`. The command finds its project root from
the file it runs in, so the audited sources, five megabytes, are copied to a
directory with the planted texts in place; the built tree stays on the search
path, and a compiled plant's built file is named in a module setup file, as
Lake names a module's imports. One such run takes 8 s, and the two run beside
the judging of the compiled rows.

### Controls

The unmodified tree must be built and fresh, and `known-red.txt` must be empty.
The run of the passes over the unplanted view must have no finding.
`lake exe whatwg_trustgate` must accept the tree and print the summary the
in-process run computed, and the narrow run of the in-tree command must print
it too. Those two equalities tie the in-process judge to the two real ones.

## 6. Every row and its class

Text (43): `partial declaration`, `unsafe declaration`, V2-T01 to V2-T17,
V2b-T01 to V2b-T13, V2c-M01 to V2c-M03, V2c-C1 to V2c-C3, V2c-R1, V2c-R2,
`unreachable test module`, V2e-F3, V2e-K1.

Configuration data (6): V2-S3, V2-X2, V2c-L1, V2e-X1, V2e-X2, V2e-X3.

Compiled environment (31):

- the eight acceptance rows: `comments, strings, and numeric projections`,
  V2-A1, V2-A2, V2-S2, V2b-A1, V2c-A1, V2c-A2, V2d-A1;
- the environment pass: `native_decide in the production tree`, V2-E1 to V2-E7;
- the strict ceiling: V2-S1;
- registrations: V2c-E01, V2d-E1, V2e-G1;
- token-table hygiene: V2c-B1, V2c-T1, V2c-T2, V2c-T3;
- the extension allowlist: V2e-U1;
- list checks over a compiled plant: V2-S4, V2-S5, V2-S6, V2-X1, V2c-L2,
  V2c-L3.

Real build (12): `sorry in the production tree`, `malformed string literal`,
`malformed raw string literal`, `malformed decimal literal`,
`unterminated comment`, V2e-O1, V2e-O2, V2e-O3, V2e-F1, V2e-F2, V2-N1, V2-N2.

The class is data in the row tables: the field `judgement` of a row says how the
in-process run judges it, and the run prints the class on each line.

## 7. What could not be made fast, and what the in-process run does not show

Every one of the 92 rows is judged in the default run; none was left to
`--each`. Twelve rows still start a process each, because what they test is the
process: Lean's parser, Lake's trace, or the command run by its file name. They
cost 28 s of process time and no wall time, since they run beside the judging.

What the default run gives up is the second judge on most rows. `--each` shows
each of the following, and stays the reference.

- The in-tree command's verdict on a planted tree, beyond the two twins. The
  wrapper `WhatwgTest/Audit/AxiomGate.lean` reads the loaded token table and
  calls `Lean.collectAxioms`; both are exercised on the unmodified tree only.
  Judging every row by it as well would cost 8 s of `lean` for each row, about
  twelve minutes of process time.
- That Lean accepts a text row's plant. A text row is judged on its text. That
  the fixture elaborates, and so is a real hole, changes only with the fixture
  or the toolchain. Compiling all 43 would add about a minute of process time,
  and some fixtures run a library search.
- The plant's own tokens for a text row. Seven text rows declare a `macro`, an
  `elab` or a `notation`, and the built tree's token table does not hold their
  tokens. In six fixtures the token is spelled only inside a string literal; in
  V2b-T10 it is also the tactic the example runs, and it carries no refused
  word either way.
- That the configuration module compiles with a list fixture. The entry is read
  from the fixture's text.
- The executable's whole run on a planted tree. Its steps are called one by one
  on planted data. The whole run is exercised on the unmodified tree.
- For a text row that plants a new module, the built environment does not hold
  the module, so the closure pass also reports its source as unreachable. Only
  the two closure rows expect that fragment.

So a change to the gate library, to the configuration, to a pass's wording or to
a row is checked by the default run. A change to the in-tree wrapper, to a
fixture or to the toolchain pin still owes `--each` once.

## 8. Receipt

Both runs were made on one tree: `html/svg` at `ab1ed31` with this change, in
the seat's worktree, Windows 11, `leanprover/lean4:v4.33.1`,
`LEAN_NUM_THREADS=4`, on 2026-10-11.

| Run | Exit | `PASS` lines | `FAIL` lines | Wall time |
| --- | --- | --- | --- | --- |
| `lake exe whatwg_trustselftest` | 0 | 101 | 0 | 36.1 s |
| `lake exe whatwg_trustselftest --each` | 0 | 178 | 0 | 1,175.6 s |

The 101 lines are six controls, 92 rows, two in-tree twins and the verdict. The
178 are seven control lines, two lines for each of the 78 rows that both gates
judge, one for each of the other 14, and the verdict.

The same rows pass. A script read both logs: each of the 92 rows of the default
run has, in the one-plant log, the `PASS` line of each judge that run makes for
it, and the one-plant log passes no row the default run does not list. For each
of the 65 rejection rows that the gate judges in process, the in-tree command of
the one-plant run met the same fragment.

Time by class. The one-plant column is read from a time stamp on each line of
its log. The default column is the judging in the process; the processes it
starts run beside the judging and are listed apart.

| Class | Rows | `--each` | Default run, judging |
| --- | --- | --- | --- |
| Text | 43 | 566 s | 9.5 s |
| Configuration data | 6 | 84 s | 1.3 s |
| Compiled environment | 31 | 421 s | 19.8 s |
| Real build | 12 | 50 s | under 0.1 s |
| Controls, and the copy of the tree | | 55 s | 4.0 s to import, scan and traverse once |
| Whole run | 92 | 1,176 s | 36 s |

Beside the judging the default run started 33 compiles by `lean`, 51 s of
process time four at a time; two elaborations of a planted root, 16 s; and one
task of `lake` processes, 18 s: the executable gate, four one-module packages
and the two narrow runs.

Negative controls, each one default run. With eight fixtures made harmless
(the refused word removed, a modifier added to an acceptance fixture, the axiom
made a theorem, another list entry, an empty build option, an empty root plant,
no unification hint, an allowlist entry listed once) the run failed exactly the
ten rows that plant them and one twin, and passed the rest. With six one-line
mutants, four in the gate library (one refused word dropped, `@[extern]` not
read, a stale strict exception admitted, every extension admitted) and two in
the in-tree wrapper (no root constants handed in, the post-command check never
firing), the run failed exactly V2b-T03, V2-E3, V2-S4, V2e-U1 and the two
twins; only the twins saw the two wrapper mutants.

At the landing. The branch was rebased onto `html/svg` at `8ad963d`, three
slices of seat SVG later, where the tree imports Aesop and Batteries: 2,837
modules where the receipt tree had 2,662. There the default run exits 0 with
101 `PASS` lines in 40.8 s (40.2 s and 39.9 s one slice earlier). The
one-plant run was not repeated: it tests the gate's code, which the three
slices did not change.

On the first of those trees, `a5b9e50`, the default run failed one control: the
in-tree command counted 109 declarations of `WhatwgTest` that reach
`Classical.choice`, and the executable and the in-process run 110. The one
declaration is `WhatwgTest.Audit.BankCensus.elabBankCensus.match_1`, the
matcher of a tuple pattern over Aesop's rule sets, in a module that slice had
just added. `Lean.collectAxioms` and the executable's traversal walk the same
constants in different orders, and around a dependency cycle outside the audited
trees they can record different axioms for one constant. The one-plant run
makes the same comparison on every accepted tree, so it would have failed
there too. The landing removes that matcher, three lines with the same
behaviour, and both gates then count 109 of 5,267; the disagreement itself is
debt D87 of ruling R-T1.