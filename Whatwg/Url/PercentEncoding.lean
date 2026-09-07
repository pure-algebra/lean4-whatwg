import Whatwg.Infra
import Whatwg.Url.Boundary

/-!
# URL percent encoding

Owner: the `percent-encoded-bytes` section of the pinned URL source together
with the eight percent-encode set definitions, the contiguous byte range
[16209,25393) of `vendor/whatwg-url-55d66993/url.bs`, SHA-256
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`. Twenty
census rows of `generated/url-census.tsv`: 15 `op`, 3 `rule`, 1 `type`, and
1 `requirement`. Every declaration below names its row and that row's
`[byte-start,byte-end)` span; no line number is cited anywhere.

Contract: `test/contracts/url-percent-encoding.contract.md`.
Graph: `docs/URL-PERCENT-ENCODING-DAG.md` (`URL-PG-PERCENT`).
Attacks: `test/counterexamples/url/PERCENT-ENCODING.md`, `URL-PE-CE-001`
through `URL-PE-CE-014`.

Carriers are Infra's and none is redeclared here: `Whatwg.Infra.Byte`,
`ByteSequence`, `CodePoint`, `CodeUnit`, `JsString`, `ScalarValue`, and
`JsString.asciiEncode?`. The Encoding Standard's answers are
`Whatwg.Url.Boundary`'s first-order tapes; no encoder or decoder body is
modelled here, and no URL-local UTF-8 codec is invented.

Observation mask: none. This family is equational — every operation is a total
function on Stratum V data — and the one decision it meets, the Encoding
boundary's answer, is an argument rather than an observation.
-/

set_option autoImplicit false

namespace Whatwg.Url.PercentEncoding

open Whatwg.Infra

/-! ## The percent-encode set carrier

Row `type.percent-encode-set` [18975,19062): "A percent-encode set is a set of
code points." -/

/-- A percent-encode set, row `type.percent-encode-set` [18975,19062): "a set of
code points". The carrier is a decidable predicate on the canonical
`Whatwg.Infra.CodePoint` (INFRA-R2's bounded natural, not `Char`): the C0
control set's "all code points greater than U+007E" includes the surrogates,
which `Char` cannot hold. No second code-point carrier is introduced. -/
abbrev PercentEncodeSet := Whatwg.Infra.CodePoint → Bool

/-- Membership in a percent-encode set: the predicate's application. -/
def mem (set : PercentEncodeSet) (codePoint : Whatwg.Infra.CodePoint) : Bool := set codePoint

/-- The one construction the eight named sets are built with. Each of the
text's "consisting of the X percent-encode set and …" sentences becomes one
application of `extend` over the parent set the census records as its
dependency, so the inclusion chain is a theorem about `extend` and not a fact
about how the members happen to have been written out. -/
def extend (base : PercentEncodeSet) (extra : List Nat) : PercentEncodeSet :=
  fun codePoint => base codePoint || extra.any fun value => decide (codePoint.val = value)

/-! ## The eight named sets, in the text's own dependency order -/

/-- Row `op.c0-control-percent-encode-set` [19062,19252): "The C0 control
percent-encode set is a percent-encode set consisting of C0 controls and all
code points greater than U+007E (~)." -/
def c0Control : PercentEncodeSet :=
  fun codePoint => codePoint.isC0Control || decide (0x7E < codePoint.val)

/-- Row `op.fragment-percent-encode-set` [19252,19458): "consisting of the
C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+003C (<),
U+003E (>), and U+0060 (`)". -/
def fragment : PercentEncodeSet := extend c0Control [0x20, 0x22, 0x3C, 0x3E, 0x60]

/-- Row `op.query-percent-encode-set` [19458,19661): "consisting of the
C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+0023 (#),
U+003C (<), and U+003E (>)". -/
def query : PercentEncodeSet := extend c0Control [0x20, 0x22, 0x23, 0x3C, 0x3E]

/-- Row `op.special-query-percent-encode-set` [19816,19965): "consisting of the
query percent-encode set and U+0027 (')". -/
def specialQuery : PercentEncodeSet := extend query [0x27]

/-- Row `op.path-percent-encode-set` [19965,20183): "consisting of the query
percent-encode set and U+003F (?), U+005E (^), U+0060 (`), U+007B ({), and
U+007D (})". -/
def path : PercentEncodeSet := extend query [0x3F, 0x5E, 0x60, 0x7B, 0x7D]

/-- Row `op.userinfo-percent-encode-set` [20183,20454): "consisting of the path
percent-encode set and U+002F (/), U+003A (:), U+003B (;), U+003D (=),
U+0040 (@), U+005B ([) to U+005D (]), inclusive, and U+007C (|)". The
`U+005B ([) to U+005D (])` clause is an inclusive range, so U+005C (\) is a
member; reading it as its two endpoints is `URL-PE-CE-002`. -/
def userinfo : PercentEncodeSet :=
  extend path [0x2F, 0x3A, 0x3B, 0x3D, 0x40, 0x5B, 0x5C, 0x5D, 0x7C]

/-- Row `op.component-percent-encode-set` [20454,20666): "consisting of the
userinfo percent-encode set and U+0024 ($) to U+0026 (&), inclusive,
U+002B (+), and U+002C (,)". The first clause is an inclusive range. -/
def component : PercentEncodeSet := extend userinfo [0x24, 0x25, 0x26, 0x2B, 0x2C]

/-- Row `op.form-percent-encode-set` [21163,21416): the
`application/x-www-form-urlencoded` percent-encode set, "consisting of the
component percent-encode set and U+0021 (!), U+0027 (') to U+0029 RIGHT
PARENTHESIS, inclusive, and U+007E (~)". The second clause is an inclusive
range. -/
def form : PercentEncodeSet := extend component [0x21, 0x27, 0x28, 0x29, 0x7E]

/-! ## The finite index the algorithm's own identity tests compare on

Steps 1 and 2 of `op.percent-encode-after-encoding` [21624,24696) compare the
`percentEncodeSet` argument with named sets. A bare predicate has no decidable
equality, so the algorithm takes the name and `setOf` resolves it. -/

/-- The name of one of the eight percent-encode sets the pinned source defines.
Steps 1 and 2 of `op.percent-encode-after-encoding` [21624,24696) branch on set
identity, which is what this index carries. -/
inductive SetName where
  /-- Row `op.c0-control-percent-encode-set` [19062,19252). -/
  | c0Control
  /-- Row `op.fragment-percent-encode-set` [19252,19458). -/
  | fragment
  /-- Row `op.query-percent-encode-set` [19458,19661). -/
  | query
  /-- Row `op.special-query-percent-encode-set` [19816,19965). -/
  | specialQuery
  /-- Row `op.path-percent-encode-set` [19965,20183). -/
  | path
  /-- Row `op.userinfo-percent-encode-set` [20183,20454). -/
  | userinfo
  /-- Row `op.component-percent-encode-set` [20454,20666). -/
  | component
  /-- Row `op.form-percent-encode-set` [21163,21416). -/
  | form
  deriving DecidableEq, Repr

/-- The set a name resolves to. Pinned by `setOf_eq` and separated by
`setOf_injective`. -/
def setOf : SetName → PercentEncodeSet
  | SetName.c0Control => c0Control
  | SetName.fragment => fragment
  | SetName.query => query
  | SetName.specialQuery => specialQuery
  | SetName.path => path
  | SetName.userinfo => userinfo
  | SetName.component => component
  | SetName.form => form

/-! ## Membership, exactly as the text lists it

The three sets whose text lists an inclusive range — userinfo's
`U+005B ([) to U+005D (])`, component's `U+0024 ($) to U+0026 (&)`, and form's
`U+0027 (') to U+0029 RIGHT PARENTHESIS` — are `extend`ed with the three code
points of the range, and `three_or_iff_range` is the one place where the three
members and the range meet. It is proved constructively: `omega` is used only on
goals it settles without classical case analysis. -/

/-- Three consecutive members are the inclusive range they span. Constructive:
each `omega` call below has either a plain arithmetic goal or a purely
disjunctive goal over equalities, neither of which needs `Classical.choice`. -/
private theorem three_or_iff_range (value low middle high : Nat) (rest : Prop)
    (hmiddle : middle = low + 1) (hhigh : high = low + 2) :
    (value = low ∨ value = middle ∨ value = high ∨ rest) ↔
      ((low ≤ value ∧ value ≤ high) ∨ rest) := by
  subst hmiddle
  subst hhigh
  constructor
  · rintro (rfl | rfl | rfl | hrest)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr hrest
  · rintro (⟨hlow, hhigh⟩ | hrest)
    · have hcases : value = low ∨ value = low + 1 ∨ value = low + 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr hrest))

/-- Row `op.c0-control-percent-encode-set` [19062,19252). -/
theorem c0Control_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem c0Control codePoint = true ↔
      (Whatwg.Infra.CodePoint.isC0Control codePoint = true ∨ 0x7E < codePoint.val) := by
  simp [mem, c0Control]

/-- Row `op.fragment-percent-encode-set` [19252,19458). -/
theorem fragment_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem fragment codePoint = true ↔
      (mem c0Control codePoint = true ∨
        codePoint.val = 0x20 ∨ codePoint.val = 0x22 ∨ codePoint.val = 0x3C ∨
        codePoint.val = 0x3E ∨ codePoint.val = 0x60) := by
  simp [mem, fragment, extend]

/-- Row `op.query-percent-encode-set` [19458,19661). -/
theorem query_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem query codePoint = true ↔
      (mem c0Control codePoint = true ∨
        codePoint.val = 0x20 ∨ codePoint.val = 0x22 ∨ codePoint.val = 0x23 ∨
        codePoint.val = 0x3C ∨ codePoint.val = 0x3E) := by
  simp [mem, query, extend]

/-- Row `op.special-query-percent-encode-set` [19816,19965). -/
theorem specialQuery_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem specialQuery codePoint = true ↔
      (mem query codePoint = true ∨ codePoint.val = 0x27) := by
  simp [mem, specialQuery, extend]

/-- Row `op.path-percent-encode-set` [19965,20183). -/
theorem path_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem path codePoint = true ↔
      (mem query codePoint = true ∨
        codePoint.val = 0x3F ∨ codePoint.val = 0x5E ∨ codePoint.val = 0x60 ∨
        codePoint.val = 0x7B ∨ codePoint.val = 0x7D) := by
  simp [mem, path, extend]

/-- Row `op.userinfo-percent-encode-set` [20183,20454). The `[`-to-`]` clause is
an inclusive range on the right-hand side, which is exactly the three members
`extend` was given. -/
theorem userinfo_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem userinfo codePoint = true ↔
      (mem path codePoint = true ∨
        codePoint.val = 0x2F ∨ codePoint.val = 0x3A ∨ codePoint.val = 0x3B ∨
        codePoint.val = 0x3D ∨ codePoint.val = 0x40 ∨
        (0x5B ≤ codePoint.val ∧ codePoint.val ≤ 0x5D) ∨ codePoint.val = 0x7C) := by
  simp only [mem, userinfo, extend, List.any_cons, List.any_nil, Bool.or_eq_true,
    Bool.false_eq_true, or_false, decide_eq_true_eq]
  exact or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl (or_congr Iff.rfl
    (or_congr Iff.rfl (or_congr Iff.rfl
      (three_or_iff_range codePoint.val 0x5B 0x5C 0x5D (codePoint.val = 0x7C) rfl rfl))))))

/-- Row `op.component-percent-encode-set` [20454,20666). The `$`-to-`&` clause
is an inclusive range on the right-hand side. -/
theorem component_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem component codePoint = true ↔
      (mem userinfo codePoint = true ∨
        (0x24 ≤ codePoint.val ∧ codePoint.val ≤ 0x26) ∨
        codePoint.val = 0x2B ∨ codePoint.val = 0x2C) := by
  simp only [mem, component, extend, List.any_cons, List.any_nil, Bool.or_eq_true,
    Bool.false_eq_true, or_false, decide_eq_true_eq]
  exact or_congr Iff.rfl
    (three_or_iff_range codePoint.val 0x24 0x25 0x26
      (codePoint.val = 0x2B ∨ codePoint.val = 0x2C) rfl rfl)

/-- Row `op.form-percent-encode-set` [21163,21416). The `'`-to-`)` clause is an
inclusive range on the right-hand side. -/
theorem form_mem_iff (codePoint : Whatwg.Infra.CodePoint) :
    mem form codePoint = true ↔
      (mem component codePoint = true ∨
        codePoint.val = 0x21 ∨ (0x27 ≤ codePoint.val ∧ codePoint.val ≤ 0x29) ∨
        codePoint.val = 0x7E) := by
  simp only [mem, form, extend, List.any_cons, List.any_nil, Bool.or_eq_true,
    Bool.false_eq_true, or_false, decide_eq_true_eq]
  exact or_congr Iff.rfl (or_congr Iff.rfl
    (three_or_iff_range codePoint.val 0x27 0x28 0x29 (codePoint.val = 0x7E) rfl rfl))

/-! ## The seven direct inclusions the "consisting of" sentences force

These are the seven dependency edges the census records between the eight set
rows. Each is a theorem about `extend`, not a restatement of a definition. -/

/-- Rows `op.c0-control-percent-encode-set` [19062,19252) and
`op.fragment-percent-encode-set` [19252,19458). -/
theorem c0Control_subset_fragment (codePoint : Whatwg.Infra.CodePoint) :
    mem c0Control codePoint = true → mem fragment codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [fragment, extend, h]

/-- Rows `op.c0-control-percent-encode-set` [19062,19252) and
`op.query-percent-encode-set` [19458,19661). -/
theorem c0Control_subset_query (codePoint : Whatwg.Infra.CodePoint) :
    mem c0Control codePoint = true → mem query codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [query, extend, h]

/-- Rows `op.query-percent-encode-set` [19458,19661) and
`op.special-query-percent-encode-set` [19816,19965). -/
theorem query_subset_specialQuery (codePoint : Whatwg.Infra.CodePoint) :
    mem query codePoint = true → mem specialQuery codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [specialQuery, extend, h]

/-- Rows `op.query-percent-encode-set` [19458,19661) and
`op.path-percent-encode-set` [19965,20183). -/
theorem query_subset_path (codePoint : Whatwg.Infra.CodePoint) :
    mem query codePoint = true → mem path codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [path, extend, h]

/-- Rows `op.path-percent-encode-set` [19965,20183) and
`op.userinfo-percent-encode-set` [20183,20454). -/
theorem path_subset_userinfo (codePoint : Whatwg.Infra.CodePoint) :
    mem path codePoint = true → mem userinfo codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [userinfo, extend, h]

/-- Rows `op.userinfo-percent-encode-set` [20183,20454) and
`op.component-percent-encode-set` [20454,20666). -/
theorem userinfo_subset_component (codePoint : Whatwg.Infra.CodePoint) :
    mem userinfo codePoint = true → mem component codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [component, extend, h]

/-- Rows `op.component-percent-encode-set` [20454,20666) and
`op.form-percent-encode-set` [21163,21416). -/
theorem component_subset_form (codePoint : Whatwg.Infra.CodePoint) :
    mem component codePoint = true → mem form codePoint = true := by
  intro h
  simp only [mem] at h ⊢
  simp [form, extend, h]

/-! ## The seven inclusions are strict

Each witness is the code point the text lists first for the child set and which
the parent does not contain. Without these the eight sets could collapse onto
one predicate and every inclusion above would still hold. -/

/-- Row `op.fragment-percent-encode-set` [19252,19458): U+0020 SPACE. -/
theorem fragment_strict_c0Control :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x20 ∧
      mem fragment codePoint = true ∧ mem c0Control codePoint = false :=
  ⟨⟨0x20, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.query-percent-encode-set` [19458,19661): U+0020 SPACE. -/
theorem query_strict_c0Control :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x20 ∧
      mem query codePoint = true ∧ mem c0Control codePoint = false :=
  ⟨⟨0x20, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.special-query-percent-encode-set` [19816,19965): U+0027 ('). -/
theorem specialQuery_strict_query :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x27 ∧
      mem specialQuery codePoint = true ∧ mem query codePoint = false :=
  ⟨⟨0x27, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.path-percent-encode-set` [19965,20183): U+003F (?). -/
theorem path_strict_query :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x3F ∧
      mem path codePoint = true ∧ mem query codePoint = false :=
  ⟨⟨0x3F, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.userinfo-percent-encode-set` [20183,20454): U+002F (/). -/
theorem userinfo_strict_path :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x2F ∧
      mem userinfo codePoint = true ∧ mem path codePoint = false :=
  ⟨⟨0x2F, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.component-percent-encode-set` [20454,20666): U+0024 ($), the low
end of the inclusive range the text lists first. -/
theorem component_strict_userinfo :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x24 ∧
      mem component codePoint = true ∧ mem userinfo codePoint = false :=
  ⟨⟨0x24, by decide⟩, rfl, by decide, by decide⟩

/-- Row `op.form-percent-encode-set` [21163,21416): U+0021 (!). -/
theorem form_strict_component :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x21 ∧
      mem form codePoint = true ∧ mem component codePoint = false :=
  ⟨⟨0x21, by decide⟩, rfl, by decide, by decide⟩

/-! ## The three cross-cutting rules of the section -/

/-- Row `rule.query-fragment-encode-set-difference` [19661,19816): "The query
percent-encode set cannot be defined in terms of the fragment percent-encode set
due to the omission of U+0060 (`)." -/
theorem fragment_not_subset_query :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x60 ∧
      mem fragment codePoint = true ∧ mem query codePoint = false :=
  ⟨⟨0x60, by decide⟩, rfl, by decide, by decide⟩

/-- Row `rule.query-fragment-encode-set-difference` [19661,19816), the other
direction: the two sets are incomparable, so neither is an extension of the
other. U+0023 (#) is in the query set and not in the fragment set. -/
theorem query_not_subset_fragment :
    ∃ codePoint : Whatwg.Infra.CodePoint, codePoint.val = 0x23 ∧
      mem query codePoint = true ∧ mem fragment codePoint = false :=
  ⟨⟨0x23, by decide⟩, rfl, by decide, by decide⟩

/-! ### The two complement rules

Both rules relate a set to a finite list of exceptions, all of which lie below
U+007F, so each splits into a bounded region decided by kernel reduction over
the 127 code point values below U+007F and an unbounded region where the C0
control set's "all code points greater than U+007E" settles both sides. The
split keeps both receipts constructive; `omega` is called only on plain
arithmetic goals. -/

/-- The code point of a value, reduced into range. Used only to state the two
bounded facts below over `Nat` so that `Nat.decidableBallLT` can decide them. -/
private def ofVal (value : Nat) : Whatwg.Infra.CodePoint :=
  ⟨value % 0x110000, Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))⟩

private theorem ofVal_val (codePoint : Whatwg.Infra.CodePoint) :
    ofVal codePoint.val = codePoint :=
  Whatwg.Infra.CodePoint.ext (Nat.mod_eq_of_lt (Nat.lt_succ_of_le codePoint.isLe))

/-- Above U+007E every named set contains the code point, through the C0 control
percent-encode set's second clause. -/
private theorem mem_of_gt_tilde (codePoint : Whatwg.Infra.CodePoint)
    (h : 0x7E < codePoint.val) :
    mem component codePoint = true ∧ mem form codePoint = true := by
  constructor <;>
    simp [mem, form, component, userinfo, path, query, c0Control, extend, h]

/-- No ASCII alphanumeric code point is above U+007E. -/
private theorem not_alphanumeric_of_gt_tilde (codePoint : Whatwg.Infra.CodePoint)
    (h : 0x7E < codePoint.val) :
    Whatwg.Infra.CodePoint.isAsciiAlphanumeric codePoint = true → False := by
  intro halnum
  simp only [Whatwg.Infra.CodePoint.isAsciiAlphanumeric, Whatwg.Infra.CodePoint.isAsciiDigit,
    Whatwg.Infra.CodePoint.isAsciiAlpha, Whatwg.Infra.CodePoint.isAsciiUpperAlpha,
    Whatwg.Infra.CodePoint.isAsciiLowerAlpha, Whatwg.Infra.CodePoint.inRange,
    Bool.or_eq_true] at halnum
  rcases halnum with h1 | h1 | h1 <;> (have hr := of_decide_eq_true h1; omega)

private theorem form_complement_low :
    ∀ value : Nat, value < 0x7F →
      (mem form (ofVal value) = true ↔
        ¬(Whatwg.Infra.CodePoint.isAsciiAlphanumeric (ofVal value) = true ∨
          (ofVal value).val = 0x2A ∨ (ofVal value).val = 0x2D ∨
          (ofVal value).val = 0x2E ∨ (ofVal value).val = 0x5F)) := by
  decide

private theorem component_complement_low :
    ∀ value : Nat, value < 0x7F →
      (mem component (ofVal value) = false ↔
        (Whatwg.Infra.CodePoint.isAsciiAlphanumeric (ofVal value) = true ∨
          (ofVal value).val = 0x2D ∨ (ofVal value).val = 0x5F ∨ (ofVal value).val = 0x2E ∨
          (ofVal value).val = 0x21 ∨ (ofVal value).val = 0x7E ∨ (ofVal value).val = 0x2A ∨
          (ofVal value).val = 0x27 ∨ (ofVal value).val = 0x28 ∨
          (ofVal value).val = 0x29)) := by
  decide

/-- Row `rule.form-encode-set-complement` [21416,21624): the
`application/x-www-form-urlencoded` percent-encode set "contains all code
points, except the ASCII alphanumeric, U+002A (*), U+002D (-), U+002E (.), and
U+005F (_)". -/
theorem form_complement (codePoint : Whatwg.Infra.CodePoint) :
    mem form codePoint = true ↔
      ¬(Whatwg.Infra.CodePoint.isAsciiAlphanumeric codePoint = true ∨
        codePoint.val = 0x2A ∨ codePoint.val = 0x2D ∨ codePoint.val = 0x2E ∨
        codePoint.val = 0x5F) := by
  rcases Nat.lt_or_ge codePoint.val 0x7F with hlow | hhigh
  · have hbounded := form_complement_low codePoint.val hlow
    rwa [ofVal_val] at hbounded
  · have htilde : 0x7E < codePoint.val := by omega
    constructor
    · intro _
      rintro (halnum | hval | hval | hval | hval)
      · exact not_alphanumeric_of_gt_tilde codePoint htilde halnum
      all_goals omega
    · intro _
      exact (mem_of_gt_tilde codePoint htilde).2

/-- Row `rule.component-encodeuricomponent-equivalence` [20666,21163), the
URL-owned half: the code points the component percent-encode set leaves
unencoded are exactly ECMA-262's `uriUnescaped`, the ASCII alphanumeric together
with the nine `uriMark` code points `-_.!~*'()`. The other half, that
`encodeURIComponent()` escapes exactly the complement of that set, is an
ECMA-262 obligation on the `bridges` edge of `URL-PG-PERCENT`; no theorem here
discharges it. -/
theorem component_complement (codePoint : Whatwg.Infra.CodePoint) :
    mem component codePoint = false ↔
      (Whatwg.Infra.CodePoint.isAsciiAlphanumeric codePoint = true ∨
        codePoint.val = 0x2D ∨ codePoint.val = 0x5F ∨ codePoint.val = 0x2E ∨
        codePoint.val = 0x21 ∨ codePoint.val = 0x7E ∨ codePoint.val = 0x2A ∨
        codePoint.val = 0x27 ∨ codePoint.val = 0x28 ∨ codePoint.val = 0x29) := by
  rcases Nat.lt_or_ge codePoint.val 0x7F with hlow | hhigh
  · have hbounded := component_complement_low codePoint.val hlow
    rwa [ofVal_val] at hbounded
  · have htilde : 0x7E < codePoint.val := by omega
    constructor
    · intro hfalse
      rw [(mem_of_gt_tilde codePoint htilde).1] at hfalse
      exact absurd hfalse (by simp)
    · intro hrhs
      exfalso
      rcases hrhs with halnum | hval | hval | hval | hval | hval | hval | hval | hval | hval
      · exact not_alphanumeric_of_gt_tilde codePoint htilde halnum
      all_goals omega

/-! ## The finite index resolves to the eight named sets and separates them -/

/-- `setOf` is pinned to the eight named sets. Without this, the identity tests
of steps 1 and 2 of `op.percent-encode-after-encoding` [21624,24696) could
resolve any name to any set. -/
theorem setOf_eq :
    setOf SetName.c0Control = c0Control ∧
    setOf SetName.fragment = fragment ∧
    setOf SetName.query = query ∧
    setOf SetName.specialQuery = specialQuery ∧
    setOf SetName.path = path ∧
    setOf SetName.userinfo = userinfo ∧
    setOf SetName.component = component ∧
    setOf SetName.form = form :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Eight code points that separate the eight named sets pairwise: U+0020,
U+0023, U+0027, U+003F, U+002F, U+0024, U+0021 and U+0060. Seven of them are the
strictness witnesses above and the eighth is the omission
`rule.query-fragment-encode-set-difference` [19661,19816) names. -/
private def separators : List Whatwg.Infra.CodePoint :=
  [⟨0x20, by decide⟩, ⟨0x23, by decide⟩, ⟨0x27, by decide⟩, ⟨0x3F, by decide⟩,
    ⟨0x2F, by decide⟩, ⟨0x24, by decide⟩, ⟨0x21, by decide⟩, ⟨0x60, by decide⟩]

/-- The membership pattern of a set on `separators`. -/
private def signature (set : PercentEncodeSet) : List Bool := separators.map set

/-- The eight named sets are pairwise distinct: the eight `separators` give them
eight distinct signatures. Derivable from the seven strictness witnesses and the
two incomparability witnesses above; stated separately because steps 1 and 2 of
`op.percent-encode-after-encoding` [21624,24696) branch on set identity. -/
theorem setOf_injective (m n : SetName) : setOf m = setOf n → m = n := by
  intro h
  have hs : signature (setOf m) = signature (setOf n) := congrArg signature h
  cases m <;> cases n <;> first | rfl | exact absurd hs (by decide)

/-- Step 7.3.3 of `op.percent-encode-after-encoding` [21624,24696): "Assert:
percentEncodeSet includes all non-ASCII code points." Every named set contains
the C0 control percent-encode set, which contains every code point greater than
U+007E, so the assertion is discharged rather than assumed. `URL-PE-CE-014`
attacks the mutant that drops the clause. -/
theorem setOf_includes_non_ascii (n : SetName) (codePoint : Whatwg.Infra.CodePoint) :
    Whatwg.Infra.CodePoint.isAscii codePoint = false → mem (setOf n) codePoint = true := by
  intro h
  simp only [Whatwg.Infra.CodePoint.isAscii, Whatwg.Infra.CodePoint.inRange] at h
  have hnot : ¬ (0 ≤ codePoint.val ∧ codePoint.val ≤ 0x7F) := of_decide_eq_false h
  have hval : 0x7E < codePoint.val := by
    rcases Nat.lt_or_ge 0x7E codePoint.val with hlt | hge
    · exact hlt
    · exact absurd ⟨Nat.zero_le _, Nat.le_trans hge (by decide)⟩ hnot
  cases n <;>
    simp [mem, setOf, form, component, userinfo, path, query, specialQuery, fragment,
      c0Control, extend, hval]

/-! ## Hex and decimal helpers

`isHexByte` and `hexValue` are step 2's byte ranges and step 3.1's "decoded, and
then interpreted as a hexadecimal number" of `op.percent-decode-bytes`
[17113,18462). `upperHexDigit` is the "two ASCII upper hex digits" of
`op.percent-encode-byte` [16862,17111). `decimalDigits` is the "shortest
sequence of ASCII digits representing potentialError in base ten" of step 7.4 of
`op.percent-encode-after-encoding` [21624,24696). -/

/-- Step 2.2 of `op.percent-decode-bytes` [17113,18462): whether a byte is "in
the ranges 0x30 (0) to 0x39 (9), 0x41 (A) to 0x46 (F), and 0x61 (a) to 0x66 (f),
all inclusive". Lower case is accepted on input; `URL-PE-CE-008` attacks the
mutant that drops that range. -/
def isHexByte (byte : Whatwg.Infra.Byte) : Bool :=
  decide (0x30 ≤ byte.value ∧ byte.value ≤ 0x39) ||
    decide (0x41 ≤ byte.value ∧ byte.value ≤ 0x46) ||
    decide (0x61 ≤ byte.value ∧ byte.value ≤ 0x66)

/-- Step 3.1 of `op.percent-decode-bytes` [17113,18462): the byte "decoded, and
then interpreted as a hexadecimal number". Defined on the three ranges
`isHexByte` admits. -/
def hexValue (byte : Whatwg.Infra.Byte) : Nat :=
  if byte.value ≤ 0x39 then byte.value - 0x30
  else if byte.value ≤ 0x46 then byte.value - 0x37
  else byte.value - 0x57

/-- One "ASCII upper hex digit" of `op.percent-encode-byte` [16862,17111), for a
nibble below sixteen. Lower-case output is `URL-PE-CE-001`. -/
def upperHexDigit (nibble : Nat) : Whatwg.Infra.CodeUnit :=
  if nibble < 10 then UInt16.ofNat (0x30 + nibble) else UInt16.ofNat (0x37 + nibble)

/-- One ASCII digit of step 7.4 of `op.percent-encode-after-encoding`
[21624,24696), for a digit below ten. -/
private def decimalDigitUnit (digit : Nat) : Whatwg.Infra.CodeUnit :=
  UInt16.ofNat (0x30 + digit)

/-- The base-ten digits of `value`, most significant first, with the recursion
bounded by the fuel `value` itself: each step divides by ten, so the fuel the
data carries is never exhausted before the last digit. -/
private def decimalDigitsAux : Nat → Nat → Whatwg.Infra.JsString
  | 0, value => [decimalDigitUnit value]
  | fuel + 1, value =>
      if value < 10 then [decimalDigitUnit value]
      else decimalDigitsAux fuel (value / 10) ++ [decimalDigitUnit (value % 10)]

/-- Step 7.4 of `op.percent-encode-after-encoding` [21624,24696): "the shortest
sequence of ASCII digits representing potentialError in base ten". Shortest
means no leading zero above zero; `URL-PE-CE-009` attacks a padded mutant. -/
def decimalDigits (value : Nat) : Whatwg.Infra.JsString := decimalDigitsAux value value

/-! ### Helper facts about the two digit writers -/

/-- `UInt16.ofNat` reduces modulo 2^16; below that bound it is the identity on
values. Local to this module: nothing under `Whatwg/Infra/` changes. -/
private theorem toNat_ofNat16 (n : Nat) : (UInt16.ofNat n).toNat = n % 65536 := rfl

private theorem lt_sixteen_cases (n : Nat) (h : n < 16) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
      n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by
  omega

private theorem upperHexDigit_toNat (n : Nat) (h : n < 16) :
    (upperHexDigit n).toNat = if n < 10 then 0x30 + n else 0x37 + n := by
  unfold upperHexDigit
  split <;> simp only [toNat_ofNat16] <;> omega

private theorem upperHexDigit_injOn (m n : Nat) (hm : m < 16) (hn : n < 16)
    (h : upperHexDigit m = upperHexDigit n) : m = n := by
  have hmn : (upperHexDigit m).toNat = (upperHexDigit n).toNat := congrArg UInt16.toNat h
  rw [upperHexDigit_toNat m hm, upperHexDigit_toNat n hn] at hmn
  split at hmn <;> split at hmn <;> omega

/-! ## Percent-encoded byte syntax, percent-encode, percent-decode -/

/-- Row `op.percent-encoded-byte-syntax` [16209,16325): "A percent-encoded byte
is a string consisting of U+0025 (%) followed by two ASCII hex digits." The text
says `ASCII hex digit`, not `ASCII upper hex digit`, so either case is
admitted. -/
def isPercentEncodedByte (input : Whatwg.Infra.JsString) : Bool :=
  match input with
  | [first, second, third] =>
      decide (first = 0x25) &&
        Whatwg.Infra.CodePoint.isAsciiHexDigit (Whatwg.Infra.CodePoint.ofUnit second) &&
        Whatwg.Infra.CodePoint.isAsciiHexDigit (Whatwg.Infra.CodePoint.ofUnit third)
  | _ => false

/-- Row `op.percent-encode-byte` [16862,17111): "return a string consisting of
U+0025 (%), followed by two ASCII upper hex digits representing byte". -/
def percentEncodeByte (byte : Whatwg.Infra.Byte) : Whatwg.Infra.JsString :=
  [0x25, upperHexDigit (byte.value / 16), upperHexDigit (byte.value % 16)]

/-- Row `op.percent-decode-bytes` [17113,18462), transcribed branch by branch.
Step 1 is the empty output; step 2.1 copies a byte that is not 0x25; step 2.2
copies a `%` whose next two bytes are not both in the hex ranges, without
consuming them (`URL-PE-CE-013`) and without dropping or truncating anything
when fewer than two bytes follow (`URL-PE-CE-003`, `URL-PE-CE-004`); step 2.3
reads the pair as a hexadecimal number, appends that byte and skips the two.
The recursion is on the input's own list structure, so the function is
total. -/
def percentDecodeBytes : Whatwg.Infra.ByteSequence → Whatwg.Infra.ByteSequence
  | [] => []
  | [byte] => [byte]
  | [byte, other] => [byte, other]
  | byte :: first :: second :: tail =>
      if byte ≠ 0x25 then
        byte :: percentDecodeBytes (first :: second :: tail)
      else if !(isHexByte first && isHexByte second) then
        byte :: percentDecodeBytes (first :: second :: tail)
      else
        UInt8.ofNat (hexValue first * 16 + hexValue second) :: percentDecodeBytes tail

/-- Row `op.percent-decode-string` [18464,18967): "Let bytes be the UTF-8
encoding of input. Return the percent-decoding of bytes." The UTF-8 encoding is
the Encoding Standard's answer, carried by `Whatwg.Url.Boundary.Utf8Encoding`;
no UTF-8 codec is declared here. -/
def percentDecodeString (input : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Infra.ByteSequence :=
  percentDecodeBytes input.bytes

/-- Row `requirement.percent-encoded-utf8-advice` [16325,16862): "It is
generally a good idea for sequences of percent-encoded bytes to be such that,
when percent-decoded and then passed to UTF-8 decode without BOM or fail, they
do not end up as failure." The URL-owned content is which byte sequence is
handed over; whether the call fails is the boundary's answer. -/
def followsUtf8Advice (input : Whatwg.Infra.ByteSequence)
    (answer : Whatwg.Url.Boundary.Utf8DecodeOrFail) : Prop :=
  answer.input = percentDecodeBytes input ∧ answer.failed = false

/-! ### The hex reader's laws -/

/-- Step 2.2 of `op.percent-decode-bytes` [17113,18462). -/
theorem isHexByte_iff (byte : Whatwg.Infra.Byte) :
    isHexByte byte = true ↔
      ((0x30 ≤ Whatwg.Infra.Byte.value byte ∧ Whatwg.Infra.Byte.value byte ≤ 0x39) ∨
        (0x41 ≤ Whatwg.Infra.Byte.value byte ∧ Whatwg.Infra.Byte.value byte ≤ 0x46) ∨
        (0x61 ≤ Whatwg.Infra.Byte.value byte ∧ Whatwg.Infra.Byte.value byte ≤ 0x66)) := by
  simp [isHexByte, or_assoc]

/-- Step 3.1 of `op.percent-decode-bytes` [17113,18462), on 0x30 to 0x39. -/
theorem hexValue_digit (byte : Whatwg.Infra.Byte) :
    0x30 ≤ Whatwg.Infra.Byte.value byte → Whatwg.Infra.Byte.value byte ≤ 0x39 →
      hexValue byte = Whatwg.Infra.Byte.value byte - 0x30 := by
  intro _ h2
  unfold hexValue
  rw [if_pos h2]

/-- Step 3.1 of `op.percent-decode-bytes` [17113,18462), on 0x41 to 0x46. -/
theorem hexValue_upper (byte : Whatwg.Infra.Byte) :
    0x41 ≤ Whatwg.Infra.Byte.value byte → Whatwg.Infra.Byte.value byte ≤ 0x46 →
      hexValue byte = Whatwg.Infra.Byte.value byte - 0x37 := by
  intro h1 h2
  unfold hexValue
  rw [if_neg (by omega), if_pos h2]

/-- Step 3.1 of `op.percent-decode-bytes` [17113,18462), on 0x61 to 0x66. -/
theorem hexValue_lower (byte : Whatwg.Infra.Byte) :
    0x61 ≤ Whatwg.Infra.Byte.value byte → Whatwg.Infra.Byte.value byte ≤ 0x66 →
      hexValue byte = Whatwg.Infra.Byte.value byte - 0x57 := by
  intro h1 _
  unfold hexValue
  rw [if_neg (by omega), if_neg (by omega)]

/-! ### The syntax row and the byte serializer -/

/-- Row `op.percent-encoded-byte-syntax` [16209,16325). -/
theorem isPercentEncodedByte_iff (input : Whatwg.Infra.JsString) :
    isPercentEncodedByte input = true ↔
      ∃ first second : Whatwg.Infra.CodeUnit,
        input = [0x25, first, second] ∧
        Whatwg.Infra.CodePoint.isAsciiHexDigit
          (Whatwg.Infra.CodePoint.ofUnit first) = true ∧
        Whatwg.Infra.CodePoint.isAsciiHexDigit
          (Whatwg.Infra.CodePoint.ofUnit second) = true := by
  match input with
  | [] => simp [isPercentEncodedByte]
  | [_] => simp [isPercentEncodedByte]
  | [_, _] => simp [isPercentEncodedByte]
  | [u0, u1, u2] =>
      simp only [isPercentEncodedByte, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩
        subst h0
        exact ⟨u1, u2, rfl, h1, h2⟩
      · rintro ⟨first, second, heq, hf, hs⟩
        simp only [List.cons.injEq, and_true] at heq
        obtain ⟨h0, h1, h2⟩ := heq
        subst h1
        subst h2
        exact ⟨⟨h0, hf⟩, hs⟩
  | _ :: _ :: _ :: _ :: _ => simp [isPercentEncodedByte]

/-- Row `op.percent-encode-byte` [16862,17111): the exact output shape. -/
theorem percentEncodeByte_eq (byte : Whatwg.Infra.Byte) :
    percentEncodeByte byte =
      [0x25, upperHexDigit (Whatwg.Infra.Byte.value byte / 16),
        upperHexDigit (Whatwg.Infra.Byte.value byte % 16)] := rfl

/-- Row `op.percent-encode-byte` [16862,17111): every nibble is written as an
ASCII **upper** hex digit. The lower-case mutant `URL-PE-CE-001` fails here. -/
theorem upperHexDigit_isAsciiUpperHexDigit (n : Nat) :
    n < 16 →
      Whatwg.Infra.CodePoint.isAsciiUpperHexDigit
        (Whatwg.Infra.CodePoint.ofUnit (upperHexDigit n)) = true := by
  intro h
  rcases lt_sixteen_cases n h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Row `op.percent-encode-byte` [16862,17111), stated on the serializer's own
output rather than on the helper. -/
theorem percentEncodeByte_upper (byte : Whatwg.Infra.Byte) :
    List.all (List.drop 1 (percentEncodeByte byte))
      (fun unit => Whatwg.Infra.CodePoint.isAsciiUpperHexDigit
        (Whatwg.Infra.CodePoint.ofUnit unit)) = true := by
  have hb : Whatwg.Infra.Byte.value byte < 256 := byte.toNat_lt
  have h1 : Whatwg.Infra.Byte.value byte / 16 < 16 := by omega
  have h2 : Whatwg.Infra.Byte.value byte % 16 < 16 := by omega
  simp [percentEncodeByte, upperHexDigit_isAsciiUpperHexDigit _ h1,
    upperHexDigit_isAsciiUpperHexDigit _ h2]

/-- Rows `op.percent-encode-byte` [16862,17111) and
`op.percent-encoded-byte-syntax` [16209,16325) compose: what the serializer
emits is what the syntax admits. -/
theorem percentEncodeByte_isPercentEncodedByte (byte : Whatwg.Infra.Byte) :
    isPercentEncodedByte (percentEncodeByte byte) = true := by
  have hb : Whatwg.Infra.Byte.value byte < 256 := byte.toNat_lt
  have h1 := upperHexDigit_isAsciiUpperHexDigit (Whatwg.Infra.Byte.value byte / 16) (by omega)
  have h2 := upperHexDigit_isAsciiUpperHexDigit (Whatwg.Infra.Byte.value byte % 16) (by omega)
  simp [isPercentEncodedByte, percentEncodeByte,
    Whatwg.Infra.CodePoint.isAsciiHexDigit, h1, h2]

/-- Row `op.percent-encode-byte` [16862,17111): distinct bytes never share an
escape. -/
theorem percentEncodeByte_injective (a b : Whatwg.Infra.Byte) :
    percentEncodeByte a = percentEncodeByte b → a = b := by
  intro h
  have ha : Whatwg.Infra.Byte.value a < 256 := a.toNat_lt
  have hb : Whatwg.Infra.Byte.value b < 256 := b.toNat_lt
  simp only [percentEncodeByte, List.cons.injEq, and_true] at h
  obtain ⟨-, hhigh, hlow⟩ := h
  have ehigh := upperHexDigit_injOn _ _ (by omega) (by omega) hhigh
  have elow := upperHexDigit_injOn _ _ (by omega) (by omega) hlow
  have hval : Whatwg.Infra.Byte.value a = Whatwg.Infra.Byte.value b := by omega
  calc a = UInt8.ofNat a.toNat := UInt8.ofNat_toNat.symm
    _ = UInt8.ofNat b.toNat := by rw [show a.toNat = b.toNat from hval]
    _ = b := UInt8.ofNat_toNat

/-! ## Percent-decode a byte sequence, one law per branch of the text's step 2 -/

/-- Step 1 of `op.percent-decode-bytes` [17113,18462): "Let output be an empty
byte sequence." -/
theorem percentDecodeBytes_nil : percentDecodeBytes [] = [] := rfl

/-- Step 2.1 of `op.percent-decode-bytes` [17113,18462): "If byte is not
0x25 (%), then append byte to output." -/
theorem percentDecodeBytes_other (byte : Whatwg.Infra.Byte)
    (tail : Whatwg.Infra.ByteSequence) : byte ≠ 0x25 →
      percentDecodeBytes (byte :: tail) = byte :: percentDecodeBytes tail := by
  intro hb
  match tail with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp [percentDecodeBytes, hb]

/-- Step 2.3 of `op.percent-decode-bytes` [17113,18462): the well-formed escape.
The pair is read as a hexadecimal number and the next two bytes are skipped. -/
theorem percentDecodeBytes_pair (first second : Whatwg.Infra.Byte)
    (tail : Whatwg.Infra.ByteSequence) :
    isHexByte first = true → isHexByte second = true →
      percentDecodeBytes (0x25 :: first :: second :: tail) =
        UInt8.ofNat (hexValue first * 16 + hexValue second) :: percentDecodeBytes tail := by
  intro h1 h2
  simp [percentDecodeBytes, h1, h2]

/-- Step 2.2 of `op.percent-decode-bytes` [17113,18462) with two following
bytes: only the `%` is appended, and the two following bytes are reconsidered
rather than skipped. `URL-PE-CE-013` attacks the mutant that skips them. -/
theorem percentDecodeBytes_malformed_pair (first second : Whatwg.Infra.Byte)
    (tail : Whatwg.Infra.ByteSequence) :
    (isHexByte first = false ∨ isHexByte second = false) →
      percentDecodeBytes (0x25 :: first :: second :: tail) =
        0x25 :: percentDecodeBytes (first :: second :: tail) := by
  rintro (h | h) <;> simp [percentDecodeBytes, h]

/-- Step 2.2 of `op.percent-decode-bytes` [17113,18462) with fewer than two
following bytes: "the next two bytes … are not in the ranges" is vacuously
satisfied, so the `%` is copied and nothing is dropped or truncated.
`URL-PE-CE-003` and `URL-PE-CE-004` attack the two mutants. -/
theorem percentDecodeBytes_short (tail : Whatwg.Infra.ByteSequence) :
    List.length tail < 2 →
      percentDecodeBytes (0x25 :: tail) = 0x25 :: percentDecodeBytes tail := by
  intro h
  match tail with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => exact absurd h (by simp)

/-! ### Size and fixed-point laws of percent-decode

The closing note of `op.percent-decode-string` [18464,18967): "In general,
percent-encoding results in a string with more U+0025 (%) code points than the
input, and percent-decoding results in a byte sequence with less 0x25 (%) bytes
than the input." Stated as the two monotonicity facts that hold for every input;
the strict reading fails on inputs with no escape, which "in general"
acknowledges. -/

private theorem filter_percent_cons (byte : Whatwg.Infra.Byte)
    (tail : Whatwg.Infra.ByteSequence) :
    List.length (List.filter (fun other => other == 0x25) (byte :: tail)) =
      (if byte = 0x25 then 1 else 0) +
        List.length (List.filter (fun other => other == 0x25) tail) := by
  simp only [List.filter_cons, beq_iff_eq]
  split
  · simp only [List.length_cons]; omega
  · omega

private theorem malformed_of_not_both_hex (first second : Whatwg.Infra.Byte)
    (h : (!(isHexByte first && isHexByte second)) = true) :
    isHexByte first = false ∨ isHexByte second = false := by
  cases h1 : isHexByte first
  · exact Or.inl rfl
  · cases h2 : isHexByte second
    · exact Or.inr rfl
    · simp [h1, h2] at h

private theorem both_hex_of_not_malformed (first second : Whatwg.Infra.Byte)
    (h : ¬((!(isHexByte first && isHexByte second)) = true)) :
    isHexByte first = true ∧ isHexByte second = true := by
  cases h1 : isHexByte first
  · simp [h1] at h
  · cases h2 : isHexByte second
    · simp [h1, h2] at h
    · exact ⟨rfl, rfl⟩

theorem percentDecodeBytes_length_le (input : Whatwg.Infra.ByteSequence) :
    List.length (percentDecodeBytes input) ≤ List.length input := by
  induction input using percentDecodeBytes.induct <;>
    simp_all [percentDecodeBytes] <;> omega

theorem percentDecodeBytes_percent_le (input : Whatwg.Infra.ByteSequence) :
    List.length (List.filter (fun byte => byte == 0x25) (percentDecodeBytes input)) ≤
      List.length (List.filter (fun byte => byte == 0x25) input) := by
  induction input using percentDecodeBytes.induct with
  | case1 => simp [percentDecodeBytes]
  | case2 byte => exact Nat.le_refl _
  | case3 byte other => exact Nat.le_refl _
  | case4 byte first second tail hb ih =>
      rw [percentDecodeBytes_other byte _ hb, filter_percent_cons, filter_percent_cons]
      omega
  | case5 byte first second tail hb hhex ih =>
      have hb' : byte = 0x25 := by simpa using hb
      subst hb'
      rw [percentDecodeBytes_malformed_pair first second tail
        (malformed_of_not_both_hex first second hhex),
        filter_percent_cons, filter_percent_cons]
      omega
  | case6 byte first second tail hb hhex ih =>
      have hb' : byte = 0x25 := by simpa using hb
      subst hb'
      obtain ⟨h1, h2⟩ := both_hex_of_not_malformed first second hhex
      rw [percentDecodeBytes_pair first second tail h1 h2, filter_percent_cons,
        filter_percent_cons, filter_percent_cons, filter_percent_cons]
      have hself : (if (0x25 : Whatwg.Infra.Byte) = 0x25 then 1 else 0) = 1 := if_pos rfl
      have hdecoded :
          (if UInt8.ofNat (hexValue first * 16 + hexValue second) = 0x25 then 1 else 0) ≤ 1 := by
        split <;> omega
      have hfirst : (0 : Nat) ≤ (if first = 0x25 then 1 else 0) := Nat.zero_le _
      have hsecond : (0 : Nat) ≤ (if second = 0x25 then 1 else 0) := Nat.zero_le _
      omega

/-- A byte sequence with no `%` is its own percent-decoding. -/
theorem percentDecodeBytes_id_of_no_percent (input : Whatwg.Infra.ByteSequence) :
    (0x25 : Whatwg.Infra.Byte) ∉ input → percentDecodeBytes input = input := by
  induction input using percentDecodeBytes.induct with
  | case1 => intro _; rfl
  | case2 byte => intro _; rfl
  | case3 byte other => intro _; rfl
  | case4 byte first second tail hb ih =>
      intro hmem
      rw [percentDecodeBytes_other byte _ hb,
        ih (fun hc => hmem (List.mem_cons_of_mem _ hc))]
  | case5 byte first second tail hb _ ih =>
      intro hmem
      have hb' : byte = 0x25 := by simpa using hb
      subst hb'
      exact absurd (by simp) hmem
  | case6 byte first second tail hb _ ih =>
      intro hmem
      have hb' : byte = 0x25 := by simpa using hb
      subst hb'
      exact absurd (by simp) hmem

/-- Percent-decoding is **not** idempotent, and the text does not claim it is:
`%2525` decodes to `%25`, which decodes again to `%`. The absence of an
idempotence law is frozen with this witness rather than omitted. -/
theorem percentDecodeBytes_not_idempotent :
    percentDecodeBytes (percentDecodeBytes [0x25, 0x32, 0x35, 0x32, 0x35]) ≠
      percentDecodeBytes [0x25, 0x32, 0x35, 0x32, 0x35] := by
  decide

/-! ## Percent-decode a scalar value string, and the UTF-8 advice -/

/-- Row `op.percent-decode-string` [18464,18967). -/
theorem percentDecodeString_eq (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    percentDecodeString encoding =
      percentDecodeBytes (Whatwg.Url.Boundary.Utf8Encoding.bytes encoding) := rfl

/-- Row `requirement.percent-encoded-utf8-advice` [16325,16862). -/
theorem followsUtf8Advice_iff (input : Whatwg.Infra.ByteSequence)
    (answer : Whatwg.Url.Boundary.Utf8DecodeOrFail) :
    followsUtf8Advice input answer ↔
      (Whatwg.Url.Boundary.Utf8DecodeOrFail.input answer = percentDecodeBytes input ∧
        Whatwg.Url.Boundary.Utf8DecodeOrFail.failed answer = false) := Iff.rfl

/-! ## Step 7.4's base-ten digits -/

private theorem lt_ten_cases (n : Nat) (h : n < 10) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  omega

private theorem decimalDigitUnit_isAsciiDigit (digit : Nat) (h : digit < 10) :
    Whatwg.Infra.CodePoint.isAsciiDigit
      (Whatwg.Infra.CodePoint.ofUnit (decimalDigitUnit digit)) = true := by
  rcases lt_ten_cases digit h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem decimalDigitsAux_ne_nil (fuel value : Nat) :
    decimalDigitsAux fuel value ≠ [] := by
  cases fuel with
  | zero => simp [decimalDigitsAux]
  | succ f => simp only [decimalDigitsAux]; split <;> simp

private theorem decimalDigitsAux_all (fuel : Nat) : ∀ value : Nat, value ≤ fuel →
    List.all (decimalDigitsAux fuel value)
      (fun unit => Whatwg.Infra.CodePoint.isAsciiDigit
        (Whatwg.Infra.CodePoint.ofUnit unit)) = true := by
  induction fuel with
  | zero =>
      intro value hv
      have hz : value = 0 := by omega
      subst hz
      simp [decimalDigitsAux, decimalDigitUnit_isAsciiDigit 0 (by omega)]
  | succ f ih =>
      intro value hv
      simp only [decimalDigitsAux]
      split
      · next hlt => simp [decimalDigitUnit_isAsciiDigit value hlt]
      · next hge =>
          have hge' : 10 ≤ value := by omega
          simp [List.all_append, ih (value / 10) (by omega),
            decimalDigitUnit_isAsciiDigit (value % 10) (by omega)]

private theorem decimalDigitsAux_head (fuel : Nat) : ∀ value : Nat, 0 < value → value ≤ fuel →
    List.head? (decimalDigitsAux fuel value) ≠ some 0x30 := by
  induction fuel with
  | zero => intro value h0 hv; omega
  | succ f ih =>
      intro value h0 hv
      simp only [decimalDigitsAux]
      split
      · next hlt =>
          rcases lt_ten_cases value hlt with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · omega
          all_goals decide
      · next hge =>
          have hge' : 10 ≤ value := by omega
          obtain ⟨head, rest, hsplit⟩ :
              ∃ head rest, decimalDigitsAux f (value / 10) = head :: rest := by
            cases hcase : decimalDigitsAux f (value / 10) with
            | nil => exact absurd hcase (decimalDigitsAux_ne_nil f (value / 10))
            | cons a as => exact ⟨a, as, rfl⟩
          have hih := ih (value / 10) (by omega) (by omega)
          rw [hsplit] at hih ⊢
          simpa using hih

/-- Step 7.4 of `op.percent-encode-after-encoding` [21624,24696) on zero. -/
theorem decimalDigits_zero : decimalDigits 0 = [0x30] := rfl

/-- Step 7.4 of `op.percent-encode-after-encoding` [21624,24696): the sequence
is a sequence of ASCII digits. -/
theorem decimalDigits_isAsciiDigits (value : Nat) :
    List.all (decimalDigits value)
      (fun unit => Whatwg.Infra.CodePoint.isAsciiDigit
        (Whatwg.Infra.CodePoint.ofUnit unit)) = true :=
  decimalDigitsAux_all value value (Nat.le_refl value)

/-- Step 7.4 of `op.percent-encode-after-encoding` [21624,24696): "shortest"
means no leading zero above zero. `URL-PE-CE-009` attacks a padded mutant. -/
theorem decimalDigits_shortest (value : Nat) :
    0 < value → List.head? (decimalDigits value) ≠ some 0x30 := by
  intro h
  exact decimalDigitsAux_head value value h (Nat.le_refl value)

/-! ## Percent-encode after encoding, step by step

Row `op.percent-encode-after-encoding` [21624,24696). `encodingAssertion` is
step 1, `spaceAsPlus` step 2, `isomorph` step 7.3.2, `renderByte` steps
7.3.1/7.3.4/7.3.5, `errorReference` step 7.4, `renderAnswer` one iteration of
step 7, and `encodeLoop` the whole while loop. Steps 3 and 4 — `getting an
encoder` and the I/O queue — are the Encoding Standard's, and appear only as the
answer tape `Whatwg.Url.Boundary.EncoderTape`. -/

/-- Step 1: "Assert: encoding is UTF-8 or percentEncodeSet is special-query
percent-encode set or application/x-www-form-urlencoded percent-encode set."
This is not an assertion that the encoding is ASCII-compatible. -/
def encodingAssertion (encoding : Whatwg.Url.Boundary.EncoderName)
    (percentEncodeSet : SetName) : Bool :=
  decide (encoding = Whatwg.Url.Boundary.EncoderName.utf8) ||
    decide (percentEncodeSet = SetName.specialQuery) ||
    decide (percentEncodeSet = SetName.form)

/-- Step 2: "Let spaceAsPlus be true if percentEncodeSet is
application/x-www-form-urlencoded percent-encode set; otherwise false."
`URL-PE-CE-005` and `URL-PE-CE-010` attack the mutants that widen it. -/
def spaceAsPlus (percentEncodeSet : SetName) : Bool :=
  decide (percentEncodeSet = SetName.form)

/-- Step 7.3.2: "Let isomorph be a code point whose value is byte's value." -/
def isomorph (byte : Whatwg.Infra.Byte) : Whatwg.Infra.CodePoint :=
  ⟨byte.value, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le byte.toNat_lt (by decide))⟩

/-- Steps 7.3.1, 7.3.4 and 7.3.5, in the source's own order. Step 7.3.1's
`continue` skips the rest of the iteration, so the space rule is tested before
the set is consulted even though U+0020 is in every named set
(`URL-PE-CE-010`). Step 7.3.3's assertion is discharged by
`setOf_includes_non_ascii` and needs no branch here. -/
def renderByte (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (byte : Whatwg.Infra.Byte) : Whatwg.Infra.JsString :=
  if spaceAsPlusFlag && byte == 0x20 then
    [0x2B]
  else if mem percentEncodeSet (isomorph byte) = false then
    [UInt16.ofNat byte.value]
  else
    percentEncodeByte byte

/-- Step 7.4: append `"%26%23"`, the shortest base-ten ASCII digits of
`potentialError`, and `"%3B"`. -/
def errorReference (potentialError : Nat) : Whatwg.Infra.JsString :=
  ([0x25, 0x32, 0x36, 0x25, 0x32, 0x33] : Whatwg.Infra.JsString) ++
    decimalDigits potentialError ++ ([0x25, 0x33, 0x42] : Whatwg.Infra.JsString)

/-- Steps 7.3 and 7.4 over one `encode or fail` answer. -/
def renderAnswer (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (answer : Whatwg.Url.Boundary.EncodeAnswer) : Whatwg.Infra.JsString :=
  match answer.potentialError with
  | none => List.flatMap (renderByte spaceAsPlusFlag percentEncodeSet) answer.output
  | some potentialError =>
      List.flatMap (renderByte spaceAsPlusFlag percentEncodeSet) answer.output ++
        errorReference potentialError

/-- Step 7's while loop, "While potentialError is non-null", read over the
boundary's answer tape. A null answer is the last iteration and the rest of the
tape is not read (`URL-PE-CE-011`); an empty or exhausted tape is an unanswered
decision, so the loop returns what it has, which is a live frontier and not an
error. -/
def encodeLoop (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet) :
    Whatwg.Url.Boundary.EncoderTape → Whatwg.Infra.JsString
  | [] => []
  | answer :: rest =>
      match answer.potentialError with
      | none => renderAnswer spaceAsPlusFlag percentEncodeSet answer
      | some _ =>
          renderAnswer spaceAsPlusFlag percentEncodeSet answer ++
            encodeLoop spaceAsPlusFlag percentEncodeSet rest

/-- Row `op.percent-encode-after-encoding` [21624,24696) assembled: steps 2, 5,
6, 7 and 8 over the boundary's answer tape. Steps 3 and 4 produced the tape and
are the Encoding Standard's; step 1 is the separate predicate
`encodingAssertion`. -/
def percentEncodeAfterEncoding (_encoding : Whatwg.Url.Boundary.EncoderName)
    (percentEncodeSet : SetName) (tape : Whatwg.Url.Boundary.EncoderTape) :
    Whatwg.Infra.JsString :=
  encodeLoop (spaceAsPlus percentEncodeSet) (setOf percentEncodeSet) tape

/-- Row `op.utf8-percent-encode-string` [25073,25393): "return the result of
running percent-encode after encoding with UTF-8, input, and
percentEncodeSet". -/
def utf8PercentEncodeString (input : Whatwg.Url.Boundary.Utf8Encoding)
    (percentEncodeSet : SetName) : Whatwg.Infra.JsString :=
  percentEncodeAfterEncoding Whatwg.Url.Boundary.EncoderName.utf8 percentEncodeSet input.tape

/-- Row `op.utf8-percent-encode-code-point` [24698,25071): "return the result of
running percent-encode after encoding with UTF-8, scalarValue as a string, and
percentEncodeSet". The encoding argument is the boundary's answer for
`scalarValue` as a string, which `utf8PercentEncodeCodePoint_eq` ties to the
scalar value. -/
def utf8PercentEncodeCodePoint (_scalarValue : Whatwg.Infra.ScalarValue)
    (input : Whatwg.Url.Boundary.Utf8Encoding) (percentEncodeSet : SetName) :
    Whatwg.Infra.JsString :=
  utf8PercentEncodeString input percentEncodeSet

/-! ### The step laws -/

/-- Step 1 of `op.percent-encode-after-encoding` [21624,24696). -/
theorem encodingAssertion_iff (encoding : Whatwg.Url.Boundary.EncoderName) (n : SetName) :
    encodingAssertion encoding n = true ↔
      (encoding = Whatwg.Url.Boundary.EncoderName.utf8 ∨
        n = SetName.specialQuery ∨ n = SetName.form) := by
  simp [encodingAssertion, or_assoc]

/-- Step 2 of `op.percent-encode-after-encoding` [21624,24696). -/
theorem spaceAsPlus_iff (n : SetName) : spaceAsPlus n = true ↔ n = SetName.form := by
  simp [spaceAsPlus]

/-- Step 7.3.2 of `op.percent-encode-after-encoding` [21624,24696). -/
theorem isomorph_val (byte : Whatwg.Infra.Byte) :
    (isomorph byte).val = Whatwg.Infra.Byte.value byte := rfl

/-- Step 7.3.1 of `op.percent-encode-after-encoding` [21624,24696): the space
rule is taken before the set is consulted, so it applies even though U+0020 is
in every named set. -/
theorem renderByte_plus (percentEncodeSet : PercentEncodeSet) :
    renderByte true percentEncodeSet 0x20 = [0x2B] := rfl

/-- Step 7.3.4 of `op.percent-encode-after-encoding` [21624,24696): "If isomorph
is not in percentEncodeSet, then append isomorph to output." -/
theorem renderByte_isomorph (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (byte : Whatwg.Infra.Byte) :
    (spaceAsPlusFlag = false ∨ byte ≠ 0x20) →
    mem percentEncodeSet (isomorph byte) = false →
      renderByte spaceAsPlusFlag percentEncodeSet byte =
        [UInt16.ofNat (Whatwg.Infra.Byte.value byte)] := by
  intro hplus hmem
  have hcond : (spaceAsPlusFlag && byte == 0x20) = false := by
    rcases hplus with rfl | hne
    · rfl
    · simp [hne]
  simp [renderByte, hcond, hmem]

/-- Step 7.3.5 of `op.percent-encode-after-encoding` [21624,24696): "Otherwise,
percent-encode byte and append the result to output." -/
theorem renderByte_encoded (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (byte : Whatwg.Infra.Byte) :
    (spaceAsPlusFlag = false ∨ byte ≠ 0x20) →
    mem percentEncodeSet (isomorph byte) = true →
      renderByte spaceAsPlusFlag percentEncodeSet byte = percentEncodeByte byte := by
  intro hplus hmem
  have hcond : (spaceAsPlusFlag && byte == 0x20) = false := by
    rcases hplus with rfl | hne
    · rfl
    · simp [hne]
  simp [renderByte, hcond, hmem]

/-- Step 7.4 of `op.percent-encode-after-encoding` [21624,24696). -/
theorem errorReference_eq (potentialError : Nat) :
    errorReference potentialError =
      ([0x25, 0x32, 0x36, 0x25, 0x32, 0x33] : Whatwg.Infra.JsString) ++
        decimalDigits potentialError ++ ([0x25, 0x33, 0x42] : Whatwg.Infra.JsString) := rfl

/-- Step 7.3 of `op.percent-encode-after-encoding` [21624,24696) over one answer
that reported no error. -/
theorem renderAnswer_none (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (answer : Whatwg.Url.Boundary.EncodeAnswer) :
    Whatwg.Url.Boundary.EncodeAnswer.potentialError answer = none →
      renderAnswer spaceAsPlusFlag percentEncodeSet answer =
        List.flatMap (renderByte spaceAsPlusFlag percentEncodeSet)
          (Whatwg.Url.Boundary.EncodeAnswer.output answer) := by
  intro h
  simp [renderAnswer, h]

/-- Steps 7.3 and 7.4 of `op.percent-encode-after-encoding` [21624,24696) over
one answer that reported an error. -/
theorem renderAnswer_some (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (answer : Whatwg.Url.Boundary.EncodeAnswer) (potentialError : Nat) :
    Whatwg.Url.Boundary.EncodeAnswer.potentialError answer = some potentialError →
      renderAnswer spaceAsPlusFlag percentEncodeSet answer =
        List.flatMap (renderByte spaceAsPlusFlag percentEncodeSet)
            (Whatwg.Url.Boundary.EncodeAnswer.output answer) ++
          errorReference potentialError := by
  intro h
  simp [renderAnswer, h]

/-- An unanswered encoder decision is a live frontier, not an error: the empty
tape produces the empty string. -/
theorem encodeLoop_nil (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet) :
    encodeLoop spaceAsPlusFlag percentEncodeSet [] = [] := rfl

/-- Step 7's loop condition, "While potentialError is non-null": a null answer
is the last iteration and the rest of the tape is not read. `URL-PE-CE-011`
attacks the mutant that keeps going. -/
theorem encodeLoop_terminal (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (answer : Whatwg.Url.Boundary.EncodeAnswer) (rest : Whatwg.Url.Boundary.EncoderTape) :
    Whatwg.Url.Boundary.EncodeAnswer.potentialError answer = none →
      encodeLoop spaceAsPlusFlag percentEncodeSet (answer :: rest) =
        renderAnswer spaceAsPlusFlag percentEncodeSet answer := by
  intro h
  simp [encodeLoop, h]

/-- Step 7's loop body over a non-null answer. -/
theorem encodeLoop_cons (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (answer : Whatwg.Url.Boundary.EncodeAnswer) (rest : Whatwg.Url.Boundary.EncoderTape)
    (potentialError : Nat) :
    Whatwg.Url.Boundary.EncodeAnswer.potentialError answer = some potentialError →
      encodeLoop spaceAsPlusFlag percentEncodeSet (answer :: rest) =
        renderAnswer spaceAsPlusFlag percentEncodeSet answer ++
          encodeLoop spaceAsPlusFlag percentEncodeSet rest := by
  intro h
  simp [encodeLoop, h]

/-- The loop distributes over a tape split before its terminating answer. This
is the URL-owned half of composition; whether the **encoder** distributes over a
split of the input is a boundary property, and it is false for ISO-2022-JP
(`URL-PE-CE-006`). -/
theorem encodeLoop_append (spaceAsPlusFlag : Bool) (percentEncodeSet : PercentEncodeSet)
    (front back : Whatwg.Url.Boundary.EncoderTape) :
    List.all front
        (fun answer =>
          Option.isSome (Whatwg.Url.Boundary.EncodeAnswer.potentialError answer)) = true →
      encodeLoop spaceAsPlusFlag percentEncodeSet (front ++ back) =
        encodeLoop spaceAsPlusFlag percentEncodeSet front ++
          encodeLoop spaceAsPlusFlag percentEncodeSet back := by
  induction front with
  | nil => intro _; rfl
  | cons answer rest ih =>
      intro hall
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hsome, hrest⟩ := hall
      obtain ⟨potentialError, hpe⟩ : ∃ k, answer.potentialError = some k := by
        cases hcase : answer.potentialError with
        | none => rw [hcase] at hsome; exact absurd hsome (by simp)
        | some k => exact ⟨k, rfl⟩
      rw [List.cons_append, encodeLoop_cons _ _ _ _ _ hpe, encodeLoop_cons _ _ _ _ _ hpe,
        ih hrest, List.append_assoc]

/-- Row `op.percent-encode-after-encoding` [21624,24696) assembled. -/
theorem percentEncodeAfterEncoding_eq (encoding : Whatwg.Url.Boundary.EncoderName)
    (n : SetName) (tape : Whatwg.Url.Boundary.EncoderTape) :
    percentEncodeAfterEncoding encoding n tape =
      encodeLoop (spaceAsPlus n) (setOf n) tape := rfl

/-- Row `op.utf8-percent-encode-string` [25073,25393). -/
theorem utf8PercentEncodeString_eq (encoding : Whatwg.Url.Boundary.Utf8Encoding)
    (n : SetName) :
    utf8PercentEncodeString encoding n =
      percentEncodeAfterEncoding Whatwg.Url.Boundary.EncoderName.utf8 n
        (Whatwg.Url.Boundary.Utf8Encoding.tape encoding) := rfl

/-- The UTF-8 case collapses to a per-byte rendering with no error reference:
UTF-8 encodes every scalar value, so step 7 runs once with a null
`potentialError`. -/
theorem utf8PercentEncodeString_flatMap (encoding : Whatwg.Url.Boundary.Utf8Encoding)
    (n : SetName) :
    utf8PercentEncodeString encoding n =
      List.flatMap (renderByte (spaceAsPlus n) (setOf n))
        (Whatwg.Url.Boundary.Utf8Encoding.bytes encoding) := rfl

/-- The composition law: the encode-then-percent-encode pipeline is a monoid
homomorphism from UTF-8 byte concatenation to string concatenation, because
UTF-8 is stateless and the rendering is per byte. `URL-PE-CE-006` witnesses that
the corresponding statement fails for a stateful encoder. -/
theorem utf8PercentEncodeString_append (front back whole : Whatwg.Url.Boundary.Utf8Encoding)
    (n : SetName) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes whole =
        Whatwg.Url.Boundary.Utf8Encoding.bytes front ++
          Whatwg.Url.Boundary.Utf8Encoding.bytes back →
      utf8PercentEncodeString whole n =
        utf8PercentEncodeString front n ++ utf8PercentEncodeString back n := by
  intro h
  rw [utf8PercentEncodeString_flatMap, utf8PercentEncodeString_flatMap,
    utf8PercentEncodeString_flatMap, h, List.flatMap_append]

/-- Row `op.utf8-percent-encode-code-point` [24698,25071): the code-point form is
the string form at "scalarValue as a string". -/
theorem utf8PercentEncodeCodePoint_eq (scalarValue : Whatwg.Infra.ScalarValue)
    (encoding : Whatwg.Url.Boundary.Utf8Encoding) (n : SetName) :
    Whatwg.Url.Boundary.Utf8Encoding.input encoding =
        Whatwg.Infra.JsString.ofCodePoints [scalarValue.val] →
      utf8PercentEncodeCodePoint scalarValue encoding n =
        utf8PercentEncodeString encoding n := by
  intro _
  rfl

/-! ## The ASCII face of the rendered output

The round-trip laws of `op.percent-encode-after-encoding` [21624,24696) are
stated through `Whatwg.Infra.JsString.asciiEncode?`, so the rendered string has
to be recognised as an ASCII string and its bytes computed. The four lemmas
below do exactly that and are local to this module: nothing under
`Whatwg/Infra/` changes. They are recorded as Infra candidates in the contract's
Builder notes. -/

private theorem ofUnit_val (unit : Whatwg.Infra.CodeUnit) :
    (Whatwg.Infra.CodePoint.ofUnit unit).val = unit.toNat := rfl

/-- A string with no leading surrogate has one code point per code unit. -/
private theorem codePoints_of_no_lead (input : Whatwg.Infra.JsString)
    (h : ∀ unit ∈ input, unit.toNat < 0xD800) :
    Whatwg.Infra.JsString.codePoints input =
      List.map Whatwg.Infra.CodePoint.ofUnit input := by
  induction input with
  | nil => rfl
  | cons unit rest ih =>
      have hu : ¬ (0xD800 ≤ unit.toNat ∧ unit.toNat ≤ 0xDBFF) := by
        have := h unit (by simp)
        omega
      rw [Whatwg.Infra.JsString.codePoints.eq_2, dif_neg hu, List.map_cons,
        ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

private theorem isAsciiString_of_units (input : Whatwg.Infra.JsString)
    (h : ∀ unit ∈ input, unit.toNat ≤ 0x7F) :
    Whatwg.Infra.JsString.isAsciiString input = true := by
  have hlead : ∀ unit ∈ input, unit.toNat < 0xD800 := fun u hu => by
    have := h u hu
    omega
  rw [Whatwg.Infra.JsString.isAsciiString, codePoints_of_no_lead input hlead,
    List.all_eq_true]
  intro codePoint hcp
  obtain ⟨unit, hunit, hcu⟩ := List.mem_map.mp hcp
  subst hcu
  have hle := h unit hunit
  simp only [Whatwg.Infra.CodePoint.isAscii, Whatwg.Infra.CodePoint.inRange, ofUnit_val]
  exact decide_eq_true ⟨Nat.zero_le _, hle⟩

private theorem pmap_eq_map_of {α β : Type} {p : α → Prop} (f : (a : α) → p a → β) (g : α → β)
    (hfg : ∀ (a : α) (ha : p a), f a ha = g a) :
    ∀ (l : List α) (H : ∀ a ∈ l, p a), List.pmap f l H = List.map g l
  | [], _ => rfl
  | a :: l, H => by
      simp only [List.pmap, List.map, hfg]
      rw [pmap_eq_map_of f g hfg l]

private theorem isomorphicEncode_eq (input : Whatwg.Infra.JsString)
    (h : Whatwg.Infra.JsString.isIsomorphicString input = true) :
    Whatwg.Infra.JsString.isomorphicEncode input h =
      List.map (fun codePoint => UInt8.ofNat codePoint.val)
        (Whatwg.Infra.JsString.codePoints input) := by
  unfold Whatwg.Infra.JsString.isomorphicEncode
  exact pmap_eq_map_of _ _ (fun codePoint _ => UInt8.ofNatLT_eq_ofNat codePoint.val) _ _

/-- The byte of one ASCII code unit. -/
private def unitByte (unit : Whatwg.Infra.CodeUnit) : Whatwg.Infra.Byte :=
  UInt8.ofNat unit.toNat

/-- The ASCII encoding of a string all of whose code units are ASCII. -/
private def asciiBytes (input : Whatwg.Infra.JsString) : Whatwg.Infra.ByteSequence :=
  List.map unitByte input

private theorem asciiEncode?_eq (input : Whatwg.Infra.JsString)
    (h : ∀ unit ∈ input, unit.toNat ≤ 0x7F) :
    Whatwg.Infra.JsString.asciiEncode? input = some (asciiBytes input) := by
  have hA : Whatwg.Infra.JsString.isAsciiString input = true := isAsciiString_of_units input h
  have hlead : ∀ unit ∈ input, unit.toNat < 0xD800 := fun u hu => by
    have := h u hu
    omega
  unfold Whatwg.Infra.JsString.asciiEncode?
  rw [dif_pos hA]
  congr 1
  unfold Whatwg.Infra.JsString.asciiEncode
  rw [isomorphicEncode_eq, codePoints_of_no_lead input hlead, List.map_map]
  rfl

private theorem unitByte_upperHexDigit_isHex (n : Nat) (h : n < 16) :
    isHexByte (unitByte (upperHexDigit n)) = true := by
  rcases lt_sixteen_cases n h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem hexValue_unitByte_upperHexDigit (n : Nat) (h : n < 16) :
    hexValue (unitByte (upperHexDigit n)) = n := by
  rcases lt_sixteen_cases n h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-! ### Every rendered code unit is ASCII -/

private theorem upperHexDigit_toNat_le (n : Nat) (h : n < 16) : (upperHexDigit n).toNat ≤ 0x7F := by
  rw [upperHexDigit_toNat n h]
  split <;> omega

private theorem renderByte_units_ascii (spaceAsPlusFlag : Bool) (n : SetName)
    (byte : Whatwg.Infra.Byte) :
    ∀ unit ∈ renderByte spaceAsPlusFlag (setOf n) byte, unit.toNat ≤ 0x7F := by
  have hb : Whatwg.Infra.Byte.value byte < 256 := byte.toNat_lt
  intro unit hunit
  unfold renderByte at hunit
  split at hunit
  · simp only [List.mem_singleton] at hunit
    subst hunit
    decide
  · split at hunit
    · rename_i hmem
      have hascii : Whatwg.Infra.CodePoint.isAscii (isomorph byte) = true := by
        cases hcase : Whatwg.Infra.CodePoint.isAscii (isomorph byte) with
        | false =>
            rw [setOf_includes_non_ascii n _ hcase] at hmem
            exact absurd hmem (by simp)
        | true => rfl
      have hle : Whatwg.Infra.Byte.value byte ≤ 0x7F := by
        simp only [Whatwg.Infra.CodePoint.isAscii, Whatwg.Infra.CodePoint.inRange,
          isomorph] at hascii
        exact (of_decide_eq_true hascii).2
      simp only [List.mem_singleton] at hunit
      subst hunit
      simp only [toNat_ofNat16]
      omega
    · simp only [percentEncodeByte, List.mem_cons, List.not_mem_nil, or_false] at hunit
      rcases hunit with rfl | rfl | rfl
      · decide
      · exact upperHexDigit_toNat_le _ (by omega)
      · exact upperHexDigit_toNat_le _ (by omega)

private theorem utf8PercentEncodeString_units_ascii
    (encoding : Whatwg.Url.Boundary.Utf8Encoding) (n : SetName) :
    ∀ unit ∈ utf8PercentEncodeString encoding n, unit.toNat ≤ 0x7F := by
  intro unit hunit
  rw [utf8PercentEncodeString_flatMap] at hunit
  obtain ⟨byte, _, hmem⟩ := List.mem_flatMap.mp hunit
  exact renderByte_units_ascii _ n byte unit hmem

/-- Every named set contains every code point above U+007E, so the output of the
UTF-8 specialization is an ASCII string and the round-trip laws below may use
`Whatwg.Infra.JsString.asciiEncode?`. -/
theorem utf8PercentEncodeString_isAsciiString (encoding : Whatwg.Url.Boundary.Utf8Encoding)
    (n : SetName) :
    Whatwg.Infra.JsString.isAsciiString (utf8PercentEncodeString encoding n) = true :=
  isAsciiString_of_units _ (utf8PercentEncodeString_units_ascii encoding n)

/-! ## Round trips, on their exact stated domains

The closing note of `op.percent-encode-after-encoding` [21624,24696): "Of the
possible values for the percentEncodeSet argument only two end up encoding
U+0025 (%) and thus give 'roundtripable data': component percent-encode set and
application/x-www-form-urlencoded percent-encode set." -/

/-- The unconditional byte-level round trip, with no domain restriction. -/
theorem percentDecodeBytes_percentEncodeByte (byte : Whatwg.Infra.Byte) :
    Option.map percentDecodeBytes
      (Whatwg.Infra.JsString.asciiEncode? (percentEncodeByte byte)) = some [byte] := by
  have hb : Whatwg.Infra.Byte.value byte < 256 := byte.toNat_lt
  have hunits : ∀ unit ∈ percentEncodeByte byte, unit.toNat ≤ 0x7F := by
    intro unit hunit
    simp only [percentEncodeByte, List.mem_cons, List.not_mem_nil, or_false] at hunit
    rcases hunit with rfl | rfl | rfl
    · decide
    · exact upperHexDigit_toNat_le _ (by omega)
    · exact upperHexDigit_toNat_le _ (by omega)
  rw [asciiEncode?_eq _ hunits, Option.map_some]
  congr 1
  have hshape : asciiBytes (percentEncodeByte byte) =
      0x25 :: unitByte (upperHexDigit (Whatwg.Infra.Byte.value byte / 16)) ::
        unitByte (upperHexDigit (Whatwg.Infra.Byte.value byte % 16)) :: [] := rfl
  rw [hshape, percentDecodeBytes_pair _ _ []
      (unitByte_upperHexDigit_isHex _ (by omega))
      (unitByte_upperHexDigit_isHex _ (by omega)),
    hexValue_unitByte_upperHexDigit _ (by omega),
    hexValue_unitByte_upperHexDigit _ (by omega),
    show Whatwg.Infra.Byte.value byte / 16 * 16 + Whatwg.Infra.Byte.value byte % 16 =
      Whatwg.Infra.Byte.value byte from by omega]
  exact congrArg (fun b => [b]) UInt8.ofNat_toNat

private theorem decode_renderByte (spaceAsPlusFlag : Bool) (n : SetName)
    (h25 : mem (setOf n) (isomorph 0x25) = true) (byte : Whatwg.Infra.Byte)
    (hbyte : spaceAsPlusFlag = true → byte ≠ 0x20) (tail : Whatwg.Infra.ByteSequence) :
    percentDecodeBytes (asciiBytes (renderByte spaceAsPlusFlag (setOf n) byte) ++ tail) =
      byte :: percentDecodeBytes tail := by
  have hb : Whatwg.Infra.Byte.value byte < 256 := byte.toNat_lt
  have hplus : spaceAsPlusFlag = false ∨ byte ≠ 0x20 := by
    cases spaceAsPlusFlag with
    | false => exact Or.inl rfl
    | true => exact Or.inr (hbyte rfl)
  cases hmem : mem (setOf n) (isomorph byte) with
  | false =>
      have hascii : Whatwg.Infra.CodePoint.isAscii (isomorph byte) = true := by
        cases hcase : Whatwg.Infra.CodePoint.isAscii (isomorph byte) with
        | false =>
            rw [setOf_includes_non_ascii n _ hcase] at hmem
            exact absurd hmem (by simp)
        | true => rfl
      have hle : Whatwg.Infra.Byte.value byte ≤ 0x7F := by
        simp only [Whatwg.Infra.CodePoint.isAscii, Whatwg.Infra.CodePoint.inRange,
          isomorph] at hascii
        exact (of_decide_eq_true hascii).2
      have hne : byte ≠ 0x25 := by
        intro heq
        subst heq
        rw [h25] at hmem
        exact absurd hmem (by simp)
      have hshape : asciiBytes (renderByte spaceAsPlusFlag (setOf n) byte) = [byte] := by
        rw [renderByte_isomorph _ _ _ hplus hmem]
        simp only [asciiBytes, List.map_cons, List.map_nil, unitByte, toNat_ofNat16,
          Nat.mod_eq_of_lt (show Whatwg.Infra.Byte.value byte < 65536 by omega)]
        exact congrArg (fun b => [b]) UInt8.ofNat_toNat
      rw [hshape, List.cons_append, List.nil_append, percentDecodeBytes_other byte tail hne]
  | true =>
      have hshape : asciiBytes (renderByte spaceAsPlusFlag (setOf n) byte) =
          0x25 :: unitByte (upperHexDigit (Whatwg.Infra.Byte.value byte / 16)) ::
            unitByte (upperHexDigit (Whatwg.Infra.Byte.value byte % 16)) :: [] := by
        rw [renderByte_encoded _ _ _ hplus hmem]
        rfl
      rw [hshape, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        percentDecodeBytes_pair _ _ tail
          (unitByte_upperHexDigit_isHex _ (by omega))
          (unitByte_upperHexDigit_isHex _ (by omega)),
        hexValue_unitByte_upperHexDigit _ (by omega),
        hexValue_unitByte_upperHexDigit _ (by omega),
        show Whatwg.Infra.Byte.value byte / 16 * 16 + Whatwg.Infra.Byte.value byte % 16 =
          Whatwg.Infra.Byte.value byte from by omega]
      exact congrArg (fun b => b :: percentDecodeBytes tail) UInt8.ofNat_toNat

private theorem decode_render_flatMap (spaceAsPlusFlag : Bool) (n : SetName)
    (h25 : mem (setOf n) (isomorph 0x25) = true) (input : Whatwg.Infra.ByteSequence)
    (hinput : spaceAsPlusFlag = true → (0x20 : Whatwg.Infra.Byte) ∉ input) :
    percentDecodeBytes
        (asciiBytes (List.flatMap (renderByte spaceAsPlusFlag (setOf n)) input)) = input := by
  induction input with
  | nil => rfl
  | cons byte rest ih =>
      have hbyte : spaceAsPlusFlag = true → byte ≠ 0x20 := by
        intro hsp heq
        exact hinput hsp (by rw [← heq]; simp)
      have hrest : spaceAsPlusFlag = true → (0x20 : Whatwg.Infra.Byte) ∉ rest := by
        intro hsp hmem
        exact hinput hsp (List.mem_cons_of_mem _ hmem)
      simp only [List.flatMap_cons, asciiBytes, List.map_append]
      rw [show List.map unitByte (renderByte spaceAsPlusFlag (setOf n) byte) =
            asciiBytes (renderByte spaceAsPlusFlag (setOf n) byte) from rfl,
        decode_renderByte spaceAsPlusFlag n h25 byte hbyte _]
      rw [show List.map unitByte (List.flatMap (renderByte spaceAsPlusFlag (setOf n)) rest) =
            asciiBytes (List.flatMap (renderByte spaceAsPlusFlag (setOf n)) rest) from rfl,
        ih hrest]

/-- The component set round-trips on its whole domain: every UTF-8 byte
sequence. It is the only named set that both encodes U+0025 and never maps
U+0020 to `+`. -/
theorem roundTrip_component (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Option.map percentDecodeBytes
        (Whatwg.Infra.JsString.asciiEncode?
          (utf8PercentEncodeString encoding SetName.component)) =
      some (Whatwg.Url.Boundary.Utf8Encoding.bytes encoding) := by
  rw [asciiEncode?_eq _ (utf8PercentEncodeString_units_ascii encoding SetName.component),
    Option.map_some]
  congr 1
  rw [utf8PercentEncodeString_flatMap]
  exact decode_render_flatMap (spaceAsPlus SetName.component) SetName.component (by decide) _
    (by intro h; exact absurd h (by decide))

/-- The form set round-trips on the strictly smaller domain of byte sequences
containing no 0x20 (SP), because step 7.3.1 maps SP to U+002B (+) and
percent-decode does not undo that. The plus rule belongs to
`op.urlencoded-parser` (U7), not to percent-decode. -/
theorem roundTrip_form (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    (0x20 : Whatwg.Infra.Byte) ∉ Whatwg.Url.Boundary.Utf8Encoding.bytes encoding →
      Option.map percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (utf8PercentEncodeString encoding SetName.form)) =
        some (Whatwg.Url.Boundary.Utf8Encoding.bytes encoding) := by
  intro hspace
  rw [asciiEncode?_eq _ (utf8PercentEncodeString_units_ascii encoding SetName.form),
    Option.map_some]
  congr 1
  rw [utf8PercentEncodeString_flatMap]
  exact decode_render_flatMap (spaceAsPlus SetName.form) SetName.form (by decide) _
    (fun _ => hspace)

/-- The form set fails to round-trip at the first space: `"%20"` in, `"+"` out,
`0x2B` back. The domain restriction above is exactly needed. -/
theorem roundTrip_form_space_fails (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding = [0x20] →
      Option.map percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (utf8PercentEncodeString encoding SetName.form)) = some [0x2B] := by
  intro hbytes
  rw [utf8PercentEncodeString_flatMap, hbytes]
  decide

/-- The five parser sets do not round-trip: they leave U+0025 untouched, so an
input that already looks like an escape decodes to something else. Witness
`"%41"`, which returns as the single byte `0x41`. The text's own remedy, UTF-8
percent-encoding the `%` first, is a U5 caller's job. -/
theorem roundTrip_query_fails (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding = [0x25, 0x34, 0x31] →
      Option.map percentDecodeBytes
          (Whatwg.Infra.JsString.asciiEncode?
            (utf8PercentEncodeString encoding SetName.query)) = some [0x41] := by
  intro hbytes
  rw [utf8PercentEncodeString_flatMap, hbytes]
  decide

/-- The one case the URL side can discharge for
`requirement.percent-encoded-utf8-advice` [16325,16862): output of the component
set percent-decodes back to the UTF-8 bytes it came from, so the advice reduces
to the boundary's non-failure hypothesis on exactly those bytes. The `host
parser` and `URL rendering` consumers the note names are U4 and U6 rows. -/
theorem followsUtf8Advice_component (encoding : Whatwg.Url.Boundary.Utf8Encoding)
    (input : Whatwg.Infra.ByteSequence) (answer : Whatwg.Url.Boundary.Utf8DecodeOrFail) :
    Whatwg.Infra.JsString.asciiEncode?
        (utf8PercentEncodeString encoding SetName.component) = some input →
      Whatwg.Url.Boundary.Utf8DecodeOrFail.input answer =
        Whatwg.Url.Boundary.Utf8Encoding.bytes encoding →
      Whatwg.Url.Boundary.Utf8DecodeOrFail.failed answer = false →
        followsUtf8Advice input answer := by
  intro hencode hinput hfailed
  have hround := roundTrip_component encoding
  rw [hencode, Option.map_some, Option.some.injEq] at hround
  exact ⟨by rw [hinput, hround], hfailed⟩

/-! ## Finite probes from the source's own example table [25459,27305)

Evidence class: finite probes, never laws. The region is an authored explanation
with SHA-256 `4fa270b4ef01f88fe9fd30b223aa39184e6b3f323c03a1978583f0a00b91aec8`
and carries no census row; its eleven rows are transcribed here as thirteen
probes against the production names. A passing probe closes no clause. -/

/-- Percent-encode 0x23: `"%23"`. -/
theorem percentEncodeByte_example_23 : percentEncodeByte 0x23 = [0x25, 0x32, 0x33] := by
  decide

/-- Percent-encode 0x7F: `"%7F"`. -/
theorem percentEncodeByte_example_7F : percentEncodeByte 0x7F = [0x25, 0x37, 0x46] := by
  decide

/-- `` `%25%s%1G` `` percent-decodes to `` `%%s%1G` ``. -/
theorem percentDecodeBytes_example :
    percentDecodeBytes [0x25, 0x32, 0x35, 0x25, 0x73, 0x25, 0x31, 0x47] =
      [0x25, 0x25, 0x73, 0x25, 0x31, 0x47] := by
  decide

/-- Lower-case hex is accepted on input: `` `%2e` `` decodes to 0x2E. -/
theorem percentDecodeBytes_example_lowercase :
    percentDecodeBytes [0x25, 0x32, 0x65] = [0x2E] := by
  decide

/-- `"‽%25%2E"` percent-decodes to 0xE2 0x80 0xBD 0x25 0x2E. -/
theorem percentDecodeString_example (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding =
        [0xE2, 0x80, 0xBD, 0x25, 0x32, 0x35, 0x25, 0x32, 0x45] →
      percentDecodeString encoding = [0xE2, 0x80, 0xBD, 0x25, 0x2E] := by
  intro hbytes
  rw [percentDecodeString_eq, hbytes]
  decide

/-- Shift_JIS, `" "`, special-query: `"%20"`. -/
theorem percentEncodeAfterEncoding_example_space (label : Whatwg.Infra.JsString) :
    percentEncodeAfterEncoding (Whatwg.Url.Boundary.EncoderName.other label)
        SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [0x20] none] = [0x25, 0x32, 0x30] := by
  rw [percentEncodeAfterEncoding_eq]
  decide

/-- Shift_JIS, `"≡"`, special-query: `"%81%DF"`. -/
theorem percentEncodeAfterEncoding_example_equiv (label : Whatwg.Infra.JsString) :
    percentEncodeAfterEncoding (Whatwg.Url.Boundary.EncoderName.other label)
        SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [0x81, 0xDF] none] =
      [0x25, 0x38, 0x31, 0x25, 0x44, 0x46] := by
  rw [percentEncodeAfterEncoding_eq]
  decide

/-- Shift_JIS, `"‽"`, special-query: the encoder fails at U+203D and the run
emits `"%26%238253%3B"`. -/
theorem percentEncodeAfterEncoding_example_error (label : Whatwg.Infra.JsString) :
    percentEncodeAfterEncoding (Whatwg.Url.Boundary.EncoderName.other label)
        SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [] (some 8253),
          Whatwg.Url.Boundary.EncodeAnswer.mk [] none] =
      [0x25, 0x32, 0x36, 0x25, 0x32, 0x33, 0x38, 0x32, 0x35, 0x33, 0x25, 0x33, 0x42] := by
  rw [percentEncodeAfterEncoding_eq]
  decide

/-- ISO-2022-JP, `"¥"`, special-query: `` "%1B(J\%1B(B" ``. The escape sequences
the stateful encoder emits are C0 controls and are percent-encoded; the payload
byte 0x5C is not in the special-query set and passes through as `` \ ``. -/
theorem percentEncodeAfterEncoding_example_iso2022jp :
    percentEncodeAfterEncoding Whatwg.Url.Boundary.EncoderName.iso2022jp
        SetName.specialQuery
        [Whatwg.Url.Boundary.EncodeAnswer.mk [0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42] none] =
      [0x25, 0x31, 0x42, 0x28, 0x4A, 0x5C, 0x25, 0x31, 0x42, 0x28, 0x42] := by
  decide

/-- Shift_JIS, `"1+1 ≡ 2%20‽"`, form set:
`"1%2B1+%81%DF+2%2520%26%238253%3B"`. Every distinguishing behaviour of the form
set appears at once: `+` is escaped, SP becomes `+`, `%` is escaped, and the
encoder error becomes a decimal character reference. -/
theorem percentEncodeAfterEncoding_example_form (label : Whatwg.Infra.JsString) :
    percentEncodeAfterEncoding (Whatwg.Url.Boundary.EncoderName.other label) SetName.form
        [Whatwg.Url.Boundary.EncodeAnswer.mk
            [0x31, 0x2B, 0x31, 0x20, 0x81, 0xDF, 0x20, 0x32, 0x25, 0x32, 0x30] (some 8253),
          Whatwg.Url.Boundary.EncodeAnswer.mk [] none] =
      [0x31, 0x25, 0x32, 0x42, 0x31, 0x2B, 0x25, 0x38, 0x31, 0x25, 0x44, 0x46, 0x2B, 0x32,
        0x25, 0x32, 0x35, 0x32, 0x30, 0x25, 0x32, 0x36, 0x25, 0x32, 0x33, 0x38, 0x32, 0x35,
        0x33, 0x25, 0x33, 0x42] := by
  rw [percentEncodeAfterEncoding_eq]
  decide

/-- UTF-8 percent-encode U+2261 (≡) with the userinfo set: `"%E2%89%A1"`. -/
theorem utf8PercentEncodeString_example_equiv (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding = [0xE2, 0x89, 0xA1] →
      utf8PercentEncodeString encoding SetName.userinfo =
        [0x25, 0x45, 0x32, 0x25, 0x38, 0x39, 0x25, 0x41, 0x31] := by
  intro hbytes
  rw [utf8PercentEncodeString_flatMap, hbytes]
  decide

/-- UTF-8 percent-encode U+203D (‽) with the userinfo set: `"%E2%80%BD"`. -/
theorem utf8PercentEncodeString_example_interrobang
    (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding = [0xE2, 0x80, 0xBD] →
      utf8PercentEncodeString encoding SetName.userinfo =
        [0x25, 0x45, 0x32, 0x25, 0x38, 0x30, 0x25, 0x42, 0x44] := by
  intro hbytes
  rw [utf8PercentEncodeString_flatMap, hbytes]
  decide

/-- UTF-8 percent-encode `"Say what‽"` with the userinfo set:
`"Say%20what%E2%80%BD"`. -/
theorem utf8PercentEncodeString_example_say (encoding : Whatwg.Url.Boundary.Utf8Encoding) :
    Whatwg.Url.Boundary.Utf8Encoding.bytes encoding =
        [0x53, 0x61, 0x79, 0x20, 0x77, 0x68, 0x61, 0x74, 0xE2, 0x80, 0xBD] →
      utf8PercentEncodeString encoding SetName.userinfo =
        [0x53, 0x61, 0x79, 0x25, 0x32, 0x30, 0x77, 0x68, 0x61, 0x74, 0x25, 0x45, 0x32,
          0x25, 0x38, 0x30, 0x25, 0x42, 0x44] := by
  intro hbytes
  rw [utf8PercentEncodeString_flatMap, hbytes]
  decide

end Whatwg.Url.PercentEncoding
