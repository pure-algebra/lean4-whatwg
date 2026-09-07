import Whatwg.Infra

/-!
# URL dependency and host boundaries

Owner: the foreign-boundary answer shapes the pinned URL source calls out to,
for the Encoding Standard operations named by `census/url/externals.tsv`.

The Encoding Standard is not pinned in this repository, so `get an encoder`,
`encode or fail`, the I/O queue, `UTF-8 encode`, and
`UTF-8 decode without BOM or fail` have no semantic owner here, and Infra
explicitly defers to Encoding for all of them. DB-02 is the ruling that
applies: a host is a decision, and a decision's answer is first-order data on a
tape, never a modelled body. Every declaration below is such an answer shape.
No encoder algorithm, no decoder algorithm, and no unpinned table is admitted.

Contract: `test/contracts/url-percent-encoding.contract.md`.
Graph: `docs/URL-PERCENT-ENCODING-DAG.md` (`URL-PG-PERCENT`).
Source: `vendor/whatwg-url-55d66993/url.bs`, SHA-256
`a5aa827f544f9077912dc1553cfd9025b6afa4e996460074b5f67d83e0f3c805`. Census rows
of `generated/url-census.tsv` are cited with their `[byte-start,byte-end)` span;
no line number is cited.

The remaining URL boundaries — Unicode UTS #46, Web IDL, HTML origins, File API
blob URL entries, the Public Suffix List, and the IANA scheme and Bidi
requirements — still need named pins and dispositions and have no declaration
here; see `docs/URL-PACKAGE-PLAN.md`.
-/

set_option autoImplicit false

namespace Whatwg.Url.Boundary

open Whatwg.Infra

/-- The name of the encoding step 3 of `op.percent-encode-after-encoding`
[21624,24696) gets an encoder from. This is a first-order name, not an encoder:
no encoding algorithm is modelled anywhere in this repository.

Only two names are distinguished, and both are named by the pin itself:
`utf8`, which step 1's assertion and the two UTF-8 specializations single out,
and `iso2022jp`, the stateful encoder the example table at [25459,27305) and
the note inside `op.parser-query` [116259,118265) both call out. Every other
encoding is carried by its label. -/
inductive EncoderName where
  /-- UTF-8, the encoding step 1 of `op.percent-encode-after-encoding`
  [21624,24696) asserts unless the set is special-query or form. -/
  | utf8
  /-- ISO-2022-JP, the one encoder the pin names as stateful. -/
  | iso2022jp
  /-- Any other encoding, carried by its label. -/
  | other (label : Whatwg.Infra.JsString)
  deriving DecidableEq, Repr

namespace EncoderName

/-- Whether the encoder carries state across `encode or fail` calls. The pin
names exactly one such encoder: `op.parser-query` [116259,118265) says the query
state buffers "due to the stateful ISO-2022-JP encoder", and the example table
at [25459,27305) shows one shift-in and one shift-out around a whole run rather
than around each code point. A stateful encoder's answers are not a function of
the input's code points taken independently, so no per-input-split composition
law is available for it (`URL-PE-CE-006`). -/
def isStateful : EncoderName → Bool
  | iso2022jp => true
  | utf8 => false
  | other _ => false

end EncoderName

/-- One answer of `encode or fail`, as step 7.2 of
`op.percent-encode-after-encoding` [21624,24696) consumes it: the bytes pushed
into `encodeOutput` during the call, and the returned `potentialError`, which
step 7.4 renders in base ten when it is non-null. This is the boundary's answer,
not a stored function. -/
structure EncodeAnswer where
  /-- Step 7.3's "`encodeOutput` converted to a byte sequence". -/
  output : Whatwg.Infra.ByteSequence
  /-- The `potentialError` step 7.2 sets and steps 7 and 7.4 read: the code
  point value the URL text renders in base ten, or null. -/
  potentialError : Option Nat
  deriving DecidableEq, Repr

/-- One run of the while loop of step 7 of `op.percent-encode-after-encoding`
[21624,24696): the sequence of `encode or fail` answers the retained encoder
gave, in order. A short or empty tape is an unanswered decision and therefore a
live frontier, never an error (AGENTS.md, representation rules). -/
abbrev EncoderTape := List EncodeAnswer

namespace EncoderTape

/-- Whether the run recorded by the tape ended, that is, whether its last
answer's `potentialError` is null, which is exactly the negation of step 7's
loop condition "While `potentialError` is non-null". An empty tape is not
terminated: nothing has been answered yet. -/
def terminated (tape : EncoderTape) : Bool :=
  match List.getLast? tape with
  | some answer => Option.isNone answer.potentialError
  | none => false

end EncoderTape

/-- The Encoding Standard's `UTF-8 encode` answer for one scalar value string,
paired with the string it was asked about. `op.percent-decode-string`
[18464,18967), `op.utf8-percent-encode-code-point` [24698,25071) and
`op.utf8-percent-encode-string` [25073,25393) each name `UTF-8 encode` and
nothing else about it; this record is that answer, not a stored function. -/
structure Utf8Encoding where
  /-- The scalar value string handed to `UTF-8 encode`. -/
  input : Whatwg.Infra.JsString
  /-- The byte sequence the Encoding owner returns for it. -/
  bytes : Whatwg.Infra.ByteSequence
  deriving DecidableEq, Repr

namespace Utf8Encoding

/-- The `encode or fail` answer tape a UTF-8 encoder produces for this input.
UTF-8 encodes every scalar value, so the run is one answer whose
`potentialError` is null and whose output is the whole encoding; step 7's loop
therefore runs exactly once. -/
def tape (encoding : Utf8Encoding) : EncoderTape :=
  [EncodeAnswer.mk encoding.bytes none]

end Utf8Encoding

/-- The Encoding Standard's `UTF-8 decode without BOM or fail` answer for one
byte sequence, as `requirement.percent-encoded-utf8-advice` [16325,16862) reads
it: the bytes handed over, and whether the call ended as failure. -/
structure Utf8DecodeOrFail where
  /-- The byte sequence handed to `UTF-8 decode without BOM or fail`. -/
  input : Whatwg.Infra.ByteSequence
  /-- Whether the call ended as failure. -/
  failed : Bool
  deriving DecidableEq, Repr

/-! ## The boundary's two frozen facts and the two tape laws -/

/-- UTF-8 is not stateful: `op.percent-encode-after-encoding` [21624,24696)
retains one encoder across the run, and for UTF-8 that retention is
unobservable. -/
theorem isStateful_utf8 : EncoderName.isStateful EncoderName.utf8 = false := rfl

/-- ISO-2022-JP is stateful. `op.parser-query` [116259,118265) names this
encoder as the reason the query state buffers instead of encoding each code
point independently, and `URL-PE-CE-006` witnesses the difference between a
retained encoder and a per-code-point restart. -/
theorem isStateful_iso2022jp : EncoderName.isStateful EncoderName.iso2022jp = true := rfl

/-- `EncoderTape.terminated` records that a tape ends in a null answer, which is
what makes step 7's loop result a complete run rather than a live frontier.
Row `op.percent-encode-after-encoding` [21624,24696), step 7. -/
theorem EncoderTape.terminated_iff (tape : EncoderTape) :
    EncoderTape.terminated tape = true ↔
      ∃ answer : EncodeAnswer,
        List.getLast? tape = some answer ∧ EncodeAnswer.potentialError answer = none := by
  unfold EncoderTape.terminated
  cases hlast : List.getLast? tape with
  | none => simp
  | some answer =>
    cases hpe : EncodeAnswer.potentialError answer with
    | none => simp
    | some k => simp

/-- UTF-8 never fails, so `encode or fail` answers once with a null
`potentialError` carrying the whole encoding. Rows
`op.utf8-percent-encode-string` [25073,25393) and
`op.utf8-percent-encode-code-point` [24698,25071) run step 7 over exactly this
tape. -/
theorem Utf8Encoding.tape_eq (encoding : Utf8Encoding) :
    Utf8Encoding.tape encoding = [EncodeAnswer.mk (Utf8Encoding.bytes encoding) none] := rfl

end Whatwg.Url.Boundary
