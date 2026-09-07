import Std

/-!
# Finite Infra UTF-8 codec mutants

Independent breaker models for `INFRA-UTF8-CE-001` through `INFRA-UTF8-CE-018`.
Attack record: `test/counterexamples/infra/UTF8.md`.
Contract: `test/contracts/infra-utf8.contract.md`.
Graph: `INFRA-PG-UTF8` (`docs/INFRA-UTF8-DAG.md`).

Every model here is a toy over `List Nat`, deliberately independent of
`Whatwg.Infra.Utf8`. It distinguishes a named mutation from the transcription
the pinned source (`vendor/whatwg-encoding-67494fce/encoding.bs`, SHA-256
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`) requires.
The matching quantified production statements are in
`WhatwgTest/Infra/Utf8Laws.lean`; a passing model here proves nothing about
them, which is why every row of the attack record also names the production
statement that carries the obligation.

Only kernel reduction is used and no production import is needed, so this
module is green from the moment it is committed.
-/

set_option autoImplicit false

namespace WhatwgTest.Infra.Counterexamples.Utf8.Breaker

/-! ## The decoder, with every attacked constant as a parameter

`op.utf-8-decoder` [86515,90406) of the pin. The four boundary constants of the
"0xE0 to 0xEF" and "0xF0 to 0xF4" switch rows are configuration, so a mutant
differs from the transcription in exactly one number; `restoreByte` is step
4.2, "Restore byte to ioQueue"; `truncPerMissingByte` is step 1's single error
on `end-of-queue`. -/

/-- U+FFFD REPLACEMENT CHARACTER, the scalar value the "replacement" arm of
`op.process-an-item` [15509,17620) pushes. -/
def fffd : Nat := 0xFFFD

/-- The decoder's attacked constants. -/
structure Config where
  /-- Step 3.1 of the "0xE0 to 0xEF" row: "If byte is 0xE0, then set UTF-8
  lower boundary to 0xA0." -/
  e0Lower : Nat
  /-- Step 3.2 of the same row: "If byte is 0xED, then set UTF-8 upper boundary
  to 0x9F." -/
  edUpper : Nat
  /-- Step 3.1 of the "0xF0 to 0xF4" row: "If byte is 0xF0, then set UTF-8 lower
  boundary to 0x90." -/
  f0Lower : Nat
  /-- Step 3.2 of the same row: "If byte is 0xF4, then set UTF-8 upper boundary
  to 0x8F." -/
  f4Upper : Nat
  /-- Step 4.2: "Restore byte to ioQueue." -/
  restoreByte : Bool
  /-- Step 1: one error on `end-of-queue`, not one per byte still needed. -/
  truncPerMissingByte : Bool
  /-- Step 3, the "Otherwise" row: "Return error." -/
  errorOnStrayByte : Bool
  deriving DecidableEq, Repr

/-- The transcription of the pin. -/
def spec : Config := ⟨0xA0, 0x9F, 0x90, 0x8F, true, false, true⟩

/-- Step 4's range test, "in the range UTF-8 lower boundary to UTF-8 upper
boundary, inclusive". -/
def inBounds (lo hi n : Nat) : Bool := decide (lo ≤ n ∧ n ≤ hi)

/-- The lower boundary the "0xE0 to 0xEF" and "0xF0 to 0xF4" rows install. -/
def lowerFor (cfg : Config) (b : Nat) : Nat :=
  if b == 0xE0 then cfg.e0Lower else if b == 0xF0 then cfg.f0Lower else 0x80

/-- The upper boundary those two rows install. -/
def upperFor (cfg : Config) (b : Nat) : Nat :=
  if b == 0xED then cfg.edUpper else if b == 0xF4 then cfg.f4Upper else 0xBF

/-- Step 1's answer when the queue ends mid-sequence: one error, or the mutant's
one error per byte still needed. -/
def truncated (cfg : Config) (missing : Nat) : List Nat × Bool :=
  (if cfg.truncPerMissingByte then List.replicate missing fffd else [fffd], false)

/-- Prepend one emitted code point value. -/
def emit (v : Nat) (r : List Nat × Bool) : List Nat × Bool := (v :: r.1, r.2)

/-- Prepend one substituted U+FFFD and record that the run was not clean. -/
def emitError (r : List Nat × Bool) : List Nat × Bool := (fffd :: r.1, false)

/-- One pass of `op.process-a-queue` [14785,15508) over UTF-8's decoder in
"replacement" mode, paired with whether the run produced no `error` at all,
which is the "fatal" mode's answer. Fuel-bounded exactly as
`Whatwg.Infra.ByteSequence.isPrefixLoop` is: every step consumes at least one
byte, so `input.length` is always enough. -/
def run (cfg : Config) : Nat → List Nat → List Nat × Bool
  | 0, _ => ([], true)
  | _, [] => ([], true)
  | fuel + 1, b :: rest =>
    if b ≤ 0x7F then emit b (run cfg fuel rest)
    else if 0xC2 ≤ b && b ≤ 0xDF then
      match rest with
      | [] => truncated cfg 1
      | c :: tail =>
        if inBounds 0x80 0xBF c then
          emit ((b - 0xC0) * 0x40 + (c - 0x80)) (run cfg fuel tail)
        else if cfg.restoreByte then emitError (run cfg fuel (c :: tail))
        else emitError (run cfg fuel tail)
    else if 0xE0 ≤ b && b ≤ 0xEF then
      match rest with
      | [] => truncated cfg 2
      | c :: tail =>
        if inBounds (lowerFor cfg b) (upperFor cfg b) c then
          match tail with
          | [] => truncated cfg 1
          | d :: tail2 =>
            if inBounds 0x80 0xBF d then
              emit ((b - 0xE0) * 0x1000 + (c - 0x80) * 0x40 + (d - 0x80)) (run cfg fuel tail2)
            else if cfg.restoreByte then emitError (run cfg fuel (d :: tail2))
            else emitError (run cfg fuel tail2)
        else if cfg.restoreByte then emitError (run cfg fuel (c :: tail))
        else emitError (run cfg fuel tail)
    else if 0xF0 ≤ b && b ≤ 0xF4 then
      match rest with
      | [] => truncated cfg 3
      | c :: tail =>
        if inBounds (lowerFor cfg b) (upperFor cfg b) c then
          match tail with
          | [] => truncated cfg 2
          | d :: tail2 =>
            if inBounds 0x80 0xBF d then
              match tail2 with
              | [] => truncated cfg 1
              | e :: tail3 =>
                if inBounds 0x80 0xBF e then
                  emit ((b - 0xF0) * 0x40000 + (c - 0x80) * 0x1000 + (d - 0x80) * 0x40 +
                    (e - 0x80)) (run cfg fuel tail3)
                else if cfg.restoreByte then emitError (run cfg fuel (e :: tail3))
                else emitError (run cfg fuel tail3)
            else if cfg.restoreByte then emitError (run cfg fuel (d :: tail2))
            else emitError (run cfg fuel tail2)
        else if cfg.restoreByte then emitError (run cfg fuel (c :: tail))
        else emitError (run cfg fuel tail)
    else if cfg.errorOnStrayByte then emitError (run cfg fuel rest)
    else run cfg fuel rest

/-- `op.utf-8-decode-without-bom` [45763,46180) in "replacement" mode. -/
def decodeWithoutBom (cfg : Config) (input : List Nat) : List Nat :=
  (run cfg (input.length + 1) input).1

/-- `op.utf-8-decode-without-bom-or-fail` [46181,46905): "If potentialError is
an error, then return failure." -/
def decodeOrFail (cfg : Config) (input : List Nat) : Option (List Nat) :=
  let r := run cfg (input.length + 1) input
  if r.2 then some r.1 else none

/-! ## The encoder, and the byte order mark

`op.utf-8-encoder` [90407,91744) and `op.utf-8-decode` [45059,45762). -/

/-- The byte order mark, "0xEF 0xBB 0xBF". -/
def bom : List Nat := [0xEF, 0xBB, 0xBF]

/-- Steps 2 to 6 of `op.utf-8-encoder` [90407,91744), as a function of the code
point's value. Nothing in the algorithm rejects a surrogate; the rejection is
the *domain*, which is why `INFRA-UTF8-CE-002` attacks the domain. -/
def encodeValue (v : Nat) : List Nat :=
  if v ≤ 0x7F then [v]
  else if v ≤ 0x7FF then [0xC0 + v / 0x40, 0x80 + v % 0x40]
  else if v ≤ 0xFFFF then [0xE0 + v / 0x1000, 0x80 + (v / 0x40) % 0x40, 0x80 + v % 0x40]
  else [0xF0 + v / 0x40000, 0x80 + (v / 0x1000) % 0x40, 0x80 + (v / 0x40) % 0x40,
    0x80 + v % 0x40]

/-- Mutant: an encoder that opens its output with a byte order mark. -/
def encodeValueWithBom (v : Nat) : List Nat := bom ++ encodeValue v

/-- Steps 1 and 2 of `op.utf-8-decode` [45059,45762): peek three bytes, and if
they are the mark, read three bytes. Once. -/
def stripBomOnce (input : List Nat) : List Nat :=
  if input.take 3 == bom then input.drop 3 else input

/-- Mutant: the mark is stripped to a fixed point. -/
def stripBomAll : Nat → List Nat → List Nat
  | 0, input => input
  | fuel + 1, input => if input.take 3 == bom then stripBomAll fuel (input.drop 3) else input

/-- Mutant: the mark is never stripped, which is what the literal 1-based
reading of `op.io-queue-peek` [7651,8447) produces (INFRA-R15). -/
def stripBomNever (input : List Nat) : List Nat := input

/-! ## The I/O queue

`op.io-queue-read` [6610,7078) and `op.io-queue-push` [8448,9041). `none` is
`end-of-queue`. -/

/-- Step 2, "If ioQueue[0] is end-of-queue, then return end-of-queue", with step
3's removal not reached. -/
def readSpec : List (Option Nat) → Option (Option Nat × List (Option Nat))
  | [] => none
  | none :: rest => some (none, none :: rest)
  | some a :: rest => some (some a, rest)

/-- Mutant: `read` is a pop, so the terminator is consumed. -/
def readPop : List (Option Nat) → Option (Option Nat × List (Option Nat))
  | [] => none
  | item :: rest => some (item, rest)

/-- Step 1.2, "insert item before the last item in ioQueue", and step 2,
"Otherwise, append item to ioQueue". -/
def pushSpec (queue : List (Option Nat)) (item : Option Nat) : List (Option Nat) :=
  match queue.getLast? with
  | some none => match item with
    | none => queue
    | some _ => queue.dropLast ++ [item, none]
  | _ => queue ++ [item]

/-- Mutant: `push` always appends. -/
def pushAppend (queue : List (Option Nat)) (item : Option Nat) : List (Option Nat) :=
  queue ++ [item]

/-! ## The mutant configurations -/

/-- `INFRA-UTF8-CE-001`: the 0xE0 lower boundary is left at 0x80. -/
def noE0Lower : Config := { spec with e0Lower := 0x80 }

/-- `INFRA-UTF8-CE-003`: the 0xE0 lower boundary is 0x9F, one below 0xA0. -/
def e0OffByOne : Config := { spec with e0Lower := 0x9F }

/-- `INFRA-UTF8-CE-004`: the 0xED upper boundary is 0xA0, one above 0x9F. -/
def edOffByOne : Config := { spec with edUpper := 0xA0 }

/-- `INFRA-UTF8-CE-005`: the 0xF0 lower boundary is 0x8F, one below 0x90. -/
def f0OffByOne : Config := { spec with f0Lower := 0x8F }

/-- `INFRA-UTF8-CE-006`: the 0xF4 upper boundary is 0x90, one above 0x8F. -/
def f4OffByOne : Config := { spec with f4Upper := 0x90 }

/-- `INFRA-UTF8-CE-012`: one error per byte still needed at end of input. -/
def truncPerByte : Config := { spec with truncPerMissingByte := true }

/-- `INFRA-UTF8-CE-013`: the offending byte is consumed instead of restored. -/
def noRestore : Config := { spec with restoreByte := false }

/-- `INFRA-UTF8-CE-018`: a stray byte is skipped instead of substituted. -/
def silentStray : Config := { spec with errorOnStrayByte := false }

/-! ## The witnesses -/

/-- `INFRA-UTF8-CE-001` — an overlong three-byte form is accepted as U+0000.
The 0xE0 lower boundary of 0xA0 is the only thing that rejects it. -/
theorem ce001_overlong_accepted :
    decodeWithoutBom spec [0xE0, 0x80, 0x80] = [fffd, fffd, fffd] ∧
      decodeWithoutBom noE0Lower [0xE0, 0x80, 0x80] = [0x0] := by
  decide

/-- `INFRA-UTF8-CE-002` — a surrogate code point has a UTF-8 encoding under the
algorithm and no round trip: the encoder's domain, and not a step of the
algorithm, is what excludes it. `Whatwg.Infra.Utf8.encodeScalar` therefore takes
a `ScalarValue` and not a `CodePoint`. -/
theorem ce002_surrogate_encoded :
    encodeValue 0xD800 = [0xED, 0xA0, 0x80] ∧
      decodeWithoutBom spec (encodeValue 0xD800) = [fffd, fffd, fffd] := by
  decide

/-- `INFRA-UTF8-CE-003` — the 0xE0 second-byte lower boundary off by one accepts
the overlong encoding of U+07FF. -/
theorem ce003_e0_off_by_one :
    decodeWithoutBom spec [0xE0, 0x9F, 0xBF] = [fffd, fffd, fffd] ∧
      decodeWithoutBom e0OffByOne [0xE0, 0x9F, 0xBF] = [0x7FF] := by
  decide

/-- `INFRA-UTF8-CE-004` — the 0xED second-byte upper boundary off by one accepts
the leading surrogate U+D800, which the decoder must never emit. -/
theorem ce004_ed_off_by_one :
    decodeWithoutBom spec [0xED, 0xA0, 0x80] = [fffd, fffd, fffd] ∧
      decodeWithoutBom edOffByOne [0xED, 0xA0, 0x80] = [0xD800] := by
  decide

/-- `INFRA-UTF8-CE-005` — the 0xF0 second-byte lower boundary off by one accepts
the overlong four-byte encoding of U+FFFF. -/
theorem ce005_f0_off_by_one :
    decodeWithoutBom spec [0xF0, 0x8F, 0xBF, 0xBF] = [fffd, fffd, fffd, fffd] ∧
      decodeWithoutBom f0OffByOne [0xF0, 0x8F, 0xBF, 0xBF] = [0xFFFF] := by
  decide

/-- `INFRA-UTF8-CE-006` — the 0xF4 second-byte upper boundary off by one accepts
U+110000, which is not a code point at all. -/
theorem ce006_f4_off_by_one :
    decodeWithoutBom spec [0xF4, 0x90, 0x80, 0x80] = [fffd, fffd, fffd, fffd] ∧
      decodeWithoutBom f4OffByOne [0xF4, 0x90, 0x80, 0x80] = [0x110000] := by
  decide

/-- The boundaries are inclusive on the accepting side: U+D7FF and U+10FFFF
decode, so a mutant that tightens them is caught too. -/
theorem ce003_006_boundaries_are_inclusive :
    decodeWithoutBom spec [0xED, 0x9F, 0xBF] = [0xD7FF] ∧
      decodeWithoutBom spec [0xF4, 0x8F, 0xBF, 0xBF] = [0x10FFFF] ∧
        decodeWithoutBom spec [0xE0, 0xA0, 0x80] = [0x800] ∧
          decodeWithoutBom spec [0xF0, 0x90, 0x80, 0x80] = [0x10000] := by
  decide

/-- `INFRA-UTF8-CE-007` — the mark is stripped to a fixed point, so a document
that begins with two marks loses both. Step 2 of `op.utf-8-decode`
[45059,45762) runs once. -/
theorem ce007_bom_stripped_twice :
    stripBomOnce (bom ++ bom) = bom ∧ stripBomAll 4 (bom ++ bom) = [] ∧
      decodeWithoutBom spec (stripBomOnce (bom ++ bom)) = [0xFEFF] ∧
        decodeWithoutBom spec (stripBomAll 4 (bom ++ bom)) = [] := by
  decide

/-- `INFRA-UTF8-CE-008` — the mark is never stripped. This is what the literal
1-based reading of `op.io-queue-peek` [7651,8447) produces, since `peek 3` then
returns the bytes at indices 1, 2 and 3 and never matches 0xEF 0xBB 0xBF at
index 0 (ruling request INFRA-R15). -/
theorem ce008_bom_never_stripped :
    stripBomOnce bom = [] ∧ stripBomNever bom = bom ∧
      decodeWithoutBom spec (stripBomNever bom) = [0xFEFF] := by
  decide

/-- `INFRA-UTF8-CE-009` — `op.utf-8-decode-without-bom` [45763,46180) has no
step 1 or 2: it must keep the mark. The two hooks differ in exactly this. -/
theorem ce009_without_bom_keeps_the_mark :
    decodeWithoutBom spec bom = [0xFEFF] ∧
      decodeWithoutBom spec (stripBomOnce bom) = [] := by
  decide

/-- `INFRA-UTF8-CE-010` — the fail mode drops the failure and answers with the
replacement-mode output. -/
theorem ce010_fail_mode_returns_some :
    decodeOrFail spec [0xC0, 0x80] = none ∧
      (some (decodeWithoutBom spec [0xC0, 0x80]) : Option (List Nat)) =
        some [fffd, fffd] := by
  decide

/-- `INFRA-UTF8-CE-011` — the fail mode implemented as "decode in replacement
mode, then fail if U+FFFD occurs in the output" rejects a *well-formed* input:
U+FFFD is a scalar value and 0xEF 0xBF 0xBD is its encoding. The observation has
to be the number of substituted errors, not the output's contents. -/
theorem ce011_replacement_input_is_well_formed :
    decodeWithoutBom spec [0xEF, 0xBF, 0xBD] = [fffd] ∧
      decodeOrFail spec [0xEF, 0xBF, 0xBD] = some [fffd] := by
  decide

/-- `INFRA-UTF8-CE-012` — a truncated sequence at end of input emits one error
per byte still needed instead of the single error of step 1 of
`op.utf-8-decoder` [86515,90406). -/
theorem ce012_truncated_two_replacements :
    decodeWithoutBom spec [0xE2] = [fffd] ∧
      decodeWithoutBom truncPerByte [0xE2] = [fffd, fffd] ∧
        decodeWithoutBom spec [0xF0, 0x9F] = [fffd] ∧
          decodeWithoutBom truncPerByte [0xF0, 0x9F] = [fffd, fffd] := by
  decide

/-- `INFRA-UTF8-CE-013` — step 4.2's "Restore byte to ioQueue" is skipped, so a
truncated sequence eats the byte that follows it. Here the ASCII `A` is lost. -/
theorem ce013_offending_byte_restored :
    decodeWithoutBom spec [0xE2, 0x82, 0x41] = [fffd, 0x41] ∧
      decodeWithoutBom noRestore [0xE2, 0x82, 0x41] = [fffd] := by
  decide

/-- `INFRA-UTF8-CE-014` — the encoder prefixes a byte order mark. Under
`op.utf-8-decode` [45059,45762) the mark is stripped again and the round trip
still holds, so only a statement about the encoder's own output catches it;
under `op.utf-8-decode-without-bom` [45763,46180) it is visible. -/
theorem ce014_encoder_emits_bom :
    encodeValue 0x41 = [0x41] ∧ encodeValueWithBom 0x41 = [0xEF, 0xBB, 0xBF, 0x41] ∧
      decodeWithoutBom spec (stripBomOnce (encodeValueWithBom 0x41)) = [0x41] ∧
        decodeWithoutBom spec (encodeValueWithBom 0x41) = [0xFEFF, 0x41] := by
  decide

/-! ### The stateful legacy encoder

`rule.iso-2022-jp-encoder-stateful` [123264,124113): "Encoding U+00A5 (¥) gives
0x1B 0x28 0x4A 0x5C 0x1B 0x28 0x42. Doing that twice, concatenating the results,
and then decoding yields U+00A5 U+FFFD U+00A5." No ISO-2022-JP decoder is
modelled here and none is admitted by this packet; the witness is only that the
retained-instance answer and the concatenation of two restarted answers are
different byte sequences, which is why
`Whatwg.Infra.Encoding.Encoder.foreign` advances its tape. -/

/-- The pin's own answer for one U+00A5 from a fresh encoder. -/
def yenFromFreshEncoder : List Nat := [0x1B, 0x28, 0x4A, 0x5C, 0x1B, 0x28, 0x42]

/-- The answer a *retained* encoder gives for two U+00A5 in one run: the shift
sequences bracket the run, not each code point. -/
def yenTwiceFromRetainedEncoder : List Nat := [0x1B, 0x28, 0x4A, 0x5C, 0x5C, 0x1B, 0x28, 0x42]

/-- `INFRA-UTF8-CE-015` — a stateful encoder treated as stateless. Restarting
the instance per code point is not the same byte sequence as retaining it, so
`op.encode-or-fail` [51167,53203)'s "the caller will have to keep an encoder
instance alive" is a real requirement and not advice. -/
theorem ce015_stateful_encoder_is_not_restartable :
    yenFromFreshEncoder ++ yenFromFreshEncoder ≠ yenTwiceFromRetainedEncoder := by
  decide

/-- `INFRA-UTF8-CE-016` — `read` removes the terminator, so the second read of
an immediate queue blocks instead of answering `end-of-queue`. Step 2 of
`op.io-queue-read` [6610,7078) returns before step 3's removal. -/
theorem ce016_read_keeps_end_of_queue :
    readSpec [none] = some (none, [none]) ∧ readPop [none] = some (none, []) ∧
      (readSpec [none]).map (fun r => readSpec r.2) = some (some (none, [none])) ∧
        (readPop [none]).map (fun r => readPop r.2) = some none := by
  decide

/-- `INFRA-UTF8-CE-017` — `push` appends after the terminator, so
`end-of-queue` is no longer the last item and every later reader stops early.
Step 1.2 of `op.io-queue-push` [8448,9041) inserts before it. -/
theorem ce017_push_before_end_of_queue :
    pushSpec [some 0x41, none] (some 0x42) = [some 0x41, some 0x42, none] ∧
      pushAppend [some 0x41, none] (some 0x42) = [some 0x41, none, some 0x42] := by
  decide

/-- `INFRA-UTF8-CE-018` — an unexpected continuation byte is skipped silently
instead of substituted. The "Otherwise" row of step 3 of `op.utf-8-decoder`
[86515,90406) returns error for every byte from 0x80 to 0xC1 and from 0xF5
up. -/
theorem ce018_stray_byte_is_an_error :
    decodeWithoutBom spec [0x80] = [fffd] ∧ decodeWithoutBom silentStray [0x80] = [] ∧
      decodeWithoutBom spec [0xC0] = [fffd] ∧ decodeWithoutBom spec [0xF5] = [fffd] ∧
        decodeWithoutBom spec [0xFF] = [fffd] := by
  decide

/-! ### The transcription itself, on the pin's own bytes

Not a mutant: the four-length shape and the pin's 💩 example
(`example.io-queue-restore` [9727,9981)), kept beside the mutants so a reader can
see that `spec` is the algorithm and not one more variant. -/

theorem spec_round_trips_the_pin_example :
    encodeValue 0x1F4A9 = [0xF0, 0x9F, 0x92, 0xA9] ∧
      decodeWithoutBom spec [0xF0, 0x9F, 0x92, 0xA9] = [0x1F4A9] := by
  decide

theorem spec_four_length_shape :
    (encodeValue 0x41).length = 1 ∧ (encodeValue 0xE9).length = 2 ∧
      (encodeValue 0x20AC).length = 3 ∧ (encodeValue 0x10FFFF).length = 4 := by
  decide

end WhatwgTest.Infra.Counterexamples.Utf8.Breaker
