import Whatwg.Infra.Bytes.Sequence
import Whatwg.Infra.Text.Codec

/-!
# Text.Utf8

Owner: the UTF-8 codec of the WHATWG Encoding Standard — the I/O queue of
section `terminology`, the encoder/decoder vocabulary of section `encodings`,
the four hooks for standards of section `specification-hooks`, and the UTF-8
encoder and decoder of section `the-encoding`.

Authority pin: `whatwg/encoding` commit
`67494fceee1b95bbc87b58142fcc14e48310f257` (2025-06-16, "Review Draft
Publication: June 2025"), source `encoding.bs`, sealed under
`vendor/whatwg-encoding-67494fce/` by `generated/vendor-manifest.tsv`, SHA-256
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`, 144,545
bytes. `SPEC-MANIFEST.md` owns the pin and `docs/PROVENANCE.md` its fetch
record. Ruling R-U1 opened the packet; ruling INFRA-R14 put it in this module
rather than in `Whatwg.Infra.Text.Codec`, whose pin is `infra.bs`, so that one
module names one authority.

The Encoding Standard has **no census** in this repository, so every
declaration is anchored by a `[byte-start,byte-end)` span into those sealed
bytes together with the span's SHA-256. Each docstring below names its span;
the digest of every span is in this table, recomputed from the sealed bytes.
No line number is cited anywhere.

| Alias | Algorithm or definition | Span | Span SHA-256 |
| --- | --- | --- | --- |
| QUEUE | I/O queue, end-of-queue | [5298,6609) | `9cd0d416170082e8e8107fc0fdff3197d83836c6c33fb4b80d91324d008fabab` |
| READ | I/O queue / read | [6610,7078) | `480e7b46cee256258dea5e42a8795381fde9801ad39bf6c1d429514e671dafb3` |
| READN | I/O queue / read items | [7079,7650) | `7125981956fad8e645ab082eb3c9463ac2767a554c8adda2450b4da734d1cf89` |
| PEEK | I/O queue / peek | [7651,8447) | `96d14ab43ad476c0c1c6c48076acc394bef0cb8b529583490c828fb63171af66` |
| PUSH | I/O queue / push | [8448,9041) | `687c17a075ee9486c29d19bdd588a0a5b718dec6c3f44a10e0440da186eb6d6c` |
| PUSHN | I/O queue / push items | [9042,9270) | `8a88caf9ab139753f6408fc4d8d3a01e3a5fdc093dd9350d669a4f6d9dd2debc` |
| RESTORE | I/O queue / restore | [9271,9726) | `cdacf56b375040d309d17eb17ec57aaf29961d6dbff6994e1f3480c2784b0a45` |
| EXRESTORE | the restore example | [9727,9981) | `79064942cb2aa294367a8b7cc7882ddd0b21829e786de9bf99d3d2ee5bd20f3d` |
| FROMQ | from I/O queue / convert | [9982,10285) | `3674840845a16126bd8c21d29e9d5b9b39ced74a6004734153383eceb0f7207f` |
| TOQ | to I/O queue / convert | [10286,10769) | `704fc709a7ea639bd6dde388ff31ae3143197bebeb79c3becd0d676decc5d81c` |
| VOCAB | decoder, encoder, handler, error mode | [13366,14779) | `6d90a844904e4911440a470b8c970dbf1097b0c28d542cf90698b53dc8d01a4f` |
| PROCQ | process a queue | [14785,15508) | `4025bb2135b3f424b62c265a3e07bb0d96ae341501f758055192c71cda843ce3` |
| PROCI | process an item | [15509,17620) | `7131bccacd9c20cbfa60a7ca5796205787ecc0c1a79d60e28eeec3ae14d08851` |
| HOOKS | the note that names the four hooks | [43782,45058) | `276ce2d78f278df9a100ad254f482e9791a66aeee74aec41c4bc2923202952a7` |
| DECODE | UTF-8 decode | [45059,45762) | `4143e0ffb36daea30b24fd3e90a574a0a4e2025a7367eea4cca34aac82f9e9f4` |
| NOBOM | UTF-8 decode without BOM | [45763,46180) | `278a469c693ad299446bdef8ee49c069c3e6271788f7a81863e5d9a322164c9c` |
| ORFAIL | UTF-8 decode without BOM or fail | [46181,46905) | `7d53beab92ccd1bb6bef68728c1a9ea7a08ed68b1af0b29f3abf33b5ed5ec426` |
| ENCODE | UTF-8 encode | [46912,47215) | `47e428dc21403bb3b23e06ff2d32153dec5c990b1bfca3757b62acdad417711b` |
| LEGACY | encode (the legacy hook) | [50170,50822) | `ab4e914ee0fbbb0cda597f539213de437eb26aa72eb9e15aa7b85e7f587d46d5` |
| GETENC | get an encoder | [50829,51166) | `8bf32b8213a61a1080768d4cafea2da6f5d413d9f60d5d88113c0a6a430c79aa` |
| ORFAILENC | encode or fail | [51167,53203) | `6bdff2bb587e37dd433c7823934f880626979ea67e28d007528e252927a891c4` |
| DECODER | UTF-8 decoder | [86515,90406) | `7a2f860a829aae4a0917bff78cbf4a35794f9e6edd9a77945d47300032cd3b72` |
| ENCODER | UTF-8 encoder | [90407,91744) | `24b9d002af18c590a3ac2166e738709d674c61fac1056a8d48a93ebc2542ce41` |
| ISO2022 | ISO-2022-JP encoder statefulness | [123264,124113) | `2e8280c2ce62126c984810354cc7f0a12f3d49366c2644370f72a0a9ef78ae50` |

Carrier reuse (`Whatwg/AGENTS.md`): `Byte`, `ByteSequence`, `CodePoint`,
`CodeUnit`, `JsString`, `ScalarValue` and `replacementCharacter` are Infra's and
are consumed, never redeclared. The three carriers added here — `Item`,
`IoQueue` and the encoder profile — are the Encoding Standard's own.

Boundary discipline (DB-02): exactly one encoder algorithm is owned, UTF-8's.
Every other encoding is a first-order profile whose answers are data on
`Encoding.EncoderTape`; an exhausted tape answers `none`, an unanswered decision
and a live frontier, never an error (DB-07).
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-! ## Numeric helpers

Private arithmetic bridges between the pin's bitwise notation and the
`omega`-decidable forms every range argument below is discharged in. They are
implementation helpers, not part of the frozen surface. -/

/-- `x >>> n` is `x / 2 ^ n`, the form `omega` reasons about. -/
private theorem shiftRight_div (x n : Nat) : x >>> n = x / 2 ^ n :=
  Nat.shiftRight_eq_div_pow x n

/-- `(x <<< 6) ||| y` is `x * 64 + y` when `y` fits in six bits: the two
operands are bit-disjoint. -/
private theorem lor_shift_six (x y : Nat) (hy : y < 64) : (x <<< 6) ||| y = x * 64 + y := by
  have h6 : y < 2 ^ 6 := Nat.lt_of_lt_of_le hy (by decide)
  have hpow : (2 : Nat) ^ 6 = 64 := by decide
  rw [← Nat.shiftLeft_add_eq_or_of_lt h6 x, Nat.shiftLeft_eq, hpow]

/-- `0x80 ||| y` is `0x80 + y` when `y` fits in six bits: this is step 5.2 of
ENCODER, "Append to bytes 0x80 | (temp & 0x3F)". -/
private theorem lor_continuation (y : Nat) (hy : y < 64) : 0x80 ||| y = 0x80 + y := by
  have h6 : y < 2 ^ 6 := Nat.lt_of_lt_of_le hy (by decide)
  have hshift : (2 : Nat) <<< 6 = 0x80 := by decide
  rw [← hshift]
  exact (Nat.shiftLeft_add_eq_or_of_lt h6 2).symm

/-- `x &&& 0x3F` is `x % 64`, "the six least significant bits". -/
private theorem land_six (x : Nat) : x &&& 0x3F = x % 64 := by
  have h : (0x3F : Nat) = 2 ^ 6 - 1 := by decide
  have hpow : (2 : Nat) ^ 6 = 64 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, hpow]

/-- `x &&& 0x1F` is `x % 32`, "the five least significant bits" of DECODER's
0xC2-to-0xDF row. -/
private theorem land_five (x : Nat) : x &&& 0x1F = x % 32 := by
  have h : (0x1F : Nat) = 2 ^ 5 - 1 := by decide
  have hpow : (2 : Nat) ^ 5 = 32 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, hpow]

/-- `x &&& 0xF` is `x % 16`, "the four least significant bits" of DECODER's
0xE0-to-0xEF row. -/
private theorem land_four (x : Nat) : x &&& 0xF = x % 16 := by
  have h : (0xF : Nat) = 2 ^ 4 - 1 := by decide
  have hpow : (2 : Nat) ^ 4 = 16 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, hpow]

/-- `x &&& 0x7` is `x % 8`, "the three least significant bits" of DECODER's
0xF0-to-0xF4 row. -/
private theorem land_three (x : Nat) : x &&& 0x7 = x % 8 := by
  have h : (0x7 : Nat) = 2 ^ 3 - 1 := by decide
  have hpow : (2 : Nat) ^ 3 = 8 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod, hpow]

/-- A byte's number is what `UInt8.ofNat` was given, below 0x100. -/
private theorem toNat_ofNat_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n :=
  UInt8.toNat_ofNat_of_lt' h

/-- `CodePoint.isScalarValue` is `ScalarValue`'s membership condition: "a code
point that is not a surrogate". -/
private theorem isSurrogate_of_isScalarValue {c : CodePoint}
    (h : CodePoint.isScalarValue c = true) : CodePoint.isSurrogate c = false := by
  rw [CodePoint.isScalarValue] at h
  cases hc : CodePoint.isSurrogate c with
  | false => rfl
  | true => rw [hc] at h; exact absurd h (by decide)

/-! ## The I/O queue

Section `terminology`. QUEUE: "An I/O queue is a type of list with items of a
particular type (i.e., bytes or scalar values). End-of-queue is a special item
that can be present in I/O queues of any type and it signifies that there are
no more items in the queue." The terminator is an item *of the same list*, so
the carrier is `List (Item α)` and not `List α` beside a flag. -/

/-- An item of an I/O queue, QUEUE [5298,6609): a value of the queue's type, or
the special `end-of-queue` item. -/
inductive Item (α : Type) where
  /-- An ordinary item of the queue's own type. -/
  | value : α → Item α
  /-- QUEUE's "end-of-queue … a special item that can be present in I/O queues
  of any type". -/
  | endOfQueue : Item α

/-- An I/O queue, QUEUE [5298,6609): "a type of list with items of a particular
type". -/
abbrev IoQueue (α : Type) : Type := List (Item α)

namespace IoQueue

/-- READ [6610,7078). Step 1, "If ioQueue is empty, then wait until its size is
at least 1", is an unanswered decision: `none`, a live frontier and never an
error. Step 2, "If ioQueue[0] is end-of-queue, then return end-of-queue",
returns *before* step 3's removal, so the terminator stays in the queue and an
immediate queue answers `end-of-queue` forever. Step 3, "Remove ioQueue[0] and
return it". -/
def read {α : Type} : IoQueue α → Option (Item α × IoQueue α)
  | [] => none
  | Item.endOfQueue :: rest => some (Item.endOfQueue, Item.endOfQueue :: rest)
  | Item.value a :: rest => some (Item.value a, rest)

/-- READN [7079,7650): "Let readItems be « ». Perform the following step number
times: Append to readItems the result of reading an item from ioQueue. Remove
end-of-queue from readItems. Return readItems." A read that waits makes the
whole operation wait, which is `none`. -/
def readItems {α : Type} (ioQueue : IoQueue α) : Nat → Option (List α × IoQueue α)
  | 0 => some ([], ioQueue)
  | number + 1 =>
    match read ioQueue with
    | none => none
    | some (item, rest) =>
      match readItems rest number with
      | none => none
      | some (readItemsTail, final) =>
        match item with
        | Item.value a => some (a :: readItemsTail, final)
        | Item.endOfQueue => some (readItemsTail, final)

/-- The scan of PEEK [7651,8447) step 3, "For each n in the range … : If
ioQueue[n] is end-of-queue, break. Otherwise, append ioQueue[n] to prefix",
from the index `start`, with one unit of fuel per index the range names. -/
private def peekLoop {α : Type} (ioQueue : IoQueue α) (start : Nat) : Nat → List α
  | 0 => []
  | fuel + 1 =>
    match ioQueue[start]? with
    | none => []
    | some Item.endOfQueue => []
    | some (Item.value a) => a :: peekLoop ioQueue (start + 1) fuel

/-- The structural companion of `peekLoop`, recursing on the fuel first so that
the zero case reduces without inspecting the queue. -/
private def peekTake {α : Type} : Nat → IoQueue α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, Item.endOfQueue :: _ => []
  | number + 1, Item.value a :: rest => a :: peekTake number rest

private theorem peekLoop_eq {α : Type} :
    ∀ (fuel : Nat) (ioQueue : IoQueue α) (start : Nat),
      peekLoop ioQueue start fuel = peekTake fuel (ioQueue.drop start)
  | 0, _, _ => rfl
  | fuel + 1, ioQueue, start => by
    rw [peekLoop]
    cases hq : ioQueue[start]? with
    | none =>
      have hnil : ioQueue.drop start = [] :=
        List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hq)
      rw [hnil]
      rfl
    | some item =>
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hq
      have hd : ioQueue.drop start = item :: ioQueue.drop (start + 1) := by
        rw [List.drop_eq_getElem_cons hlt, hget]
      rw [hd]
      cases item with
      | endOfQueue => rfl
      | value a => rw [peekTake, peekLoop_eq fuel ioQueue (start + 1)]

/-- PEEK [7651,8447), transcribed literally. Step 3 reads "For each n in the
range 1 to number, inclusive: If ioQueue[n] is end-of-queue, break. Otherwise,
append ioQueue[n] to prefix"; Infra's indexing syntax is zero-based
(`vendor/whatwg-infra-3f984adc/infra.bs` [67159,67540)) and Infra's range
[82259,82581) is the set {1,…,number}, so the literal reading skips
`ioQueue[0]`. Ruling request INFRA-R15; `peekPrefix` is the other reading and
`peek_eq_peekPrefix_tail` states exactly how they differ. -/
def peek {α : Type} (ioQueue : IoQueue α) (number : Nat) : List α :=
  peekLoop ioQueue 1 number

/-- PEEK [7651,8447) read zero-based, `ioQueue[0]` through
`ioQueue[number − 1]`. This is the reading DECODE [45059,45762) step 2 needs for
its byte-order-mark test to be one, and the reading INFRA-R15 asks the operator
to ratify. -/
def peekPrefix {α : Type} (ioQueue : IoQueue α) (number : Nat) : List α :=
  peekLoop ioQueue 0 number

/-- PUSH [8448,9041) step 1's test, "If the last item in ioQueue is
end-of-queue". -/
private def lastIsEndOfQueue {α : Type} (ioQueue : IoQueue α) : Bool :=
  match ioQueue.getLast? with
  | some Item.endOfQueue => true
  | _ => false

private theorem lastIsEndOfQueue_eq_false {α : Type} {q : IoQueue α}
    (h : q.getLast? ≠ some Item.endOfQueue) : lastIsEndOfQueue q = false := by
  rw [lastIsEndOfQueue]
  match hq : q.getLast? with
  | none => rfl
  | some (Item.value _) => rfl
  | some Item.endOfQueue => exact absurd hq h

private theorem lastIsEndOfQueue_concat {α : Type} (q : IoQueue α) :
    lastIsEndOfQueue (q ++ [Item.endOfQueue]) = true := by
  rw [lastIsEndOfQueue]
  have hlast : (q ++ [Item.endOfQueue]).getLast? = some (Item.endOfQueue : Item α) := by
    simp
  rw [hlast]

/-- PUSH [8448,9041): "If the last item in ioQueue is end-of-queue: If item is
end-of-queue, do nothing. Otherwise, insert item before the last item in
ioQueue. Otherwise, append item to ioQueue." A queue therefore never carries two
terminators. -/
def push {α : Type} (ioQueue : IoQueue α) (item : Item α) : IoQueue α :=
  if lastIsEndOfQueue ioQueue then
    match item with
    | Item.endOfQueue => ioQueue
    | Item.value a =>
      ioQueue.take (ioQueue.length - 1) ++ [Item.value a, Item.endOfQueue]
  else ioQueue ++ [item]

/-- PUSHN [9042,9270): "push each item in the sequence to ioQueue, in the given
order". -/
def pushItems {α : Type} (ioQueue : IoQueue α) (items : List (Item α)) : IoQueue α :=
  items.foldl push ioQueue

/-- RESTORE [9271,9726): "To restore an item other than end-of-queue to an I/O
queue, perform the list prepend operation." The restriction "other than
end-of-queue" is carried by the argument type and discharged by typing
(INFRA-R3). -/
def restore {α : Type} (ioQueue : IoQueue α) (a : α) : IoQueue α :=
  Item.value a :: ioQueue

/-- RESTORE [9271,9726), second sentence: "To restore a list of items excluding
end-of-queue to an I/O queue, insert those items, in the given order, before the
first item in the queue." -/
def restoreItems {α : Type} (ioQueue : IoQueue α) (items : List α) : IoQueue α :=
  items.map Item.value ++ ioQueue

/-- FROMQ [9982,10285): "return the result of reading an indefinite number of
items from ioQueue". Reading stops at the terminator, which READ leaves in
place. -/
def convertFrom {α : Type} : IoQueue α → List α
  | [] => []
  | Item.endOfQueue :: _ => []
  | Item.value a :: rest => a :: convertFrom rest

/-- TOQ [10286,10769): "Return an I/O queue containing the items in input, in
order, followed by end-of-queue." Step 1's assertion, "input is not a list or it
does not contain end-of-queue", is discharged by typing: the argument is a
`List α`, not a `List (Item α)`. -/
def convertTo {α : Type} (input : List α) : IoQueue α :=
  input.map Item.value ++ [Item.endOfQueue]

/-- Whether the queue carries the terminator, the note of QUEUE [5298,6609):
"Immediate queues have end-of-queue as their last item, whereas streaming queues
need not have it." -/
def containsEndOfQueue {α : Type} (ioQueue : IoQueue α) : Bool :=
  ioQueue.any fun item =>
    match item with
    | Item.endOfQueue => true
    | Item.value _ => false

/-! ### The queue's laws -/

/-- READ [6610,7078) step 1 on the empty queue: unanswered, a live frontier. -/
theorem read_nil {α : Type} : read ([] : IoQueue α) = none := rfl

/-- READ [6610,7078) step 2: the terminator is returned and left in place. -/
theorem read_endOfQueue {α : Type} (rest : IoQueue α) :
    read (Item.endOfQueue :: rest) = some (Item.endOfQueue, Item.endOfQueue :: rest) := rfl

/-- READ [6610,7078) step 3: "Remove ioQueue[0] and return it." -/
theorem read_value {α : Type} (a : α) (rest : IoQueue α) :
    read (Item.value a :: rest) = some (Item.value a, rest) := rfl

/-- READN [7079,7650) on an immediate queue read to or past its end: the values
before the terminator, with the terminator still in the queue. -/
theorem readItems_endOfQueue {α : Type} :
    ∀ (l : List α) (n : Nat), l.length ≤ n →
      readItems (l.map Item.value ++ [Item.endOfQueue]) n = some (l, [Item.endOfQueue])
  | [], 0, _ => rfl
  | [], n + 1, _ => by
      have ih := readItems_endOfQueue ([] : List α) n (Nat.zero_le _)
      rw [List.map_nil, List.nil_append] at ih ⊢
      simp only [readItems, read_endOfQueue, ih]
  | a :: t, 0, h => absurd h (by simp)
  | a :: t, n + 1, h => by
      have ht : t.length ≤ n := by
        rw [List.length_cons] at h; omega
      simp only [List.map_cons, List.cons_append, readItems, read_value,
        readItems_endOfQueue t n ht]

/-- PUSH [8448,9041) step 2: "Otherwise, append item to ioQueue." -/
theorem push_append {α : Type} (q : IoQueue α) (item : Item α)
    (h : q.getLast? ≠ some Item.endOfQueue) : push q item = q ++ [item] := by
  simp [push, lastIsEndOfQueue_eq_false h]

/-- PUSH [8448,9041) step 1.2: "Otherwise, insert item before the last item in
ioQueue." -/
theorem push_before_endOfQueue {α : Type} (q : IoQueue α) (a : α) :
    push (q ++ [Item.endOfQueue]) (Item.value a) =
      q ++ [Item.value a, Item.endOfQueue] := by
  simp only [push, lastIsEndOfQueue_concat, if_true]
  have hlen : (q ++ [Item.endOfQueue]).length - 1 = q.length := by simp
  simp only [hlen]
  simp

/-- PUSH [8448,9041) step 1.1: "If item is end-of-queue, do nothing." -/
theorem push_endOfQueue_idem {α : Type} (q : IoQueue α) :
    push (q ++ [Item.endOfQueue]) Item.endOfQueue = q ++ [Item.endOfQueue] := by
  simp only [push, lastIsEndOfQueue_concat, if_true]

/-- RESTORE [9271,9726): "perform the list prepend operation". -/
theorem restore_eq {α : Type} (q : IoQueue α) (a : α) :
    restore q a = Item.value a :: q := rfl

/-- RESTORE [9271,9726), second sentence. -/
theorem restoreItems_eq {α : Type} (q : IoQueue α) (l : List α) :
    restoreItems q l = l.map Item.value ++ q := rfl

/-- EXRESTORE [9727,9981), the pin's own example: "Inserting the bytes
« 0xF0, 0x9F » in an I/O queue « 0x92 0xA9, end-of-queue », results in an I/O
queue « 0xF0, 0x9F, 0x92 0xA9, end-of-queue »." The four bytes are U+1F4A9's
UTF-8 encoding. -/
theorem restoreItems_example :
    restoreItems
        [Item.value (0x92 : Byte), Item.value (0xA9 : Byte), Item.endOfQueue]
        [(0xF0 : Byte), (0x9F : Byte)] =
      [Item.value (0xF0 : Byte), Item.value (0x9F : Byte), Item.value (0x92 : Byte),
        Item.value (0xA9 : Byte), Item.endOfQueue] := rfl

/-- TOQ [10286,10769) step 2. -/
theorem convertTo_eq {α : Type} (l : List α) :
    convertTo l = l.map Item.value ++ [Item.endOfQueue] := rfl

/-- FROMQ after TOQ is the identity: RS-1's codec round trip at the container
level. -/
theorem convertFrom_convertTo {α : Type} (l : List α) : convertFrom (convertTo l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [convertTo, List.map_cons, List.cons_append, convertFrom] at *
                   rw [ih]

/-- Every converted queue is an immediate queue. -/
theorem containsEndOfQueue_convertTo {α : Type} (l : List α) :
    containsEndOfQueue (convertTo l) = true := by
  unfold containsEndOfQueue convertTo
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, List.cons_append, List.any_cons, ih, Bool.or_true]

private theorem peekTake_convertTo {α : Type} :
    ∀ (n : Nat) (l : List α), peekTake n (convertTo l) = l.take n
  | 0, l => by cases l <;> rfl
  | n + 1, [] => rfl
  | n + 1, a :: t => by
    rw [convertTo, List.map_cons, List.cons_append, peekTake, List.take_succ_cons]
    have ih := peekTake_convertTo n t
    rw [convertTo] at ih
    rw [ih]

/-- PEEK [7651,8447) read zero-based on an immediate queue: the first `number`
values, cut at the terminator. -/
theorem peekPrefix_convertTo {α : Type} (l : List α) (n : Nat) :
    peekPrefix (convertTo l) n = l.take n := by
  rw [peekPrefix, peekLoop_eq, List.drop_zero, peekTake_convertTo]


/-- **INFRA-R15, stated as a theorem.** The literal transcription of PEEK
[7651,8447) is the zero-based peek of the queue with its first item dropped, so
the two readings disagree on every nonempty queue. -/
theorem peek_eq_peekPrefix_tail {α : Type} (q : IoQueue α) (n : Nat) :
    peek q n = peekPrefix (q.drop 1) n := by
  rw [peek, peekPrefix, peekLoop_eq, peekLoop_eq, List.drop_zero]

/-- The discriminating witness for INFRA-R15: under the literal reading the byte
order mark is not the first three bytes, so DECODE [45059,45762) would never
strip one. -/
theorem peek_bom_example :
    peek (convertTo [(0xEF : Byte), 0xBB, 0xBF]) 3 = [(0xBB : Byte), 0xBF] := rfl

end IoQueue

/-! ## Encoders, decoders and their handler results

Section `encodings`. VOCAB [13366,14779): "Instances of decoders and encoders
have a handler algorithm and might also have state. A handler algorithm takes an
input I/O queue and an item, and returns finished, one or more items, error
optionally with a code point, or continue." -/

namespace Encoding

/-- The four answers of a handler, VOCAB [13366,14779). -/
inductive HandlerResult (α : Type) where
  /-- VOCAB's `finished`. -/
  | finished : HandlerResult α
  /-- VOCAB's "one or more items". The nonemptiness is the text's wording and is
  carried by the laws, not by the carrier: PROCI [15509,17620) step 6 pushes the
  whole list and never inspects its length. -/
  | items : List α → HandlerResult α
  /-- VOCAB's "error optionally with a code point". The code point is read only
  by PROCI's "html" arm and by ORFAILENC [51167,53203) step 3; UTF-8's decoder
  never supplies one. -/
  | error : Option CodePoint → HandlerResult α
  /-- VOCAB's `continue`, spelled `continues` because `continue` is a Lean
  keyword. -/
  | continues : HandlerResult α

/-- VOCAB [13366,14779): "An error mode as used below is `replacement` or
`fatal` for a decoder". The encoder's `fatal`/`html` pair is not declared:
`html` is reachable only through LEGACY [50170,50822), which this packet does
not own, and ORFAILENC [51167,53203) fixes `fatal`. -/
inductive DecoderErrorMode where
  /-- PROCI [15509,17620) step 7's "replacement" arm. -/
  | replacement : DecoderErrorMode
  /-- PROCI [15509,17620) step 7's "fatal" arm. -/
  | fatal : DecoderErrorMode

/-- An encoding's name, [12179,13365): "Each encoding has a name, and one or
more labels." The three names GETENC [50829,51166) step 1 asserts against are
distinguished so that the assertion is statable, and ISO-2022-JP is
distinguished because it is the one stateful encoder the pin names. -/
inductive Name where
  /-- The one encoding whose encoder this repository owns. -/
  | utf8 : Name
  /-- The `replacement` encoding, which "has no encoder". -/
  | replacement : Name
  /-- The `UTF-16BE` encoding, which "has no encoder". -/
  | utf16be : Name
  /-- The `UTF-16LE` encoding, which "has no encoder". -/
  | utf16le : Name
  /-- ISO-2022-JP, ISO2022 [123264,124113): the one encoder with associated
  state. -/
  | iso2022jp : Name
  /-- Any other encoding, carried by its name [12179,13365). -/
  | other : JsString → Name

namespace Name

/-- GETENC [50829,51166) step 1 as a decidable predicate: "Assert: encoding is
not replacement or UTF-16BE/LE", and the note of VOCAB [13366,14779), "The
replacement and UTF-16BE/LE encodings have no encoder." -/
def hasEncoder : Name → Bool
  | Name.replacement => false
  | Name.utf16be => false
  | Name.utf16le => false
  | _ => true

/-- Whether the encoder instance carries state across `encode or fail` calls.
ISO2022 [123264,124113): "ISO-2022-JP's encoder has an associated ISO-2022-JP
encoder state which is ASCII, Roman, or jis0208, initially ASCII", and "The
ISO-2022-JP encoder is the only encoder for which the concatenation of multiple
outputs can result in an error when run through the corresponding decoder." -/
def isStateful : Name → Bool
  | Name.iso2022jp => true
  | _ => false

/-- Whether this repository owns the encoder algorithm for the name, as opposed
to holding a DB-02 profile for it. Exactly `utf8` today. -/
def isOwned : Name → Bool
  | Name.utf8 => true
  | _ => false

end Name

/-- One answer of ORFAILENC [51167,53203) as its caller consumes it: the bytes
pushed into `output` during the call, and the returned value, "either the number
representing the code point that could not be encoded or null, if there was no
error". -/
structure EncodeAnswer where
  /-- The bytes the call pushed to `output`. -/
  output : ByteSequence
  /-- ORFAILENC step 3 and step 4: "the number representing the code point that
  could not be encoded or null". -/
  potentialError : Option Nat

/-- The run of a retained foreign encoder instance, ORFAILENC [51167,53203):
"When it returns non-null the caller will have to invoke it again, supplying the
same encoder instance and a new output I/O queue." A short or empty tape is an
unanswered decision and therefore a live frontier (DB-07). -/
abbrev EncoderTape : Type := List EncodeAnswer

/-- Whether the tape's last answer is a null `potentialError`, i.e. whether the
caller's "While potentialError is non-null" loop stops on this tape. -/
def EncoderTape.terminated (tape : EncoderTape) : Bool :=
  match tape.getLast? with
  | some answer => answer.potentialError.isNone
  | none => false

/-- The instance GETENC [50829,51166) step 2 returns, "an instance of encoding's
encoder". For UTF-8 it is the owned handler and carries no state; for every
other name it is a DB-02 profile carrying the answers it will give. -/
inductive Encoder where
  /-- The owned UTF-8 encoder instance; ENCODER [90407,91744) has no state. -/
  | utf8 : Encoder
  /-- A foreign encoder profile: its name and the answers it will give. -/
  | foreign : Name → EncoderTape → Encoder

/-- The name of the encoding an instance encodes to. -/
def Encoder.name : Encoder → Name
  | Encoder.utf8 => Name.utf8
  | Encoder.foreign n _ => n

end Encoding

/-! ## The UTF-8 encoder

ENCODER [90407,91744). The handler's first argument is `<var ignore>unused</var>`
in the pin and is therefore not a parameter here. -/

namespace Utf8

/-- ENCODER [90407,91744) step 3's `count`, extended to the ASCII case of step 2
with the value 0, at which step 4's `(codePoint >> (6 × count)) + offset`
reproduces step 2's single byte and step 5's loop is empty. -/
def encoderCount (codePoint : CodePoint) : Nat :=
  if codePoint.val ≤ 0x7F then 0
  else if codePoint.val ≤ 0x7FF then 1
  else if codePoint.val ≤ 0xFFFF then 2
  else 3

/-- ENCODER [90407,91744) step 3's `offset` — "1 and 0xC0", "2 and 0xE0", "3 and
0xF0" — extended to the ASCII case of step 2 with the value 0x00. -/
def encoderOffset (codePoint : CodePoint) : Nat :=
  if codePoint.val ≤ 0x7F then 0x00
  else if codePoint.val ≤ 0x7FF then 0xC0
  else if codePoint.val ≤ 0xFFFF then 0xE0
  else 0xF0

/-- ENCODER [90407,91744) step 5: "While count is greater than 0: Set temp to
codePoint >> (6 × (count − 1)). Append to bytes 0x80 | (temp & 0x3F). Decrease
count by one." The loop is structural in `count`, which the caller supplies as
`encoderCount`, so no fuel appears anywhere in the encoder. -/
def encoderTail (codePoint : Nat) : Nat → ByteSequence
  | 0 => []
  | count + 1 =>
    UInt8.ofNat (0x80 ||| ((codePoint >>> (6 * count)) &&& 0x3F)) :: encoderTail codePoint count

/-- ENCODER [90407,91744) steps 2 to 6 as a total function from one scalar value
to its bytes: step 4's first byte followed by step 5's continuation bytes. The
domain is `ScalarValue` because PROCI [15509,17620) step 3 asserts
"encoderDecoder is not an encoder instance or item is not a surrogate", and
INFRA-R3 turns an assertion the carrier can express into the carrier. -/
def encodeScalar (s : ScalarValue) : ByteSequence :=
  UInt8.ofNat ((s.val.val >>> (6 * encoderCount s.val)) + encoderOffset s.val) ::
    encoderTail s.val.val (encoderCount s.val)

/-- ENCODER [90407,91744): "UTF-8's encoder's handler, given unused and
codePoint", step 1 ("If codePoint is end-of-queue, then return finished") and
steps 2 to 6. -/
def encoderHandler : Item ScalarValue → Encoding.HandlerResult Byte
  | Item.endOfQueue => Encoding.HandlerResult.finished
  | Item.value s => Encoding.HandlerResult.items (encodeScalar s)

/-- ENCODE [46912,47215) through LEGACY [50170,50822) at UTF-8, run to
completion: the encoder is stateless, so PROCQ [14785,15508) is a `flatMap`. -/
def encodeScalars (ss : List ScalarValue) : ByteSequence :=
  ss.flatMap encodeScalar

/-- ENCODE [46912,47215) at the queue face: "return the result of encoding
ioQueue with encoding UTF-8 and output". -/
def encodeQueue (ioQueue : IoQueue ScalarValue) : IoQueue Byte :=
  IoQueue.convertTo (encodeScalars (IoQueue.convertFrom ioQueue))

/-- The byte order mark DECODE [45059,45762) step 2 tests for, "0xEF 0xBB
0xBF". -/
def bom : ByteSequence := [0xEF, 0xBB, 0xBF]

/-- The scalar values of a scalar value string, HOOKS [43782,45058): "Standards
are to ensure that the input I/O queues they pass to UTF-8 encode … contain no
surrogates." The hypothesis is that restriction (INFRA-R3) and it is what makes
each code point a scalar value. -/
def scalars (input : JsString) (h : JsString.isScalarValueString input = true) :
    List ScalarValue :=
  (JsString.codePoints input).pmap
    (fun c (hc : CodePoint.isScalarValue c = true) => ⟨c, isSurrogate_of_isScalarValue hc⟩)
    (fun c hc => List.all_eq_true.mp h c hc)

/-- ENCODE [46912,47215) at the string face, with HOOKS' restriction as a
hypothesis argument in the exact shape `JsString.isomorphicEncode` already
uses. -/
def encode (input : JsString) (h : JsString.isScalarValueString input = true) : ByteSequence :=
  encodeScalars (scalars input h)

/-- `encode` with its hypothesis decided at run time, in the shape
`JsString.isomorphicEncode?` and `asciiEncode?` already use. -/
def encode? (input : JsString) : Option ByteSequence :=
  if h : JsString.isScalarValueString input = true then some (encode input h) else none

/-! ### The encoder's laws -/

/-- ENCODER [90407,91744) step 3's switch, with the ASCII case of step 2 folded
in as count 0. -/
theorem encoderCount_eq (c : CodePoint) :
    encoderCount c =
      (if c.val ≤ 0x7F then 0 else if c.val ≤ 0x7FF then 1
        else if c.val ≤ 0xFFFF then 2 else 3) := rfl

/-- ENCODER [90407,91744) step 3's offsets, with the ASCII case folded in as
0x00. -/
theorem encoderOffset_eq (c : CodePoint) :
    encoderOffset c =
      (if c.val ≤ 0x7F then 0x00 else if c.val ≤ 0x7FF then 0xC0
        else if c.val ≤ 0xFFFF then 0xE0 else 0xF0) := rfl

/-- ENCODER [90407,91744) step 5 at count zero: the loop is empty. -/
theorem encoderTail_zero (v : Nat) : encoderTail v 0 = [] := rfl

/-- ENCODER [90407,91744) step 5's loop body. The byte at shift `6 × count` is
appended first, so the recursion peels the high group. -/
theorem encoderTail_succ (v : Nat) (n : Nat) :
    encoderTail v (n + 1) =
      UInt8.ofNat (0x80 ||| ((v >>> (6 * n)) &&& 0x3F)) :: encoderTail v n := rfl

/-- Step 5 runs exactly `count` times. -/
theorem encoderTail_length (v : Nat) (n : Nat) : List.length (encoderTail v n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [encoderTail_succ, List.length_cons, ih]

/-- Every byte step 5 appends is a continuation byte. -/
theorem encoderTail_continuation (v : Nat) (n : Nat) (b : Byte)
    (hb : b ∈ encoderTail v n) : 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  induction n with
  | zero => exact absurd hb (by rw [encoderTail_zero]; simp)
  | succ n ih =>
    rw [encoderTail_succ, List.mem_cons] at hb
    rcases hb with rfl | hb
    · have hlt : (v >>> (6 * n)) % 64 < 64 := Nat.mod_lt _ (by decide)
      rw [land_six, lor_continuation _ hlt, toNat_ofNat_lt (by omega)]
      omega
    · exact ih hb

/-- ENCODER [90407,91744) steps 4 to 6 assembled. -/
theorem encodeScalar_eq (s : ScalarValue) :
    encodeScalar s =
      UInt8.ofNat ((s.val.val >>> (6 * encoderCount s.val)) + encoderOffset s.val) ::
        encoderTail s.val.val (encoderCount s.val) := rfl

private theorem encoderTail_one (v : Nat) :
    encoderTail v 1 = [UInt8.ofNat (0x80 + v % 64)] := by
  rw [encoderTail_succ, encoderTail_zero, Nat.mul_zero, Nat.shiftRight_zero, land_six,
    lor_continuation _ (Nat.mod_lt _ (by decide))]

private theorem encoderTail_two (v : Nat) :
    encoderTail v 2 =
      [UInt8.ofNat (0x80 + v / 64 % 64), UInt8.ofNat (0x80 + v % 64)] := by
  rw [encoderTail_succ, encoderTail_one, show 6 * 1 = 6 from rfl, shiftRight_div,
    show (2 : Nat) ^ 6 = 64 by decide, land_six, lor_continuation _ (Nat.mod_lt _ (by decide))]

private theorem encoderTail_three (v : Nat) :
    encoderTail v 3 =
      [UInt8.ofNat (0x80 + v / 4096 % 64), UInt8.ofNat (0x80 + v / 64 % 64),
        UInt8.ofNat (0x80 + v % 64)] := by
  rw [encoderTail_succ, encoderTail_two, show 6 * 2 = 12 from rfl, shiftRight_div,
    show (2 : Nat) ^ 12 = 4096 by decide, land_six,
    lor_continuation _ (Nat.mod_lt _ (by decide))]

/-- ENCODER [90407,91744) step 2: "If codePoint is an ASCII code point, then
return a byte whose value is codePoint." -/
theorem encodeScalar_ascii (s : ScalarValue) (h : s.val.val ≤ 0x7F) :
    encodeScalar s = [UInt8.ofNat s.val.val] := by
  have hc : encoderCount s.val = 0 := by rw [encoderCount_eq, if_pos h]
  have ho : encoderOffset s.val = 0x00 := by rw [encoderOffset_eq, if_pos h]
  rw [encodeScalar_eq, hc, ho, encoderTail_zero, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.add_zero]

private theorem encodeScalar_two_eq (s : ScalarValue) (h1 : 0x80 ≤ s.val.val)
    (h2 : s.val.val ≤ 0x7FF) :
    encodeScalar s =
      [UInt8.ofNat (s.val.val / 64 + 0xC0), UInt8.ofNat (0x80 + s.val.val % 64)] := by
  have hc : encoderCount s.val = 1 := by
    rw [encoderCount_eq, if_neg (by omega), if_pos h2]
  have ho : encoderOffset s.val = 0xC0 := by
    rw [encoderOffset_eq, if_neg (by omega), if_pos h2]
  rw [encodeScalar_eq, hc, ho, encoderTail_one, show 6 * 1 = 6 from rfl, shiftRight_div,
    show (2 : Nat) ^ 6 = 64 by decide]

private theorem encodeScalar_three_eq (s : ScalarValue) (h1 : 0x800 ≤ s.val.val)
    (h2 : s.val.val ≤ 0xFFFF) :
    encodeScalar s =
      [UInt8.ofNat (s.val.val / 4096 + 0xE0), UInt8.ofNat (0x80 + s.val.val / 64 % 64),
        UInt8.ofNat (0x80 + s.val.val % 64)] := by
  have hc : encoderCount s.val = 2 := by
    rw [encoderCount_eq, if_neg (by omega), if_neg (by omega), if_pos h2]
  have ho : encoderOffset s.val = 0xE0 := by
    rw [encoderOffset_eq, if_neg (by omega), if_neg (by omega), if_pos h2]
  rw [encodeScalar_eq, hc, ho, encoderTail_two, show 6 * 2 = 12 from rfl, shiftRight_div,
    show (2 : Nat) ^ 12 = 4096 by decide]

private theorem encodeScalar_four_eq (s : ScalarValue) (h1 : 0x10000 ≤ s.val.val) :
    encodeScalar s =
      [UInt8.ofNat (s.val.val / 262144 + 0xF0), UInt8.ofNat (0x80 + s.val.val / 4096 % 64),
        UInt8.ofNat (0x80 + s.val.val / 64 % 64), UInt8.ofNat (0x80 + s.val.val % 64)] := by
  have hc : encoderCount s.val = 3 := by
    rw [encoderCount_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have ho : encoderOffset s.val = 0xF0 := by
    rw [encoderOffset_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [encodeScalar_eq, hc, ho, encoderTail_three, show 6 * 3 = 18 from rfl, shiftRight_div,
    show (2 : Nat) ^ 18 = 262144 by decide]

/-- ENCODER [90407,91744) step 3, first row of the switch: one byte. -/
theorem encodeScalar_length_one (s : ScalarValue) (h : s.val.val ≤ 0x7F) :
    List.length (encodeScalar s) = 1 := by rw [encodeScalar_ascii s h]; rfl

/-- ENCODER [90407,91744) step 3, "U+0080 to U+07FF, inclusive": two bytes. -/
theorem encodeScalar_length_two (s : ScalarValue) (h1 : 0x80 ≤ s.val.val)
    (h2 : s.val.val ≤ 0x7FF) : List.length (encodeScalar s) = 2 := by
  rw [encodeScalar_two_eq s h1 h2]; rfl

/-- ENCODER [90407,91744) step 3, "U+0800 to U+FFFF, inclusive": three bytes. -/
theorem encodeScalar_length_three (s : ScalarValue) (h1 : 0x800 ≤ s.val.val)
    (h2 : s.val.val ≤ 0xFFFF) : List.length (encodeScalar s) = 3 := by
  rw [encodeScalar_three_eq s h1 h2]; rfl

/-- ENCODER [90407,91744) step 3, "U+10000 to U+10FFFF, inclusive": four
bytes. -/
theorem encodeScalar_length_four (s : ScalarValue) (h1 : 0x10000 ≤ s.val.val) :
    List.length (encodeScalar s) = 4 := by rw [encodeScalar_four_eq s h1]; rfl

/-- The shape is exactly four lengths: there is no fifth row in step 3's switch
and step 4 always emits a first byte. -/
theorem encodeScalar_length_mem (s : ScalarValue) : List.length (encodeScalar s) ∈ [1, 2, 3, 4] := by
  rw [encodeScalar_eq, List.length_cons, encoderTail_length, encoderCount_eq]
  split
  · decide
  · split
    · decide
    · split <;> decide

/-- Step 4 always emits a first byte. -/
theorem encodeScalar_ne_nil (s : ScalarValue) : encodeScalar s ≠ [] := by
  rw [encodeScalar_eq]; exact List.cons_ne_nil _ _

/-- The lead byte lies in exactly the four ranges DECODER [86515,90406) step 3
accepts. 0xC0 and 0xC1 are unreachable, the encoder half of "no overlong
encoding exists"; 0xF5 to 0xFF are unreachable, the encoder half of "nothing
above U+10FFFF is encodable". -/
theorem encodeScalar_head_range (s : ScalarValue) (b : Byte)
    (h : (encodeScalar s).head? = some b) :
    (b.toNat ≤ 0x7F ∨ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) ∨
      (0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF) ∨ (0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4)) := by
  have hle : s.val.val ≤ 0x10FFFF := s.val.isLe
  rcases Nat.lt_or_ge s.val.val 0x80 with h1 | h1
  · rw [encodeScalar_ascii s (by omega)] at h
    rw [List.head?_cons, Option.some.injEq] at h
    subst h
    exact Or.inl (by rw [toNat_ofNat_lt (by omega)]; omega)
  · rcases Nat.lt_or_ge s.val.val 0x800 with h2 | h2
    · rw [encodeScalar_two_eq s h1 (by omega)] at h
      rw [List.head?_cons, Option.some.injEq] at h
      subst h
      exact Or.inr (Or.inl (by rw [toNat_ofNat_lt (by omega)]; omega))
    · rcases Nat.lt_or_ge s.val.val 0x10000 with h3 | h3
      · rw [encodeScalar_three_eq s h2 (by omega)] at h
        rw [List.head?_cons, Option.some.injEq] at h
        subst h
        exact Or.inr (Or.inr (Or.inl (by rw [toNat_ofNat_lt (by omega)]; omega)))
      · rw [encodeScalar_four_eq s h3] at h
        rw [List.head?_cons, Option.some.injEq] at h
        subst h
        exact Or.inr (Or.inr (Or.inr (by rw [toNat_ofNat_lt (by omega)]; omega)))

/-- Every byte after the first is a continuation byte, so no encoded scalar
value contains a lead byte anywhere but at its head. -/
theorem encodeScalar_tail_continuation (s : ScalarValue) (b : Byte)
    (h : b ∈ (encodeScalar s).drop 1) : 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  rw [encodeScalar_eq, List.drop_succ_cons, List.drop_zero] at h
  exact encoderTail_continuation _ _ b h

/-- DECODE [45059,45762) step 2's mark. -/
theorem bom_eq : bom = [(0xEF : Byte), 0xBB, 0xBF] := rfl

/-- Canonical-form injectivity (RS-1): distinct scalar values have distinct
encodings. Proved by case analysis on the four rows of step 3's switch, so that
no classical route through `Function.Injective` is taken. -/
theorem encodeScalar_injective (a b : ScalarValue) (h : encodeScalar a = encodeScalar b) :
    a = b := by
  have hla : a.val.val ≤ 0x10FFFF := a.val.isLe
  have hlb : b.val.val ≤ 0x10FFFF := b.val.isLe
  suffices hv : a.val.val = b.val.val from Subtype.ext (CodePoint.ext hv)
  have hlen := congrArg List.length h
  rcases Nat.lt_or_ge a.val.val 0x80 with ha1 | ha1 <;>
    rcases Nat.lt_or_ge b.val.val 0x80 with hb1 | hb1
  · rw [encodeScalar_ascii a (by omega), encodeScalar_ascii b (by omega)] at h
    have := congrArg (fun l => (l.head?.getD 0).toNat) h
    simp only [List.head?_cons, Option.getD_some] at this
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
    exact this
  · rcases Nat.lt_or_ge b.val.val 0x800 with hb2 | hb2
    · rw [encodeScalar_length_one a (by omega), encodeScalar_length_two b hb1 (by omega)] at hlen
      exact absurd hlen (by decide)
    · rcases Nat.lt_or_ge b.val.val 0x10000 with hb3 | hb3
      · rw [encodeScalar_length_one a (by omega), encodeScalar_length_three b hb2 (by omega)]
          at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_length_one a (by omega), encodeScalar_length_four b hb3] at hlen
        exact absurd hlen (by decide)
  · rcases Nat.lt_or_ge a.val.val 0x800 with ha2 | ha2
    · rw [encodeScalar_length_two a ha1 (by omega), encodeScalar_length_one b (by omega)] at hlen
      exact absurd hlen (by decide)
    · rcases Nat.lt_or_ge a.val.val 0x10000 with ha3 | ha3
      · rw [encodeScalar_length_three a ha2 (by omega), encodeScalar_length_one b (by omega)]
          at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_length_four a ha3, encodeScalar_length_one b (by omega)] at hlen
        exact absurd hlen (by decide)
  · rcases Nat.lt_or_ge a.val.val 0x800 with ha2 | ha2 <;>
      rcases Nat.lt_or_ge b.val.val 0x800 with hb2 | hb2
    · rw [encodeScalar_two_eq a ha1 (by omega), encodeScalar_two_eq b hb1 (by omega)] at h
      rw [List.cons.injEq, List.cons.injEq] at h
      have e1 := congrArg UInt8.toNat h.1
      have e2 := congrArg UInt8.toNat h.2.1
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e1
      rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e2
      omega
    · rcases Nat.lt_or_ge b.val.val 0x10000 with hb3 | hb3
      · rw [encodeScalar_length_two a ha1 (by omega),
          encodeScalar_length_three b hb2 (by omega)] at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_length_two a ha1 (by omega), encodeScalar_length_four b hb3] at hlen
        exact absurd hlen (by decide)
    · rcases Nat.lt_or_ge a.val.val 0x10000 with ha3 | ha3
      · rw [encodeScalar_length_three a ha2 (by omega),
          encodeScalar_length_two b hb1 (by omega)] at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_length_four a ha3, encodeScalar_length_two b hb1 (by omega)] at hlen
        exact absurd hlen (by decide)
    · rcases Nat.lt_or_ge a.val.val 0x10000 with ha3 | ha3 <;>
        rcases Nat.lt_or_ge b.val.val 0x10000 with hb3 | hb3
      · rw [encodeScalar_three_eq a ha2 (by omega), encodeScalar_three_eq b hb2 (by omega)] at h
        rw [List.cons.injEq, List.cons.injEq, List.cons.injEq] at h
        have e1 := congrArg UInt8.toNat h.1
        have e2 := congrArg UInt8.toNat h.2.1
        have e3 := congrArg UInt8.toNat h.2.2.1
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e1
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e2
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e3
        omega
      · rw [encodeScalar_length_three a ha2 (by omega), encodeScalar_length_four b hb3] at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_length_four a ha3, encodeScalar_length_three b hb2 (by omega)] at hlen
        exact absurd hlen (by decide)
      · rw [encodeScalar_four_eq a ha3, encodeScalar_four_eq b hb3] at h
        rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at h
        have e1 := congrArg UInt8.toNat h.1
        have e2 := congrArg UInt8.toNat h.2.1
        have e3 := congrArg UInt8.toNat h.2.2.1
        have e4 := congrArg UInt8.toNat h.2.2.2.1
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e1
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e2
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e3
        rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at e4
        omega

/-- The byte order mark is emitted by exactly one scalar value, U+FEFF. -/
theorem encodeScalar_bom_iff (s : ScalarValue) :
    encodeScalar s = bom ↔ s.val.val = 0xFEFF := by
  have hle : s.val.val ≤ 0x10FFFF := s.val.isLe
  constructor
  · intro h
    have hlen := congrArg List.length h
    rw [bom_eq] at hlen h
    rcases Nat.lt_or_ge s.val.val 0x80 with h1 | h1
    · rw [encodeScalar_length_one s (by omega)] at hlen; exact absurd hlen (by decide)
    · rcases Nat.lt_or_ge s.val.val 0x800 with h2 | h2
      · rw [encodeScalar_length_two s h1 (by omega)] at hlen; exact absurd hlen (by decide)
      · rcases Nat.lt_or_ge s.val.val 0x10000 with h3 | h3
        · rw [encodeScalar_three_eq s h2 (by omega), List.cons.injEq, List.cons.injEq,
            List.cons.injEq] at h
          have e1 := congrArg UInt8.toNat h.1
          have e2 := congrArg UInt8.toNat h.2.1
          have e3 := congrArg UInt8.toNat h.2.2.1
          rw [toNat_ofNat_lt (by omega)] at e1 e2 e3
          rw [show ((0xEF : Byte)).toNat = 0xEF from rfl] at e1
          rw [show ((0xBB : Byte)).toNat = 0xBB from rfl] at e2
          rw [show ((0xBF : Byte)).toNat = 0xBF from rfl] at e3
          omega
        · rw [encodeScalar_length_four s h3] at hlen; exact absurd hlen (by decide)
  · intro h
    rw [encodeScalar_three_eq s (by omega) (by omega), h, bom_eq]
    rfl

/-- ENCODE [46912,47215) run over a list: the concatenation of the per-scalar
encodings, because the encoder is stateless. -/
theorem encodeScalars_eq (ss : List ScalarValue) :
    encodeScalars ss = ss.flatMap encodeScalar := rfl

/-- Concatenation of inputs is concatenation of outputs. -/
theorem encodeScalars_append (a b : List ScalarValue) :
    encodeScalars (a ++ b) = encodeScalars a ++ encodeScalars b := by
  rw [encodeScalars, encodeScalars, encodeScalars, List.flatMap_append]

/-- ENCODE [46912,47215) at the queue face. -/
theorem encodeQueue_convertTo (ss : List ScalarValue) :
    encodeQueue (IoQueue.convertTo ss) = IoQueue.convertTo (encodeScalars ss) := by
  rw [encodeQueue, IoQueue.convertFrom_convertTo]

private theorem map_val_pmap {α : Type} {p : α → Prop} {q : α → Prop}
    (f : (a : α) → p a → { x : α // q x }) (hf : ∀ (a : α) (h : p a), (f a h).val = a) :
    ∀ (l : List α) (H : ∀ a ∈ l, p a), (l.pmap f H).map (fun s => s.val) = l
  | [], _ => rfl
  | a :: t, H => by
    rw [List.pmap, List.map_cons, hf,
      map_val_pmap f hf t (fun x hx => H x (List.mem_cons_of_mem _ hx))]

/-- The bridge between `JsString.codePoints` and the encoder's item type. -/
theorem scalars_val (input : JsString) (h : JsString.isScalarValueString input = true) :
    (scalars input h).map (fun s => s.val) = JsString.codePoints input := by
  rw [scalars]
  exact map_val_pmap _ (fun _ _ => rfl) _ _

/-- ENCODE [46912,47215) at the string face. -/
theorem encode_eq (input : JsString) (h : JsString.isScalarValueString input = true) :
    encode input h = encodeScalars (scalars input h) := rfl

/-- `encode?` answers on a scalar value string. -/
theorem encode?_eq_some (input : JsString) (h : JsString.isScalarValueString input = true) :
    encode? input = some (encode input h) := by rw [encode?, dif_pos h]

/-- `encode?` refuses a string that is not a scalar value string. -/
theorem encode?_eq_none (input : JsString)
    (h : JsString.isScalarValueString input = false) : encode? input = none := by
  rw [encode?, dif_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Infra's "prefix" loop of section `byte-sequences` is `List.isPrefixOf` from
the scanned index on. The `startsWith` reasoning of DECODE [45059,45762) rests
on this bridge. -/
private theorem isPrefixLoop_eq (p x : ByteSequence) :
    ∀ (fuel i : Nat), i + fuel = List.length p →
      ByteSequence.isPrefixLoop p x i fuel = List.isPrefixOf (p.drop i) (x.drop i)
  | 0, i, hi => by
    have hp : p.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [ByteSequence.isPrefixLoop, hp, List.isPrefixOf]
  | fuel + 1, i, hi => by
    have hlt' : i < List.length p := by omega
    have hlt : i < ByteSequence.length p := by rw [ByteSequence.length]; omega
    have hpd : p.drop i = p[i] :: p.drop (i + 1) := List.drop_eq_getElem_cons hlt'
    rw [ByteSequence.isPrefixLoop, dif_pos hlt, hpd]
    by_cases hx' : i < List.length x
    · have hx : i < ByteSequence.length x := by rw [ByteSequence.length]; omega
      have hxd : x.drop i = x[i] :: x.drop (i + 1) := List.drop_eq_getElem_cons hx'
      rw [dif_pos hx, hxd, List.isPrefixOf]
      cases hb : (p[i] == x[i]) with
      | true =>
        have hne : (p[i] != x[i]) = false := by rw [bne, hb]; rfl
        rw [if_neg (by rw [hne]; exact Bool.false_ne_true),
          isPrefixLoop_eq p x fuel (i + 1) (by omega), Bool.true_and]
      | false =>
        have hne : (p[i] != x[i]) = true := by rw [bne, hb]; rfl
        rw [if_pos hne, Bool.false_and]
    · have hx : ¬ (i < ByteSequence.length x) := by rw [ByteSequence.length]; omega
      have hxd : x.drop i = [] := List.drop_eq_nil_of_le (by omega)
      rw [dif_neg hx, hxd]
      rfl

/-- Infra's "starts with" of section `byte-sequences` at the byte order mark:
the mark is a prefix exactly when the sequence is the mark followed by
something. -/
private theorem startsWith_bom_iff (x : ByteSequence) :
    ByteSequence.startsWith x bom = true ↔ ∃ t : ByteSequence, x = bom ++ t := by
  rw [ByteSequence.startsWith, ByteSequence.isPrefix,
    isPrefixLoop_eq _ _ _ 0 (by rw [ByteSequence.length]; omega),
    List.drop_zero, List.drop_zero, List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩; exact ⟨t, ht.symm⟩

/-- A lead byte of 0xEF puts the scalar value in step 3's three-byte row: the
one-byte row is at most 0x7F, the two-byte row at most 0xDF and the four-byte
row at least 0xF0. -/
private theorem encodeScalar_head_ef (s : ScalarValue)
    (hhead : (encodeScalar s).head? = some (0xEF : Byte)) :
    0x800 ≤ s.val.val ∧ s.val.val ≤ 0xFFFF := by
  have hle : s.val.val ≤ 0x10FFFF := s.val.isLe
  have h239 : ((0xEF : Byte)).toNat = 0xEF := rfl
  rcases Nat.lt_or_ge s.val.val 0x80 with h1 | h1
  · rw [encodeScalar_ascii s (by omega), List.head?_cons, Option.some.injEq] at hhead
    have hn := congrArg UInt8.toNat hhead
    rw [toNat_ofNat_lt (by omega), h239] at hn
    omega
  · rcases Nat.lt_or_ge s.val.val 0x800 with h2 | h2
    · rw [encodeScalar_two_eq s h1 (by omega), List.head?_cons, Option.some.injEq] at hhead
      have hn := congrArg UInt8.toNat hhead
      rw [toNat_ofNat_lt (by omega), h239] at hn
      omega
    · rcases Nat.lt_or_ge s.val.val 0x10000 with h3 | h3
      · exact ⟨h2, by omega⟩
      · rw [encodeScalar_four_eq s h3, List.head?_cons, Option.some.injEq] at hhead
        have hn := congrArg UInt8.toNat hhead
        rw [toNat_ofNat_lt (by omega), h239] at hn
        omega

/-- The encoder never manufactures a byte order mark: its output starts with
0xEF 0xBB 0xBF exactly when the input's first code point is U+FEFF. -/
theorem encode_startsWith_bom_iff (input : JsString)
    (h : JsString.isScalarValueString input = true) :
    ByteSequence.startsWith (encode input h) bom = true ↔
      ∃ c : CodePoint, (JsString.codePoints input).head? = some c ∧ c.val = 0xFEFF := by
  have hval := scalars_val input h
  rw [encode_eq, encodeScalars_eq]
  match hs : scalars input h with
  | [] =>
    rw [hs, List.map_nil] at hval
    rw [List.flatMap_nil, ← hval]
    constructor
    · intro hp
      rcases (startsWith_bom_iff []).mp hp with ⟨t, ht⟩
      exact absurd (congrArg List.length ht) (by simp [bom])
    · rintro ⟨c, hc, _⟩
      exact absurd hc (by simp)
  | s :: rest =>
    rw [hs, List.map_cons] at hval
    rw [List.flatMap_cons, ← hval, List.head?_cons]
    have hne := encodeScalar_ne_nil s
    have hsplit : (encodeScalar s ++ List.flatMap encodeScalar rest).head? =
        (encodeScalar s).head? := by
      match hE : encodeScalar s with
      | [] => exact absurd hE hne
      | a :: t => rw [List.cons_append, List.head?_cons, List.head?_cons]
    constructor
    · intro hp
      rcases (startsWith_bom_iff _).mp hp with ⟨t, ht⟩
      refine ⟨s.val, rfl, ?_⟩
      refine (encodeScalar_bom_iff s).mp ?_
      have hhead : (encodeScalar s).head? = some (0xEF : Byte) := by
        rw [← hsplit, ht, bom_eq]; rfl
      have hrange := encodeScalar_head_ef s hhead
      have hlen : List.length (encodeScalar s) = 3 :=
        encodeScalar_length_three s hrange.1 hrange.2
      have hbl : List.length bom = 3 := rfl
      exact List.append_inj_left ht (by rw [hlen, hbl])
    · rintro ⟨c, hc, hv⟩
      rw [Option.some.injEq] at hc
      subst hc
      have heb : encodeScalar s = bom := (encodeScalar_bom_iff s).mpr hv
      rw [heb]
      exact (startsWith_bom_iff _).mpr ⟨_, rfl⟩

private theorem codePoints_single (u : CodeUnit) :
    JsString.codePoints [u] = [CodePoint.ofUnit u] := by
  show (if _hl : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF then [CodePoint.ofUnit u]
      else CodePoint.ofUnit u :: JsString.codePoints ([] : JsString)) = [CodePoint.ofUnit u]
  by_cases hl : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF
  · rw [dif_pos hl]
  · rw [dif_neg hl]; rfl

private theorem codePoints_cons₂ (u v : CodeUnit) (rest : JsString) :
    JsString.codePoints (u :: v :: rest) =
      (if hl : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF then
        (if ht : 0xDC00 ≤ v.toNat ∧ v.toNat ≤ 0xDFFF then
          JsString.pairValue u v hl ht :: JsString.codePoints rest
        else CodePoint.ofUnit u :: JsString.codePoints (v :: rest))
      else CodePoint.ofUnit u :: JsString.codePoints (v :: rest)) := rfl

private theorem units_le_of_codePoints_le : ∀ (input : JsString),
    (∀ c ∈ JsString.codePoints input, c.val ≤ 0x7F) → ∀ unit ∈ input, unit.toNat ≤ 0x7F
  | [], _ => by intro unit hmem; exact absurd hmem (by simp)
  | [u], h => by
    rw [codePoints_single] at h
    intro unit hmem
    rcases List.mem_cons.mp hmem with rfl | hm
    · exact h _ (List.mem_cons_self ..)
    · exact absurd hm (by simp)
  | u :: v :: rest', h => by
    rw [codePoints_cons₂] at h
    by_cases hl : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF
    · rw [dif_pos hl] at h
      by_cases ht : 0xDC00 ≤ v.toNat ∧ v.toNat ≤ 0xDFFF
      · rw [dif_pos ht] at h
        have hpair := h _ (List.mem_cons_self ..)
        simp only [JsString.pairValue] at hpair
        omega
      · rw [dif_neg ht] at h
        intro unit hmem
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact h _ (List.mem_cons_self ..)
        · exact units_le_of_codePoints_le (v :: rest')
            (fun c hc => h c (List.mem_cons_of_mem _ hc)) unit hm
    · rw [dif_neg hl] at h
      intro unit hmem
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact h _ (List.mem_cons_self ..)
      · exact units_le_of_codePoints_le (v :: rest')
          (fun c hc => h c (List.mem_cons_of_mem _ hc)) unit hm

private theorem encodeScalars_ascii (ss : List ScalarValue)
    (h : ∀ s ∈ ss, s.val.val ≤ 0x7F) :
    encodeScalars ss = ss.map (fun s => UInt8.ofNat s.val.val) := by
  induction ss with
  | nil => rfl
  | cons s t ih =>
    rw [encodeScalars, List.flatMap_cons, encodeScalar_ascii s (h s (List.mem_cons_self ..))]
    rw [encodeScalars] at ih
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.map_cons, List.cons_append,
      List.nil_append]

/-- The note of Infra's `op.ascii-encode` [56961,57243) of
`vendor/whatwg-infra-3f984adc/infra.bs`, SHA-256
`9bdf92ca84d3d01df7cc26632b244c820b041ed713988dd0c8d2b47c389a67b4`: "Isomorphic
encode and UTF-8 encode return the same byte sequence for input."
`docs/INFRA-PROOF-PLAN.md` section 4.6 left that row `partial` with the bridge
named "until Encoding has its own pin"; the pin exists now, and this is the
theorem that closes the UTF-8 half. -/
theorem encode_ascii_eq_asciiEncode (input : JsString)
    (h : JsString.isScalarValueString input = true)
    (hA : JsString.isAsciiString input = true) :
    JsString.asciiEncode? input = some (encode input h) := by
  have hcp : ∀ c ∈ JsString.codePoints input, c.val ≤ 0x7F := by
    intro c hc
    have := List.all_eq_true.mp hA c hc
    rw [CodePoint.isAscii, CodePoint.inRange] at this
    exact (of_decide_eq_true this).2
  have hunits : ∀ unit ∈ input, unit.toNat ≤ 0x7F := units_le_of_codePoints_le input hcp
  have hlead : ∀ unit ∈ input, unit.toNat < 0xD800 := fun x hx => by
    have := hunits x hx; omega
  have hval := scalars_val input h
  have hsc : ∀ s ∈ scalars input h, s.val.val ≤ 0x7F := by
    intro s hs
    exact hcp s.val (hval ▸ List.mem_map_of_mem hs)
  rw [JsString.asciiEncode?_eq input hunits, encode_eq, encodeScalars_ascii _ hsc]
  have : (scalars input h).map (fun s => UInt8.ofNat s.val.val) =
      ((scalars input h).map (fun s => s.val)).map (fun c => UInt8.ofNat c.val) := by
    rw [List.map_map]; rfl
  rw [this, hval, JsString.codePoints_of_no_lead input hlead, List.map_map]
  rfl

/-- The other half of the same note, from Infra's byte-sequences prose
[34550,34700): "UTF-8 encode from Encoding is encouraged. In rare circumstances
isomorphic encode might be needed." The two disagree on the pin's own U+00E9. A
finite probe, written with explicit code units so that no `String` literal — and
so no path into `Classical.choice` — appears. -/
theorem encode_ne_isomorphicEncode_example :
    encode? [(0xE9 : CodeUnit)] = some [(0xC3 : Byte), 0xA9] ∧
      JsString.isomorphicEncode? [(0xE9 : CodeUnit)] = some [(0xE9 : Byte)] := by
  constructor
  · decide
  · decide

/-- The pin's own 💩, the four bytes of EXRESTORE [9727,9981). A finite
probe. -/
theorem encode_astral_example :
    encode? [(0xD83D : CodeUnit), 0xDCA9] = some [(0xF0 : Byte), 0x9F, 0x92, 0xA9] := by
  decide

end Utf8

/-! ### `get an encoder` and `encode or fail`

GETENC [50829,51166) and ORFAILENC [51167,53203), the DB-02 boundary. -/

namespace Encoding

/-- GETENC [50829,51166) with its step 1 assertion as a hypothesis argument
(INFRA-R3): "Assert: encoding is not replacement or UTF-16BE/LE. Return an
instance of encoding's encoder." -/
def getAnEncoder (name : Name) (_h : Name.hasEncoder name = true) : Encoder :=
  match name with
  | Name.utf8 => Encoder.utf8
  | n => Encoder.foreign n []

/-- GETENC [50829,51166) with its assertion decided at run time. -/
def getAnEncoder? (name : Name) : Option Encoder :=
  if h : Name.hasEncoder name = true then some (getAnEncoder name h) else none

/-- ORFAILENC [51167,53203). The encoder instance is retained across the call
and returned, which is exactly what makes ISO-2022-JP's statefulness observable.
UTF-8's answer is the whole encoding with a null `potentialError`, per the note
of LEGACY [50170,50822): "Layering UTF-8 encode on top is safe as it never
triggers errors." A foreign profile answers from its tape; an exhausted tape is
an unanswered decision, a live frontier and never an error. -/
def encodeOrFail : Encoder → IoQueue ScalarValue → Option (EncodeAnswer × Encoder)
  | Encoder.utf8, ioQueue =>
    some (EncodeAnswer.mk (Utf8.encodeScalars (IoQueue.convertFrom ioQueue)) none, Encoder.utf8)
  | Encoder.foreign name (answer :: rest), _ => some (answer, Encoder.foreign name rest)
  | Encoder.foreign _ [], _ => none

/-! ### Laws of the names, the tape and the two hooks -/

/-- GETENC [50829,51166) step 1 and the note of VOCAB [13366,14779). -/
theorem Name.hasEncoder_iff (n : Name) :
    Name.hasEncoder n = false ↔
      (n = Name.replacement ∨ n = Name.utf16be ∨ n = Name.utf16le) := by
  cases n <;> simp [Name.hasEncoder]

/-- ISO2022 [123264,124113): the pin names exactly one stateful encoder. -/
theorem Name.isStateful_iff (n : Name) :
    Name.isStateful n = true ↔ n = Name.iso2022jp := by
  cases n <;> simp [Name.isStateful]

/-- This packet owns one encoder algorithm; everything else is a DB-02
profile. -/
theorem Name.isOwned_iff (n : Name) : Name.isOwned n = true ↔ n = Name.utf8 := by
  cases n <;> simp [Name.isOwned]

/-- GETENC [50829,51166) at UTF-8. -/
theorem getAnEncoder?_utf8 : getAnEncoder? Name.utf8 = some Encoder.utf8 := rfl

/-- GETENC [50829,51166) refuses the three encoder-less names. -/
theorem getAnEncoder?_eq_none (n : Name) (h : Name.hasEncoder n = false) :
    getAnEncoder? n = none := by
  rw [getAnEncoder?, dif_neg (by rw [h]; exact Bool.false_ne_true)]

/-- GETENC [50829,51166) with the assertion discharged. -/
theorem getAnEncoder?_eq_some (n : Name) (h : Name.hasEncoder n = true) :
    getAnEncoder? n = some (getAnEncoder n h) := by
  rw [getAnEncoder?, dif_pos h]

/-- The UTF-8 instance encodes to UTF-8. -/
theorem Encoder.name_utf8 : Encoder.name Encoder.utf8 = Name.utf8 := rfl

/-- ORFAILENC [51167,53203) over UTF-8's encoder on a whole immediate queue: one
answer, the whole encoding, and a null `potentialError`. -/
theorem encodeOrFail_utf8 (ss : List ScalarValue) :
    encodeOrFail Encoder.utf8 (IoQueue.convertTo ss) =
      some (EncodeAnswer.mk (Utf8.encodeScalars ss) none, Encoder.utf8) := by
  rw [encodeOrFail, IoQueue.convertFrom_convertTo]

/-- UTF-8 always answers, and never with an error. -/
theorem encodeOrFail_utf8_never_errors (q : IoQueue ScalarValue) (answer : EncodeAnswer)
    (next : Encoder) (h : encodeOrFail Encoder.utf8 q = some (answer, next)) :
    EncodeAnswer.potentialError answer = none := by
  rw [encodeOrFail] at h
  exact (congrArg (fun r => (Option.map (fun p => p.1.potentialError) r).getD (some 0)) h).symm

/-- A foreign encoder answers from its tape and the instance advances: DB-02's
"the answer is first-order data on a tape", and what makes ISO-2022-JP's
retained state observable. -/
theorem encodeOrFail_foreign_advances (n : Name) (answer : EncodeAnswer)
    (rest : EncoderTape) (q : IoQueue ScalarValue) :
    encodeOrFail (Encoder.foreign n (answer :: rest)) q =
      some (answer, Encoder.foreign n rest) := rfl

/-- An exhausted tape is an unanswered decision: a live frontier, never an
error. -/
theorem encodeOrFail_foreign_frontier (n : Name) (q : IoQueue ScalarValue) :
    encodeOrFail (Encoder.foreign n []) q = none := rfl

/-- The tape's own termination test, in the shape the URL percent-encoding
boundary already carries: step 7 of `op.percent-encode-after-encoding` of
`vendor/whatwg-url-55d66993/url.bs` [21624,24696) loops "While potentialError is
non-null". -/
theorem EncoderTape.terminated_iff (tape : EncoderTape) :
    EncoderTape.terminated tape = true ↔
      ∃ answer : EncodeAnswer, tape.getLast? = some answer ∧
        EncodeAnswer.potentialError answer = none := by
  rw [EncoderTape.terminated]
  cases h : tape.getLast? with
  | none => simp
  | some answer =>
    cases hp : answer.potentialError with
    | none => simp
    | some v => simp

end Encoding

/-! ## The UTF-8 decoder

DECODER [86515,90406). "UTF-8's decoder has an associated UTF-8 code point,
UTF-8 bytes seen, UTF-8 bytes needed — each a number, initially 0; UTF-8 lower
boundary — a byte, initially 0x80; UTF-8 upper boundary — a byte, initially
0xBF." -/

namespace Utf8

/-- The reachable-state invariant of DECODER [86515,90406), carried by the
carrier under INFRA-R3.

With `r = bytesNeeded − bytesSeen` bytes still to read and `p = 64 ^ (r − 1)`,
the value the run will finish with lies between
`codePoint × 64 × p + (lowerBoundary − 0x80) × p` and
`codePoint × 64 × p + (upperBoundary − 0x80) × p + (p − 1)`. The invariant says
that whole interval is inside U+0000…U+10FFFF and misses the surrogate range —
which is exactly what step 3's boundary table installs (0xE0 lifts the lower
boundary to 0xA0, 0xED drops the upper boundary to 0x9F, 0xF0 lifts to 0x90,
0xF4 drops to 0x8F).

Carrying it is forced, not decorative: `decoderHandler_complete` asks for a
`CodePoint` whose value is `(UTF-8 code point << 6) | (byte & 0x3F)` and
`decoderHandler_items_isScalarValue` asks for that value not to be a surrogate,
and over unrestricted five-tuples both are false — `codePoint = 864`,
`bytesNeeded = 1`, `bytesSeen = 0`, boundaries 0x80/0xBF and `byte = 0x80`
complete to U+D800. The Builder note in the contract records the two
counterexamples. -/
@[reducible] private def decoderInv (cp seen needed lo hi : Nat) : Prop :=
  needed = 0 ∨
    (seen < needed ∧ needed ≤ 3 ∧ 0x80 ≤ lo ∧ hi ≤ 0xBF ∧
      cp * 64 * 64 ^ (needed - seen - 1) + (hi - 0x80) * 64 ^ (needed - seen - 1)
          + (64 ^ (needed - seen - 1) - 1) ≤ 0x10FFFF ∧
      (cp * 64 * 64 ^ (needed - seen - 1) + (hi - 0x80) * 64 ^ (needed - seen - 1)
            + (64 ^ (needed - seen - 1) - 1) < 0xD800 ∨
        0xDFFF < cp * 64 * 64 ^ (needed - seen - 1) + (lo - 0x80) * 64 ^ (needed - seen - 1)))

/-- The five values DECODER [86515,90406) associates with UTF-8's decoder, with
the reachable-state invariant of `decoderInv` discharged by typing (INFRA-R3). -/
abbrev DecoderState : Type :=
  { st : Nat × Nat × Nat × Byte × Byte //
      decoderInv st.1 st.2.1 st.2.2.1 st.2.2.2.1.toNat st.2.2.2.2.toNat }

namespace DecoderState

/-- The state of DECODER [86515,90406) with the given five values; a five-tuple
outside the reachable set is not a state of any run and is mapped to the initial
state, which is the total-function reading of INFRA-R3. -/
def mk (codePoint bytesSeen bytesNeeded : Nat) (lowerBoundary upperBoundary : Byte) :
    DecoderState :=
  if h : decoderInv codePoint bytesSeen bytesNeeded lowerBoundary.toNat upperBoundary.toNat then
    ⟨(codePoint, bytesSeen, bytesNeeded, lowerBoundary, upperBoundary), h⟩
  else ⟨(0, 0, 0, 0x80, 0xBF), Or.inl rfl⟩

/-- DECODER [86515,90406): "UTF-8 code point … a number, initially 0". -/
def codePoint (st : DecoderState) : Nat := st.val.1

/-- DECODER [86515,90406): "UTF-8 bytes seen … a number, initially 0". -/
def bytesSeen (st : DecoderState) : Nat := st.val.2.1

/-- DECODER [86515,90406): "UTF-8 bytes needed … a number, initially 0". -/
def bytesNeeded (st : DecoderState) : Nat := st.val.2.2.1

/-- DECODER [86515,90406): "UTF-8 lower boundary — a byte, initially 0x80". -/
def lowerBoundary (st : DecoderState) : Byte := st.val.2.2.2.1

/-- DECODER [86515,90406): "UTF-8 upper boundary — a byte, initially 0xBF". -/
def upperBoundary (st : DecoderState) : Byte := st.val.2.2.2.2

/-- The initial state of DECODER [86515,90406). -/
def initial : DecoderState := mk 0 0 0 (0x80 : Byte) (0xBF : Byte)

/-- DECODER [86515,90406)'s `<dl>` of initial values. -/
theorem initial_eq : initial = mk 0 0 0 (0x80 : Byte) (0xBF : Byte) := rfl

end DecoderState

private theorem mk_fields (cp seen needed : Nat) (lo hi : Byte)
    (h : decoderInv cp seen needed lo.toNat hi.toNat) :
    (DecoderState.mk cp seen needed lo hi).codePoint = cp ∧
      (DecoderState.mk cp seen needed lo hi).bytesSeen = seen ∧
      (DecoderState.mk cp seen needed lo hi).bytesNeeded = needed ∧
      (DecoderState.mk cp seen needed lo hi).lowerBoundary = lo ∧
      (DecoderState.mk cp seen needed lo hi).upperBoundary = hi := by
  rw [DecoderState.mk, dif_pos h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem state_inv (st : DecoderState) :
    decoderInv st.codePoint st.bytesSeen st.bytesNeeded st.lowerBoundary.toNat
      st.upperBoundary.toNat := st.property

/-- The completion value of DECODER [86515,90406) steps 9 to 11 is a code point:
the invariant bounds the whole interval the run can still reach by U+10FFFF. -/
private theorem complete_le (st : DecoderState) (b : Byte) (hzero : ¬ (st.bytesNeeded = 0))
    (hin : ¬ (b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat))
    (hcomp : st.bytesSeen + 1 = st.bytesNeeded) :
    (st.codePoint <<< 6) ||| (b.toNat &&& 0x3F) ≤ 0x10FFFF := by
  rcases state_inv st with hz | ⟨_, _, hlo, hhi, hmax, _⟩
  · exact absurd hz hzero
  · have hr : st.bytesNeeded - st.bytesSeen - 1 = 0 := by omega
    rw [hr, Nat.pow_zero] at hmax
    have hb : b.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [land_six, lor_shift_six _ _ hb]
    have hble : b.toNat ≤ 0xBF := by omega
    have hbge : 0x80 ≤ b.toNat := by omega
    have hmod : b.toNat % 64 = b.toNat - 0x80 := by omega
    omega

/-- The completion value is never a surrogate: that is what the 0xED upper
boundary of step 3 buys, and it is a theorem of the invariant rather than a
typing assumption. -/
private theorem complete_scalar (st : DecoderState) (b : Byte) (hzero : ¬ (st.bytesNeeded = 0))
    (hin : ¬ (b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat))
    (hcomp : st.bytesSeen + 1 = st.bytesNeeded) :
    ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) < 0xD800 ∨
      0xDFFF < ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) := by
  rcases state_inv st with hz | ⟨_, _, hlo, hhi, _, hsur⟩
  · exact absurd hz hzero
  · have hr : st.bytesNeeded - st.bytesSeen - 1 = 0 := by omega
    rw [hr, Nat.pow_zero] at hsur
    have hb : b.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [land_six, lor_shift_six _ _ hb]
    have hble : b.toNat ≤ 0xBF := by omega
    have hbge : 0x80 ≤ b.toNat := by omega
    have hmod : b.toNat % 64 = b.toNat - 0x80 := by omega
    omega

/-- DECODER [86515,90406): "UTF-8's decoder's handler, given ioQueue and byte,
runs these steps", steps 1 to 11. The handler returns the possibly-modified
input queue because step 4.2 restores the byte to it. Its item type is
`CodePoint` and not `ScalarValue`: step 11 returns "a code point whose value is
codePoint", and that the value is never a surrogate is the theorem
`decoderHandler_items_isScalarValue`. -/
def decoderHandler (st : DecoderState) (ioQueue : IoQueue Byte) (item : Item Byte) :
    Encoding.HandlerResult CodePoint × DecoderState × IoQueue Byte :=
  match item with
  | Item.endOfQueue =>
    if _hne : st.bytesNeeded ≠ 0 then
      (Encoding.HandlerResult.error none,
        DecoderState.mk st.codePoint st.bytesSeen 0 st.lowerBoundary st.upperBoundary, ioQueue)
    else
      (Encoding.HandlerResult.finished, st, ioQueue)
  | Item.value byte =>
    if hzero : st.bytesNeeded = 0 then
      if hA : byte.toNat ≤ 0x7F then
        (Encoding.HandlerResult.items [⟨byte.toNat, Nat.le_trans hA (by decide)⟩], st, ioQueue)
      else if _h2 : 0xC2 ≤ byte.toNat ∧ byte.toNat ≤ 0xDF then
        (Encoding.HandlerResult.continues,
          DecoderState.mk (byte.toNat &&& 0x1F) st.bytesSeen 1 (0x80 : Byte) (0xBF : Byte),
          ioQueue)
      else if _h3 : 0xE0 ≤ byte.toNat ∧ byte.toNat ≤ 0xEF then
        (Encoding.HandlerResult.continues,
          DecoderState.mk (byte.toNat &&& 0xF) st.bytesSeen 2
            (if byte.toNat = 0xE0 then (0xA0 : Byte) else (0x80 : Byte))
            (if byte.toNat = 0xED then (0x9F : Byte) else (0xBF : Byte)),
          ioQueue)
      else if _h4 : 0xF0 ≤ byte.toNat ∧ byte.toNat ≤ 0xF4 then
        (Encoding.HandlerResult.continues,
          DecoderState.mk (byte.toNat &&& 0x7) st.bytesSeen 3
            (if byte.toNat = 0xF0 then (0x90 : Byte) else (0x80 : Byte))
            (if byte.toNat = 0xF4 then (0x8F : Byte) else (0xBF : Byte)),
          ioQueue)
      else
        (Encoding.HandlerResult.error none, st, ioQueue)
    else
      if hout : byte.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < byte.toNat then
        (Encoding.HandlerResult.error none, DecoderState.initial, IoQueue.restore ioQueue byte)
      else
        if hcomp : st.bytesSeen + 1 = st.bytesNeeded then
          (Encoding.HandlerResult.items
              [⟨(st.codePoint <<< 6) ||| (byte.toNat &&& 0x3F),
                complete_le st byte hzero hout hcomp⟩],
            DecoderState.initial, ioQueue)
        else
          (Encoding.HandlerResult.continues,
            DecoderState.mk ((st.codePoint <<< 6) ||| (byte.toNat &&& 0x3F)) (st.bytesSeen + 1)
              st.bytesNeeded (0x80 : Byte) (0xBF : Byte),
            ioQueue)

/-! ### The handler's laws, one per numbered step or switch row -/

/-- DECODER [86515,90406) step 1: "If byte is end-of-queue and UTF-8 bytes
needed is not 0, then set UTF-8 bytes needed to 0 and return error." -/
theorem decoderHandler_endOfQueue_pending (st : DecoderState) (q : IoQueue Byte)
    (h : st.bytesNeeded ≠ 0) :
    decoderHandler st q Item.endOfQueue =
      (Encoding.HandlerResult.error none,
        DecoderState.mk st.codePoint st.bytesSeen 0 st.lowerBoundary st.upperBoundary, q) := by
  simp only [decoderHandler, dif_pos h]

/-- DECODER [86515,90406) step 2: "If byte is end-of-queue, then return
finished." -/
theorem decoderHandler_endOfQueue_idle (st : DecoderState) (q : IoQueue Byte)
    (h : st.bytesNeeded = 0) :
    decoderHandler st q Item.endOfQueue = (Encoding.HandlerResult.finished, st, q) := by
  simp only [decoderHandler, dif_neg (show ¬ (st.bytesNeeded ≠ 0) from fun hc => hc h)]

/-- DECODER [86515,90406) step 3, switch row "0x00 to 0x7F": "Return a code
point whose value is byte." -/
theorem decoderHandler_ascii (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded = 0) (hA : b.toNat ≤ 0x7F) :
    ∃ c : CodePoint,
      decoderHandler st q (Item.value b) = (Encoding.HandlerResult.items [c], st, q) ∧
        c.val = b.toNat := by
  refine ⟨⟨b.toNat, Nat.le_trans hA (by decide)⟩, ?_, rfl⟩
  simp only [decoderHandler, dif_pos hzero, dif_pos hA]

/-- DECODER [86515,90406) step 3, switch row "0xC2 to 0xDF": bytes needed 1,
code point `byte & 0x1F`, "the five least significant bits of byte". -/
theorem decoderHandler_lead_two (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded = 0) (h1 : 0xC2 ≤ b.toNat) (h2 : b.toNat ≤ 0xDF) :
    decoderHandler st q (Item.value b) =
      (Encoding.HandlerResult.continues,
        DecoderState.mk (b.toNat &&& 0x1F) st.bytesSeen 1 (0x80 : Byte) (0xBF : Byte), q) := by
  simp only [decoderHandler, dif_pos hzero, dif_neg (show ¬ b.toNat ≤ 0x7F by omega),
    dif_pos (show 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF from ⟨h1, h2⟩)]

/-- DECODER [86515,90406) step 3, switch row "0xE0 to 0xEF", with its boundary
table: "If byte is 0xE0, then set UTF-8 lower boundary to 0xA0. If byte is 0xED,
then set UTF-8 upper boundary to 0x9F." -/
theorem decoderHandler_lead_three (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded = 0) (h1 : 0xE0 ≤ b.toNat) (h2 : b.toNat ≤ 0xEF) :
    decoderHandler st q (Item.value b) =
      (Encoding.HandlerResult.continues,
        DecoderState.mk (b.toNat &&& 0xF) st.bytesSeen 2
          (if b.toNat = 0xE0 then (0xA0 : Byte) else (0x80 : Byte))
          (if b.toNat = 0xED then (0x9F : Byte) else (0xBF : Byte)), q) := by
  simp only [decoderHandler, dif_pos hzero, dif_neg (show ¬ b.toNat ≤ 0x7F by omega),
    dif_neg (show ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) by omega),
    dif_pos (show 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF from ⟨h1, h2⟩)]

/-- DECODER [86515,90406) step 3, switch row "0xF0 to 0xF4", with its boundary
table: "If byte is 0xF0, then set UTF-8 lower boundary to 0x90. If byte is 0xF4,
then set UTF-8 upper boundary to 0x8F." -/
theorem decoderHandler_lead_four (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded = 0) (h1 : 0xF0 ≤ b.toNat) (h2 : b.toNat ≤ 0xF4) :
    decoderHandler st q (Item.value b) =
      (Encoding.HandlerResult.continues,
        DecoderState.mk (b.toNat &&& 0x7) st.bytesSeen 3
          (if b.toNat = 0xF0 then (0x90 : Byte) else (0x80 : Byte))
          (if b.toNat = 0xF4 then (0x8F : Byte) else (0xBF : Byte)), q) := by
  simp only [decoderHandler, dif_pos hzero, dif_neg (show ¬ b.toNat ≤ 0x7F by omega),
    dif_neg (show ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) by omega),
    dif_neg (show ¬ (0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF) by omega),
    dif_pos (show 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4 from ⟨h1, h2⟩)]

/-- DECODER [86515,90406) step 3, switch row "Otherwise": every byte from 0x80
to 0xC1 and every byte from 0xF5 upward is an error at bytes-needed 0, with no
state change and no restore. -/
theorem decoderHandler_lead_error (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded = 0)
    (h : (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xC1) ∨ 0xF5 ≤ b.toNat) :
    decoderHandler st q (Item.value b) = (Encoding.HandlerResult.error none, st, q) := by
  simp only [decoderHandler, dif_pos hzero, dif_neg (show ¬ b.toNat ≤ 0x7F by omega),
    dif_neg (show ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) by omega),
    dif_neg (show ¬ (0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF) by omega),
    dif_neg (show ¬ (0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4) by omega)]

/-- DECODER [86515,90406) step 4: "If byte is not in the range UTF-8 lower
boundary to UTF-8 upper boundary, inclusive: Set UTF-8 code point, UTF-8 bytes
needed, and UTF-8 bytes seen to 0, set UTF-8 lower boundary to 0x80, and set
UTF-8 upper boundary to 0xBF. Restore byte to ioQueue. Return error." -/
theorem decoderHandler_out_of_boundary (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded ≠ 0)
    (hout : b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat) :
    decoderHandler st q (Item.value b) =
      (Encoding.HandlerResult.error none, DecoderState.initial, IoQueue.restore q b) := by
  simp only [decoderHandler, dif_neg hzero, dif_pos hout]

/-- DECODER [86515,90406) steps 5 to 8: reset the boundaries to 0x80 and 0xBF,
shift the accumulator left by six and take the byte's six least significant
bits, increase bytes seen by one, and continue while more bytes are needed. -/
theorem decoderHandler_accumulate (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded ≠ 0) (hlo : st.lowerBoundary.toNat ≤ b.toNat)
    (hhi : b.toNat ≤ st.upperBoundary.toNat) (hne : st.bytesSeen + 1 ≠ st.bytesNeeded) :
    decoderHandler st q (Item.value b) =
      (Encoding.HandlerResult.continues,
        DecoderState.mk ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) (st.bytesSeen + 1)
          st.bytesNeeded (0x80 : Byte) (0xBF : Byte), q) := by
  simp only [decoderHandler, dif_neg hzero,
    dif_neg (show ¬ (b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat) by
      omega),
    dif_neg hne]

/-- DECODER [86515,90406) steps 9 to 11: "Let codePoint be UTF-8 code point. Set
UTF-8 code point, UTF-8 bytes needed, and UTF-8 bytes seen to 0. Return a code
point whose value is codePoint." Step 5 has already reset the boundaries, so the
state returned is the initial state. -/
theorem decoderHandler_complete (st : DecoderState) (q : IoQueue Byte) (b : Byte)
    (hzero : st.bytesNeeded ≠ 0) (hlo : st.lowerBoundary.toNat ≤ b.toNat)
    (hhi : b.toNat ≤ st.upperBoundary.toNat) (hcomp : st.bytesSeen + 1 = st.bytesNeeded) :
    ∃ c : CodePoint,
      decoderHandler st q (Item.value b) =
          (Encoding.HandlerResult.items [c], DecoderState.initial, q) ∧
        c.val = (st.codePoint <<< 6) ||| (b.toNat &&& 0x3F) := by
  have hout : ¬ (b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat) := by omega
  refine ⟨⟨(st.codePoint <<< 6) ||| (b.toNat &&& 0x3F),
    complete_le st b hzero hout hcomp⟩, ?_, rfl⟩
  simp only [decoderHandler, dif_neg hzero, dif_neg hout, dif_pos hcomp]

/-- The decoder never supplies a code point with its error: only an encoder
does, for step 7's "html" arm of PROCI [15509,17620) and step 3 of ORFAILENC
[51167,53203). -/
theorem decoderHandler_error_none (st : DecoderState) (q : IoQueue Byte) (item : Item Byte)
    (c : CodePoint) :
    (decoderHandler st q item).1 ≠ Encoding.HandlerResult.error (some c) := by
  match item with
  | Item.endOfQueue =>
    by_cases h : st.bytesNeeded = 0
    · rw [decoderHandler_endOfQueue_idle st q h]; exact fun hc => by cases hc
    · rw [decoderHandler_endOfQueue_pending st q h]; exact fun hc => by cases hc
  | Item.value b =>
    by_cases hzero : st.bytesNeeded = 0
    · by_cases hA : b.toNat ≤ 0x7F
      · obtain ⟨d, hd, _⟩ := decoderHandler_ascii st q b hzero hA
        rw [hd]; exact fun hc => by cases hc
      · by_cases h2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
        · rw [decoderHandler_lead_two st q b hzero h2.1 h2.2]; exact fun hc => by cases hc
        · by_cases h3 : 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF
          · rw [decoderHandler_lead_three st q b hzero h3.1 h3.2]; exact fun hc => by cases hc
          · by_cases h4 : 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4
            · rw [decoderHandler_lead_four st q b hzero h4.1 h4.2]; exact fun hc => by cases hc
            · rw [decoderHandler_lead_error st q b hzero (by omega)]
              exact fun hc => by cases hc
    · by_cases hout : b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat
      · rw [decoderHandler_out_of_boundary st q b hzero hout]; exact fun hc => by cases hc
      · by_cases hcomp : st.bytesSeen + 1 = st.bytesNeeded
        · obtain ⟨d, hd, _⟩ :=
            decoderHandler_complete st q b hzero (by omega) (by omega) hcomp
          rw [hd]; exact fun hc => by cases hc
        · rw [decoderHandler_accumulate st q b hzero (by omega) (by omega) hcomp]
          exact fun hc => by cases hc

/-- The decoder never returns a surrogate, which is what step 6.1 of PROCI
[15509,17620) asserts: "Assert: encoderDecoder is not a decoder instance or
result does not contain any surrogates." It is a theorem of the 0xED
upper-boundary row through the carrier's invariant, not a typing assumption. -/
theorem decoderHandler_items_isScalarValue (st : DecoderState) (q : IoQueue Byte)
    (item : Item Byte) (out : List CodePoint) (_hn : st.bytesNeeded ≤ 3)
    (_hc : st.codePoint ≤ 0x10FFFF)
    (h : (decoderHandler st q item).1 = Encoding.HandlerResult.items out) :
    out.all CodePoint.isScalarValue = true := by
  match item with
  | Item.endOfQueue =>
    by_cases hz : st.bytesNeeded = 0
    · rw [decoderHandler_endOfQueue_idle st q hz] at h; exact absurd h (by simp)
    · rw [decoderHandler_endOfQueue_pending st q hz] at h; exact absurd h (by simp)
  | Item.value b =>
    by_cases hzero : st.bytesNeeded = 0
    · by_cases hA : b.toNat ≤ 0x7F
      · obtain ⟨d, hd, hdv⟩ := decoderHandler_ascii st q b hzero hA
        rw [hd] at h
        have : out = [d] := by
          have := congrArg (fun r => match r with
            | Encoding.HandlerResult.items l => l
            | _ => ([] : List CodePoint)) h
          exact this.symm
        rw [this, List.all_cons, List.all_nil, Bool.and_true]
        rw [CodePoint.isScalarValue, CodePoint.isSurrogate, CodePoint.isLeadingSurrogate,
          CodePoint.isTrailingSurrogate, CodePoint.inRange, CodePoint.inRange, hdv]
        have : b.toNat ≤ 0x7F := hA
        simp only [decide_eq_false (show ¬ (0xD800 ≤ b.toNat ∧ b.toNat ≤ 0xDBFF) by omega),
          decide_eq_false (show ¬ (0xDC00 ≤ b.toNat ∧ b.toNat ≤ 0xDFFF) by omega)]
        rfl
      · by_cases h2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
        · rw [decoderHandler_lead_two st q b hzero h2.1 h2.2] at h; exact absurd h (by simp)
        · by_cases h3 : 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF
          · rw [decoderHandler_lead_three st q b hzero h3.1 h3.2] at h; exact absurd h (by simp)
          · by_cases h4 : 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4
            · rw [decoderHandler_lead_four st q b hzero h4.1 h4.2] at h
              exact absurd h (by simp)
            · rw [decoderHandler_lead_error st q b hzero (by omega)] at h
              exact absurd h (by simp)
    · by_cases hout : b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat
      · rw [decoderHandler_out_of_boundary st q b hzero hout] at h; exact absurd h (by simp)
      · by_cases hcomp : st.bytesSeen + 1 = st.bytesNeeded
        · obtain ⟨d, hd, hdv⟩ :=
            decoderHandler_complete st q b hzero (by omega) (by omega) hcomp
          rw [hd] at h
          have hout' : out = [d] := by
            have := congrArg (fun r => match r with
              | Encoding.HandlerResult.items l => l
              | _ => ([] : List CodePoint)) h
            exact this.symm
          have hns := complete_scalar st b hzero hout hcomp
          rw [hout', List.all_cons, List.all_nil, Bool.and_true]
          rw [CodePoint.isScalarValue, CodePoint.isSurrogate, CodePoint.isLeadingSurrogate,
            CodePoint.isTrailingSurrogate, CodePoint.inRange, CodePoint.inRange, hdv]
          simp only [decide_eq_false (show ¬ (0xD800 ≤ ((st.codePoint <<< 6) |||
              (b.toNat &&& 0x3F)) ∧ ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) ≤ 0xDBFF) by
              omega),
            decide_eq_false (show ¬ (0xDC00 ≤ ((st.codePoint <<< 6) |||
              (b.toNat &&& 0x3F)) ∧ ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) ≤ 0xDFFF) by
              omega)]
          rfl
        · rw [decoderHandler_accumulate st q b hzero (by omega) (by omega) hcomp] at h
          exact absurd h (by simp)

/-! ### Processing an item and processing a queue

PROCI [15509,17620) and PROCQ [14785,15508), specialized to UTF-8's decoder. -/

/-- PROCI [15509,17620) specialized to UTF-8's decoder. The three assertions of
steps 1 to 3 hold by construction: the mode is a `DecoderErrorMode` so it is
never "html", the instance is a decoder so it is never asked for "replacement"
as an encoder, and the surrogate assertion is an encoder-side assertion. Step 5
pushes `end-of-queue`, step 6 pushes the items, step 7 switches on the mode and
step 8 returns `continue`. -/
def processItem (mode : Encoding.DecoderErrorMode) (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (item : Item Byte) :
    Encoding.HandlerResult CodePoint × DecoderState × IoQueue Byte × IoQueue CodePoint :=
  match decoderHandler st input item with
  | (Encoding.HandlerResult.finished, st', input') =>
    (Encoding.HandlerResult.finished, st', input', IoQueue.push output Item.endOfQueue)
  | (Encoding.HandlerResult.items out, st', input') =>
    (Encoding.HandlerResult.continues, st', input',
      IoQueue.pushItems output (out.map Item.value))
  | (Encoding.HandlerResult.error c, st', input') =>
    match mode with
    | Encoding.DecoderErrorMode.replacement =>
      (Encoding.HandlerResult.continues, st', input',
        IoQueue.push output (Item.value replacementCharacter.val))
    | Encoding.DecoderErrorMode.fatal =>
      (Encoding.HandlerResult.error c, st', input', output)
  | (Encoding.HandlerResult.continues, st', input') =>
    (Encoding.HandlerResult.continues, st', input', output)

/-- PROCQ [14785,15508): "While true: Let result be the result of processing an
item with the result of reading from input …; If result is not continue, then
return result." The `While true` is fuel-bounded exactly as
`Whatwg.Infra.ByteSequence.isPrefixLoop` is, and the first component is `none`
when the fuel runs out — a live frontier and never an error (DB-07). -/
def processQueue : Encoding.DecoderErrorMode → DecoderState → IoQueue Byte →
    IoQueue CodePoint → Nat →
      Option (Encoding.HandlerResult CodePoint) × DecoderState × IoQueue Byte ×
        IoQueue CodePoint
  | _, st, input, output, 0 => (none, st, input, output)
  | mode, st, input, output, fuel + 1 =>
    match IoQueue.read input with
    | none => (none, st, input, output)
    | some (item, input') =>
      match processItem mode st input' output item with
      | (Encoding.HandlerResult.continues, st', input'', output') =>
        processQueue mode st' input'' output' fuel
      | (result, st', input'', output') => (some result, st', input'', output')

/-- The fuel that always suffices. Step 4.2 of DECODER [86515,90406) restores a
byte, so the queue's length alone is not a decreasing measure; `2 × length + 1`
is, because a restore happens only together with a reset of "UTF-8 bytes needed"
to 0 and the `bytesNeeded = 0` branch never restores. -/
def processQueueFuel (input : IoQueue Byte) : Nat := 2 * input.length + 1

/-- The fuel of PROCQ [14785,15508). -/
theorem processQueueFuel_eq (q : IoQueue Byte) : processQueueFuel q = 2 * q.length + 1 := rfl

private def runMeasure (st : DecoderState) (input : IoQueue Byte) : Nat :=
  2 * input.length + (if st.bytesNeeded = 0 then 0 else 1)

private theorem runMeasure_le (st : DecoderState) (input : IoQueue Byte) :
    runMeasure st input ≤ 2 * input.length + 1 := by
  rw [runMeasure]; split <;> omega

private theorem runMeasure_ge (st : DecoderState) (input : IoQueue Byte) :
    2 * input.length ≤ runMeasure st input := by
  rw [runMeasure]; split <;> omega

private theorem runMeasure_of_zero (st : DecoderState) (input : IoQueue Byte)
    (h : st.bytesNeeded = 0) : runMeasure st input = 2 * input.length := by
  rw [runMeasure, if_pos h, Nat.add_zero]

private theorem runMeasure_of_pos (st : DecoderState) (input : IoQueue Byte)
    (h : st.bytesNeeded ≠ 0) : runMeasure st input = 2 * input.length + 1 := by
  rw [runMeasure, if_neg h]

private theorem initial_bytesNeeded : DecoderState.initial.bytesNeeded = 0 := rfl

private theorem processItem_carries (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (item : Item Byte) :
    (processItem mode st input output item).2.1 = (decoderHandler st input item).2.1 ∧
      (processItem mode st input output item).2.2.1 = (decoderHandler st input item).2.2 := by
  simp only [processItem]
  generalize decoderHandler st input item = d
  obtain ⟨r, st', q'⟩ := d
  cases r with
  | finished => exact ⟨rfl, rfl⟩
  | items out => exact ⟨rfl, rfl⟩
  | error c => cases mode <;> exact ⟨rfl, rfl⟩
  | continues => exact ⟨rfl, rfl⟩

private theorem processItem_finished_result (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (item : Item Byte)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.finished) :
    (processItem mode st input output item).1 = Encoding.HandlerResult.finished := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h
  subst h
  rfl

/-- A value item either leaves the input queue alone, or is restored to it by
step 4.2 of DECODER [86515,90406) — and a restore happens only from a pending
state and always resets "UTF-8 bytes needed" to 0. That is the whole content of
the fuel bound. -/
private theorem handler_value_progress (st : DecoderState) (q : IoQueue Byte) (b : Byte) :
    (decoderHandler st q (Item.value b)).2.2 = q ∨
      (st.bytesNeeded ≠ 0 ∧ (decoderHandler st q (Item.value b)).2.2 = IoQueue.restore q b ∧
        (decoderHandler st q (Item.value b)).2.1.bytesNeeded = 0) := by
  by_cases hzero : st.bytesNeeded = 0
  · by_cases hA : b.toNat ≤ 0x7F
    · obtain ⟨d, hd, _⟩ := decoderHandler_ascii st q b hzero hA
      exact Or.inl (by rw [hd])
    · by_cases h2 : 0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF
      · exact Or.inl (by rw [decoderHandler_lead_two st q b hzero h2.1 h2.2])
      · by_cases h3 : 0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF
        · exact Or.inl (by rw [decoderHandler_lead_three st q b hzero h3.1 h3.2])
        · by_cases h4 : 0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4
          · exact Or.inl (by rw [decoderHandler_lead_four st q b hzero h4.1 h4.2])
          · exact Or.inl (by rw [decoderHandler_lead_error st q b hzero (by omega)])
  · by_cases hout : b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat
    · refine Or.inr ⟨hzero, ?_, ?_⟩
      · rw [decoderHandler_out_of_boundary st q b hzero hout]
      · rw [decoderHandler_out_of_boundary st q b hzero hout]
        exact initial_bytesNeeded
    · by_cases hcomp : st.bytesSeen + 1 = st.bytesNeeded
      · obtain ⟨d, hd, _⟩ := decoderHandler_complete st q b hzero (by omega) (by omega) hcomp
        exact Or.inl (by rw [hd])
      · exact Or.inl (by rw [decoderHandler_accumulate st q b hzero (by omega) (by omega) hcomp])

private theorem step_decreases (mode : Encoding.DecoderErrorMode) (st st' : DecoderState)
    (input input' input'' : IoQueue Byte) (output output' : IoQueue CodePoint)
    (item : Item Byte) (hread : IoQueue.read input = some (item, input'))
    (hproc : processItem mode st input' output item =
      (Encoding.HandlerResult.continues, st', input'', output')) :
    runMeasure st' input'' < runMeasure st input := by
  have hst : st' = (decoderHandler st input' item).2.1 := by
    rw [← (processItem_carries mode st input' output item).1, hproc]
  have hin : input'' = (decoderHandler st input' item).2.2 := by
    rw [← (processItem_carries mode st input' output item).2, hproc]
  match item with
  | Item.endOfQueue =>
    have hq : input' = input := by
      match input with
      | [] => rw [IoQueue.read_nil] at hread; simp at hread
      | Item.endOfQueue :: rest =>
        rw [IoQueue.read_endOfQueue] at hread
        simp only [Option.some.injEq, Prod.mk.injEq] at hread
        exact hread.2.symm
      | Item.value a :: rest =>
        rw [IoQueue.read_value] at hread
        simp at hread
    by_cases hzero : st.bytesNeeded = 0
    · have hfin := processItem_finished_result mode st input' output Item.endOfQueue
        (by rw [decoderHandler_endOfQueue_idle st input' hzero])
      rw [hproc] at hfin
      exact absurd hfin (by simp)
    · rw [decoderHandler_endOfQueue_pending st input' hzero] at hst hin
      simp only at hst hin
      have hnb : st'.bytesNeeded = 0 := by
        rw [hst]
        exact (mk_fields st.codePoint st.bytesSeen 0 st.lowerBoundary st.upperBoundary
          (Or.inl rfl)).2.2.1
      rw [runMeasure_of_zero st' input'' hnb, runMeasure_of_pos st input hzero, hin, hq]
      omega
  | Item.value b =>
    have hq : input = Item.value b :: input' := by
      match input with
      | [] => rw [IoQueue.read_nil] at hread; simp at hread
      | Item.endOfQueue :: rest =>
        rw [IoQueue.read_endOfQueue] at hread
        simp at hread
      | Item.value a :: rest =>
        rw [IoQueue.read_value] at hread
        simp only [Option.some.injEq, Prod.mk.injEq, Item.value.injEq] at hread
        rw [hread.1, hread.2]
    have hlen : input.length = input'.length + 1 := by rw [hq]; rfl
    rcases handler_value_progress st input' b with hkeep | ⟨hpos, hres, hnb⟩
    · rw [hkeep] at hin
      have h1 := runMeasure_le st' input''
      have h2 := runMeasure_ge st input
      rw [hin]
      rw [hin] at h1
      omega
    · rw [hres] at hin
      have hnb' : st'.bytesNeeded = 0 := by rw [hst]; exact hnb
      have hl : input''.length = input.length := by
        rw [hin, IoQueue.restore, List.length_cons, hlen]
      rw [runMeasure_of_zero st' input'' hnb', runMeasure_of_pos st input hpos, hl]
      omega

private theorem processQueue_succ (mode : Encoding.DecoderErrorMode) :
    ∀ (fuel : Nat) (st : DecoderState) (input : IoQueue Byte) (output : IoQueue CodePoint),
      runMeasure st input ≤ fuel →
        processQueue mode st input output (fuel + 1) = processQueue mode st input output fuel
  | 0, st, input, output, h => by
    have hlen : input.length = 0 := by
      have := runMeasure_ge st input
      omega
    have hnil : input = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hnil]
    rfl
  | fuel + 1, st, input, output, h => by
    show (match IoQueue.read input with
        | none => (none, st, input, output)
        | some (item, input') =>
          match processItem mode st input' output item with
          | (Encoding.HandlerResult.continues, st', input'', output') =>
            processQueue mode st' input'' output' (fuel + 1)
          | (result, st', input'', output') => (some result, st', input'', output')) =
      (match IoQueue.read input with
        | none => (none, st, input, output)
        | some (item, input') =>
          match processItem mode st input' output item with
          | (Encoding.HandlerResult.continues, st', input'', output') =>
            processQueue mode st' input'' output' fuel
          | (result, st', input'', output') => (some result, st', input'', output'))
    match hread : IoQueue.read input with
    | none => rfl
    | some (item, input') =>
      show (match processItem mode st input' output item with
          | (Encoding.HandlerResult.continues, st', input'', output') =>
            processQueue mode st' input'' output' (fuel + 1)
          | (result, st', input'', output') => (some result, st', input'', output')) =
        (match processItem mode st input' output item with
          | (Encoding.HandlerResult.continues, st', input'', output') =>
            processQueue mode st' input'' output' fuel
          | (result, st', input'', output') => (some result, st', input'', output'))
      match hproc : processItem mode st input' output item with
      | (Encoding.HandlerResult.continues, st', input'', output') =>
        have hdec :=
          step_decreases mode st st' input input' input'' output output' item hread hproc
        exact processQueue_succ mode fuel st' input'' output' (by omega)
      | (Encoding.HandlerResult.finished, st', input'', output') => rfl
      | (Encoding.HandlerResult.items out, st', input'', output') => rfl
      | (Encoding.HandlerResult.error c, st', input'', output') => rfl

private theorem processQueue_add (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (f : Nat)
    (h : runMeasure st input ≤ f) :
    ∀ k : Nat, processQueue mode st input output (f + k) = processQueue mode st input output f
  | 0 => rfl
  | k + 1 => by
    rw [show f + (k + 1) = (f + k) + 1 from rfl,
      processQueue_succ mode (f + k) st input output (by omega),
      processQueue_add mode st input output f h k]

/-- The `While true` of PROCQ [14785,15508) terminates on every immediate queue,
and `processQueueFuel` is enough fuel: above it the result no longer depends on
the fuel. -/
theorem processQueue_fuel_stable (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat)
    (h : processQueueFuel input ≤ fuel) :
    processQueue mode st input output fuel =
      processQueue mode st input output (processQueueFuel input) := by
  have hm : runMeasure st input ≤ processQueueFuel input := by
    rw [processQueueFuel]; exact runMeasure_le st input
  have hsplit : fuel = processQueueFuel input + (fuel - processQueueFuel input) := by omega
  rw [hsplit, processQueue_add mode st input output _ hm]

/-- PROCI [15509,17620) step 7's "replacement" arm: "Push U+FFFD (�) to
output." -/
theorem processItem_replacement (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (item : Item Byte)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.error none) :
    (processItem Encoding.DecoderErrorMode.replacement st input output item).2.2.2 =
      IoQueue.push output (Item.value replacementCharacter.val) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h
  subst h
  rfl

/-- PROCI [15509,17620) step 7's "fatal" arm: "Return result." Nothing is
pushed. -/
theorem processItem_fatal (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (item : Item Byte)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.error none) :
    processItem Encoding.DecoderErrorMode.fatal st input output item =
      (Encoding.HandlerResult.error none, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2, output) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

/-- PROCI [15509,17620) step 5: "If result is finished: Push end-of-queue to
output." -/
theorem processItem_finished (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (h : st.bytesNeeded = 0) :
    (processItem mode st input output Item.endOfQueue).2.2.2 =
      IoQueue.push output Item.endOfQueue := by
  simp only [processItem, decoderHandler_endOfQueue_idle st input h]

/-! ### Unfolding lemmas for the run

Private step lemmas that turn one iteration of PROCQ [14785,15508) into a
handler transition. Every law below and every round trip is chained from
them. -/

private theorem processItem_of_finished (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (item : Item Byte)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.finished) :
    processItem mode st input output item =
      (Encoding.HandlerResult.finished, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2, IoQueue.push output Item.endOfQueue) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

private theorem processItem_of_items (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (item : Item Byte)
    (out : List CodePoint) (h : (decoderHandler st input item).1 =
      Encoding.HandlerResult.items out) :
    processItem mode st input output item =
      (Encoding.HandlerResult.continues, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2,
        IoQueue.pushItems output (out.map Item.value)) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

private theorem processItem_of_error_replacement (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (item : Item Byte) (c : Option CodePoint)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.error c) :
    processItem Encoding.DecoderErrorMode.replacement st input output item =
      (Encoding.HandlerResult.continues, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2,
        IoQueue.push output (Item.value replacementCharacter.val)) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

private theorem processItem_of_error_fatal (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (item : Item Byte) (c : Option CodePoint)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.error c) :
    processItem Encoding.DecoderErrorMode.fatal st input output item =
      (Encoding.HandlerResult.error c, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2, output) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

private theorem processQueue_succ_eq (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat) :
    processQueue mode st input output (fuel + 1) =
      (match IoQueue.read input with
        | none => (none, st, input, output)
        | some (item, input') =>
          match processItem mode st input' output item with
          | (Encoding.HandlerResult.continues, st', input'', output') =>
            processQueue mode st' input'' output' fuel
          | (result, st', input'', output') => (some result, st', input'', output')) := rfl

private theorem processQueue_step (mode : Encoding.DecoderErrorMode) (st st' : DecoderState)
    (input input' input'' : IoQueue Byte) (output output' : IoQueue CodePoint) (fuel : Nat)
    (item : Item Byte) (hread : IoQueue.read input = some (item, input'))
    (hproc : processItem mode st input' output item =
      (Encoding.HandlerResult.continues, st', input'', output')) :
    processQueue mode st input output (fuel + 1) =
      processQueue mode st' input'' output' fuel := by
  simp only [processQueue_succ_eq, hread, hproc]

private theorem processQueue_stop (mode : Encoding.DecoderErrorMode) (st st' : DecoderState)
    (input input' input'' : IoQueue Byte) (output output' : IoQueue CodePoint) (fuel : Nat)
    (item : Item Byte) (result : Encoding.HandlerResult CodePoint)
    (hne : result ≠ Encoding.HandlerResult.continues)
    (hread : IoQueue.read input = some (item, input'))
    (hproc : processItem mode st input' output item = (result, st', input'', output')) :
    processQueue mode st input output (fuel + 1) = (some result, st', input'', output') := by
  simp only [processQueue_succ_eq, hread, hproc]

private theorem processItem_of_continues (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (item : Item Byte)
    (h : (decoderHandler st input item).1 = Encoding.HandlerResult.continues) :
    processItem mode st input output item =
      (Encoding.HandlerResult.continues, (decoderHandler st input item).2.1,
        (decoderHandler st input item).2.2, output) := by
  simp only [processItem]
  generalize hd : decoderHandler st input item = d at h ⊢
  obtain ⟨r, st', q'⟩ := d
  simp only at h ⊢
  subst h
  rfl

private theorem processQueue_read_none (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat)
    (hread : IoQueue.read input = none) :
    processQueue mode st input output (fuel + 1) = (none, st, input, output) := by
  simp only [processQueue_succ_eq, hread]

private theorem processQueue_of_finished (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat) (item : Item Byte)
    (input' : IoQueue Byte) (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.finished) :
    processQueue mode st input output (fuel + 1) =
      (some Encoding.HandlerResult.finished, (decoderHandler st input' item).2.1,
        (decoderHandler st input' item).2.2, IoQueue.push output Item.endOfQueue) := by
  simp only [processQueue_succ_eq, hread, processItem_of_finished mode st input' output item hh]

private theorem processQueue_of_items (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat) (item : Item Byte)
    (input' : IoQueue Byte) (out : List CodePoint)
    (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.items out) :
    processQueue mode st input output (fuel + 1) =
      processQueue mode (decoderHandler st input' item).2.1 (decoderHandler st input' item).2.2
        (IoQueue.pushItems output (out.map Item.value)) fuel := by
  simp only [processQueue_succ_eq, hread,
    processItem_of_items mode st input' output item out hh]

private theorem processQueue_of_continues (mode : Encoding.DecoderErrorMode) (st : DecoderState)
    (input : IoQueue Byte) (output : IoQueue CodePoint) (fuel : Nat) (item : Item Byte)
    (input' : IoQueue Byte) (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.continues) :
    processQueue mode st input output (fuel + 1) =
      processQueue mode (decoderHandler st input' item).2.1 (decoderHandler st input' item).2.2
        output fuel := by
  simp only [processQueue_succ_eq, hread, processItem_of_continues mode st input' output item hh]

private theorem processQueue_of_error_fatal (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (fuel : Nat) (item : Item Byte) (input' : IoQueue Byte)
    (c : Option CodePoint) (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.error c) :
    processQueue Encoding.DecoderErrorMode.fatal st input output (fuel + 1) =
      (some (Encoding.HandlerResult.error c), (decoderHandler st input' item).2.1,
        (decoderHandler st input' item).2.2, output) := by
  simp only [processQueue_succ_eq, hread, processItem_of_error_fatal st input' output item c hh]

private theorem processQueue_of_error_replacement (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint) (fuel : Nat) (item : Item Byte) (input' : IoQueue Byte)
    (c : Option CodePoint) (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.error c) :
    processQueue Encoding.DecoderErrorMode.replacement st input output (fuel + 1) =
      processQueue Encoding.DecoderErrorMode.replacement (decoderHandler st input' item).2.1
        (decoderHandler st input' item).2.2
        (IoQueue.push output (Item.value replacementCharacter.val)) fuel := by
  simp only [processQueue_succ_eq, hread,
    processItem_of_error_replacement st input' output item c hh]

private theorem convertTo_cons {α : Type} (a : α) (l : List α) :
    IoQueue.convertTo (a :: l) = Item.value a :: IoQueue.convertTo l := rfl

private theorem read_convertTo_cons {α : Type} (a : α) (l : List α) :
    IoQueue.read (IoQueue.convertTo (a :: l)) = some (Item.value a, IoQueue.convertTo l) := rfl

private theorem read_convertTo_nil {α : Type} :
    IoQueue.read (IoQueue.convertTo ([] : List α)) =
      some (Item.endOfQueue, IoQueue.convertTo ([] : List α)) := rfl

/-! ### The four hooks for standards

HOOKS [43782,45058): "The algorithms defined below (UTF-8 decode, UTF-8 decode
without BOM, UTF-8 decode without BOM or fail, and UTF-8 encode) are intended
for usage by other standards." -/

/-- DECODE [45059,45762): "Let buffer be the result of peeking three bytes from
ioQueue, converted to a byte sequence. If buffer is 0xEF 0xBB 0xBF, then read
three bytes from ioQueue. Process a queue with an instance of UTF-8's decoder,
ioQueue, output, and 'replacement'. Return output." Step 1 is stated over
`IoQueue.peekPrefix`, the zero-based reading of PEEK [7651,8447) that INFRA-R15
asks the operator to ratify. -/
def decodeQueue (ioQueue : IoQueue Byte) : IoQueue CodePoint :=
  let stripped :=
    if IoQueue.peekPrefix ioQueue 3 = bom then
      match IoQueue.readItems ioQueue 3 with
      | some (_, remaining) => remaining
      | none => ioQueue
    else ioQueue
  (processQueue Encoding.DecoderErrorMode.replacement DecoderState.initial stripped []
    (processQueueFuel stripped)).2.2.2

/-- NOBOM [45763,46180): "Process a queue with an instance of UTF-8's decoder,
ioQueue, output, and 'replacement'. Return output." -/
def decodeWithoutBomQueue (ioQueue : IoQueue Byte) : IoQueue CodePoint :=
  (processQueue Encoding.DecoderErrorMode.replacement DecoderState.initial ioQueue []
    (processQueueFuel ioQueue)).2.2.2

/-- ORFAIL [46181,46905): "Let potentialError be the result of processing a
queue with an instance of UTF-8's decoder, ioQueue, output, and 'fatal'. If
potentialError is an error, then return failure. Return output." Failure is
`none` (INFRA-R3). -/
def decodeWithoutBomOrFailQueue (ioQueue : IoQueue Byte) : Option (IoQueue CodePoint) :=
  match processQueue Encoding.DecoderErrorMode.fatal DecoderState.initial ioQueue []
      (processQueueFuel ioQueue) with
  | (some (Encoding.HandlerResult.error _), _, _, _) => none
  | (_, _, _, output) => some output

/-- DECODE [45059,45762) at the byte-sequence face, through TOQ [10286,10769)
and FROMQ [9982,10285). -/
def decode (input : ByteSequence) : List CodePoint :=
  IoQueue.convertFrom (decodeQueue (IoQueue.convertTo input))

/-- NOBOM [45763,46180) at the byte-sequence face. -/
def decodeWithoutBom (input : ByteSequence) : List CodePoint :=
  IoQueue.convertFrom (decodeWithoutBomQueue (IoQueue.convertTo input))

/-- ORFAIL [46181,46905) at the byte-sequence face. -/
def decodeWithoutBomOrFail (input : ByteSequence) : Option (List CodePoint) :=
  (decodeWithoutBomOrFailQueue (IoQueue.convertTo input)).map IoQueue.convertFrom

/-- DECODE [45059,45762) at the `JsString` face. -/
def decodeString (input : ByteSequence) : JsString :=
  JsString.ofCodePoints (decode input)

/-- NOBOM [45763,46180) at the `JsString` face. -/
def decodeWithoutBomString (input : ByteSequence) : JsString :=
  JsString.ofCodePoints (decodeWithoutBom input)

/-- ORFAIL [46181,46905) at the `JsString` face. -/
def decodeWithoutBomOrFailString (input : ByteSequence) : Option JsString :=
  (decodeWithoutBomOrFail input).map JsString.ofCodePoints

private def errorCountLoop : DecoderState → IoQueue Byte → Nat → Nat
  | _, _, 0 => 0
  | st, input, fuel + 1 =>
    match IoQueue.read input with
    | none => 0
    | some (item, input') =>
      (match (decoderHandler st input' item).1 with
        | Encoding.HandlerResult.error _ => 1
        | _ => 0) +
        (match processItem Encoding.DecoderErrorMode.replacement st input' [] item with
          | (Encoding.HandlerResult.continues, st', input'', _) => errorCountLoop st' input'' fuel
          | _ => 0)

/-- How many `error` results the replacement-mode run of PROCQ [14785,15508)
substituted a U+FFFD for. This is deliberately **not** the number of U+FFFD in
the output: U+FFFD is itself a scalar value with a well-formed encoding, so
`decodeWithoutBom [0xEF, 0xBF, 0xBD]` contains one U+FFFD and `errorCount` of it
is 0 (`INFRA-UTF8-CE-011`). -/
def errorCount (input : ByteSequence) : Nat :=
  errorCountLoop DecoderState.initial (IoQueue.convertTo input)
    (processQueueFuel (IoQueue.convertTo input))

/-- Whether the byte sequence is in the image of the UTF-8 encoder, which is
what ORFAIL [46181,46905) succeeds on. -/
def isWellFormed (input : ByteSequence) : Bool := (decodeWithoutBomOrFail input).isSome

private theorem errorCountLoop_succ_eq (st : DecoderState) (input : IoQueue Byte) (fuel : Nat) :
    errorCountLoop st input (fuel + 1) =
      (match IoQueue.read input with
        | none => 0
        | some (item, input') =>
          (match (decoderHandler st input' item).1 with
            | Encoding.HandlerResult.error _ => 1
            | _ => 0) +
            (match processItem Encoding.DecoderErrorMode.replacement st input' [] item with
              | (Encoding.HandlerResult.continues, st', input'', _) =>
                errorCountLoop st' input'' fuel
              | _ => 0)) := rfl

private theorem errorCountLoop_read_none (st : DecoderState) (input : IoQueue Byte) (fuel : Nat)
    (hread : IoQueue.read input = none) : errorCountLoop st input (fuel + 1) = 0 := by
  simp only [errorCountLoop_succ_eq, hread]

private theorem errorCountLoop_of_finished (st : DecoderState) (input : IoQueue Byte)
    (fuel : Nat) (item : Item Byte) (input' : IoQueue Byte)
    (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.finished) :
    errorCountLoop st input (fuel + 1) = 0 := by
  simp only [errorCountLoop_succ_eq, hread, hh,
    processItem_of_finished Encoding.DecoderErrorMode.replacement st input' [] item hh]

private theorem errorCountLoop_of_items (st : DecoderState) (input : IoQueue Byte) (fuel : Nat)
    (item : Item Byte) (input' : IoQueue Byte) (out : List CodePoint)
    (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.items out) :
    errorCountLoop st input (fuel + 1) =
      errorCountLoop (decoderHandler st input' item).2.1 (decoderHandler st input' item).2.2
        fuel := by
  simp only [errorCountLoop_succ_eq, hread, hh,
    processItem_of_items Encoding.DecoderErrorMode.replacement st input' [] item out hh,
    Nat.zero_add]

private theorem errorCountLoop_of_continues (st : DecoderState) (input : IoQueue Byte)
    (fuel : Nat) (item : Item Byte) (input' : IoQueue Byte)
    (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.continues) :
    errorCountLoop st input (fuel + 1) =
      errorCountLoop (decoderHandler st input' item).2.1 (decoderHandler st input' item).2.2
        fuel := by
  simp only [errorCountLoop_succ_eq, hread, hh,
    processItem_of_continues Encoding.DecoderErrorMode.replacement st input' [] item hh,
    Nat.zero_add]

private theorem errorCountLoop_of_error (st : DecoderState) (input : IoQueue Byte) (fuel : Nat)
    (item : Item Byte) (input' : IoQueue Byte) (c : Option CodePoint)
    (hread : IoQueue.read input = some (item, input'))
    (hh : (decoderHandler st input' item).1 = Encoding.HandlerResult.error c) :
    errorCountLoop st input (fuel + 1) =
      1 + errorCountLoop (decoderHandler st input' item).2.1
        (decoderHandler st input' item).2.2 fuel := by
  simp only [errorCountLoop_succ_eq, hread, hh,
    processItem_of_error_replacement st input' [] item c hh]

/-- The fatal run of PROCQ [14785,15508) reports an error exactly when the
replacement run substituted at least one U+FFFD. The two runs visit the same
states and the same input queues — `processItem`'s state and queue outputs do
not depend on the mode — so they part company only at the first `error`. -/
private theorem fatal_error_iff : ∀ (fuel : Nat) (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint),
      ((∃ c : Option CodePoint,
          (processQueue Encoding.DecoderErrorMode.fatal st input output fuel).1 =
            some (Encoding.HandlerResult.error c)) ↔ 0 < errorCountLoop st input fuel)
  | 0, st, input, output => by
    constructor
    · rintro ⟨c, hc⟩; exact absurd hc (by simp [processQueue])
    · intro hc; exact absurd hc (by simp [errorCountLoop])
  | fuel + 1, st, input, output => by
    cases hread : IoQueue.read input with
    | none =>
      rw [processQueue_read_none _ st input output fuel hread,
        errorCountLoop_read_none st input fuel hread]
      constructor
      · rintro ⟨c, hc⟩; exact absurd hc (by simp)
      · intro hc; exact absurd hc (by simp)
    | some p =>
      obtain ⟨item, input'⟩ := p
      cases hh : (decoderHandler st input' item).1 with
      | finished =>
        rw [processQueue_of_finished _ st input output fuel item input' hread hh,
          errorCountLoop_of_finished st input fuel item input' hread hh]
        constructor
        · rintro ⟨c, hc⟩; exact absurd hc (by simp)
        · intro hc; exact absurd hc (by simp)
      | items out =>
        rw [processQueue_of_items _ st input output fuel item input' out hread hh,
          errorCountLoop_of_items st input fuel item input' out hread hh]
        exact fatal_error_iff fuel _ _ _
      | continues =>
        rw [processQueue_of_continues _ st input output fuel item input' hread hh,
          errorCountLoop_of_continues st input fuel item input' hread hh]
        exact fatal_error_iff fuel _ _ _
      | error c =>
        rw [processQueue_of_error_fatal st input output fuel item input' c hread hh,
          errorCountLoop_of_error st input fuel item input' c hread hh]
        constructor
        · intro _; omega
        · intro _; exact ⟨c, rfl⟩

/-- Wherever no error is substituted, the two error modes of PROCI
[15509,17620) step 7 produce the same output: they part company only at an
`error`. -/
private theorem modes_agree : ∀ (fuel : Nat) (st : DecoderState) (input : IoQueue Byte)
    (output : IoQueue CodePoint), errorCountLoop st input fuel = 0 →
      (processQueue Encoding.DecoderErrorMode.fatal st input output fuel).2.2.2 =
        (processQueue Encoding.DecoderErrorMode.replacement st input output fuel).2.2.2
  | 0, _, _, _, _ => rfl
  | fuel + 1, st, input, output, h => by
    cases hread : IoQueue.read input with
    | none =>
      rw [processQueue_read_none _ st input output fuel hread,
        processQueue_read_none _ st input output fuel hread]
    | some p =>
      obtain ⟨item, input'⟩ := p
      cases hh : (decoderHandler st input' item).1 with
      | finished =>
        rw [processQueue_of_finished _ st input output fuel item input' hread hh,
          processQueue_of_finished _ st input output fuel item input' hread hh]
      | items out =>
        rw [processQueue_of_items _ st input output fuel item input' out hread hh,
          processQueue_of_items _ st input output fuel item input' out hread hh]
        rw [errorCountLoop_of_items st input fuel item input' out hread hh] at h
        exact modes_agree fuel _ _ _ h
      | continues =>
        rw [processQueue_of_continues _ st input output fuel item input' hread hh,
          processQueue_of_continues _ st input output fuel item input' hread hh]
        rw [errorCountLoop_of_continues st input fuel item input' hread hh] at h
        exact modes_agree fuel _ _ _ h
      | error c =>
        rw [errorCountLoop_of_error st input fuel item input' c hread hh] at h
        omega

private theorem decodeWithoutBomOrFailQueue_eq_none_iff (q : IoQueue Byte) :
    decodeWithoutBomOrFailQueue q = none ↔
      ∃ c : Option CodePoint,
        (processQueue Encoding.DecoderErrorMode.fatal DecoderState.initial q []
          (processQueueFuel q)).1 = some (Encoding.HandlerResult.error c) := by
  rw [decodeWithoutBomOrFailQueue]
  generalize processQueue Encoding.DecoderErrorMode.fatal DecoderState.initial q []
    (processQueueFuel q) = r
  obtain ⟨r1, st', q', out⟩ := r
  cases r1 with
  | none => simp
  | some hr =>
    cases hr with
    | error c => simp
    | finished => simp
    | items o => simp
    | continues => simp

private theorem decodeWithoutBomOrFailQueue_eq_some (q : IoQueue Byte)
    (out : IoQueue CodePoint) (h : decodeWithoutBomOrFailQueue q = some out) :
    out = (processQueue Encoding.DecoderErrorMode.fatal DecoderState.initial q []
      (processQueueFuel q)).2.2.2 := by
  rw [decodeWithoutBomOrFailQueue] at h
  generalize hr : processQueue Encoding.DecoderErrorMode.fatal DecoderState.initial q []
    (processQueueFuel q) = r at h ⊢
  obtain ⟨r1, st', q', o⟩ := r
  cases r1 with
  | none => simp only [Option.some.injEq] at h; exact h.symm
  | some hres =>
    cases hres with
    | error c => exact absurd h (by simp)
    | finished => simp only [Option.some.injEq] at h; exact h.symm
    | items l => simp only [Option.some.injEq] at h; exact h.symm
    | continues => simp only [Option.some.injEq] at h; exact h.symm

/-! ### The hooks' compositional laws -/

/-- NOBOM [45763,46180) at the byte-sequence face. -/
theorem decodeWithoutBom_eq (b : ByteSequence) :
    decodeWithoutBom b =
      IoQueue.convertFrom (decodeWithoutBomQueue (IoQueue.convertTo b)) := rfl

/-- DECODE [45059,45762) at the byte-sequence face. -/
theorem decode_eq (b : ByteSequence) :
    decode b = IoQueue.convertFrom (decodeQueue (IoQueue.convertTo b)) := rfl

/-- ORFAIL [46181,46905) at the byte-sequence face. -/
theorem decodeWithoutBomOrFail_eq (b : ByteSequence) :
    decodeWithoutBomOrFail b =
      (decodeWithoutBomOrFailQueue (IoQueue.convertTo b)).map IoQueue.convertFrom := rfl

/-- NOBOM [45763,46180) at the `JsString` face. -/
theorem decodeWithoutBomString_eq (b : ByteSequence) :
    decodeWithoutBomString b = JsString.ofCodePoints (decodeWithoutBom b) := rfl

/-- DECODE [45059,45762) at the `JsString` face. -/
theorem decodeString_eq (b : ByteSequence) :
    decodeString b = JsString.ofCodePoints (decode b) := rfl

/-- ORFAIL [46181,46905) at the `JsString` face. -/
theorem decodeWithoutBomOrFailString_eq (b : ByteSequence) :
    decodeWithoutBomOrFailString b =
      (decodeWithoutBomOrFail b).map JsString.ofCodePoints := rfl

/-! ### The failure set

ORFAIL [46181,46905). The fail mode returns `none` exactly when the replacement
mode substituted at least one U+FFFD for an `error`. This is *not* "when the
output contains U+FFFD": U+FFFD is a scalar value with a well-formed encoding,
so `errorCount` and not the output's contents is the right observation
(`INFRA-UTF8-CE-011`). -/

/-- ORFAIL [46181,46905) step 2 against PROCI [15509,17620) step 7's
"replacement" arm. -/
theorem decodeWithoutBomOrFail_eq_none_iff (b : ByteSequence) :
    decodeWithoutBomOrFail b = none ↔ 0 < errorCount b := by
  rw [decodeWithoutBomOrFail, Option.map_eq_none_iff, decodeWithoutBomOrFailQueue_eq_none_iff,
    errorCount]
  exact fatal_error_iff _ _ _ _

/-- The failure set is exactly where the replacement mode substitutes. -/
theorem errorCount_eq_zero_iff (b : ByteSequence) :
    errorCount b = 0 ↔ isWellFormed b = true := by
  constructor
  · intro h
    rw [isWellFormed]
    cases hd : decodeWithoutBomOrFail b with
    | none =>
      have hpos := (decodeWithoutBomOrFail_eq_none_iff b).mp hd
      omega
    | some v => rfl
  · intro h
    rcases Nat.eq_zero_or_pos (errorCount b) with h0 | hp
    · exact h0
    · have hnone := (decodeWithoutBomOrFail_eq_none_iff b).mpr hp
      rw [isWellFormed, hnone] at h
      exact absurd h (by simp)

/-- Wherever the fatal mode succeeds, the replacement mode gives the same
answer: the two modes differ only at an `error`. -/
theorem decodeWithoutBomOrFail_eq_some_imp (b : ByteSequence) (cs : List CodePoint)
    (h : decodeWithoutBomOrFail b = some cs) : decodeWithoutBom b = cs := by
  have hzero : errorCount b = 0 := by
    rcases Nat.eq_zero_or_pos (errorCount b) with h0 | hp
    · exact h0
    · rw [(decodeWithoutBomOrFail_eq_none_iff b).mpr hp] at h
      exact absurd h (by simp)
  rw [decodeWithoutBomOrFail] at h
  cases hq : decodeWithoutBomOrFailQueue (IoQueue.convertTo b) with
  | none => rw [hq] at h; exact absurd h (by simp)
  | some out =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hout := decodeWithoutBomOrFailQueue_eq_some (IoQueue.convertTo b) out hq
    rw [decodeWithoutBom, decodeWithoutBomQueue, ← h, hout]
    rw [modes_agree (processQueueFuel (IoQueue.convertTo b)) DecoderState.initial
      (IoQueue.convertTo b) [] hzero]

/-! ### The run over one encoded scalar value

The round trips are chained from one lemma: a run started in the initial state
over `encodeScalar s ++ rest` consumes exactly `encodeScalar s`, pushes `s`'s
code point, and comes back to the initial state. -/

private theorem initial_codePoint : DecoderState.initial.codePoint = 0 := rfl
private theorem initial_bytesSeen : DecoderState.initial.bytesSeen = 0 := rfl
private theorem initial_lower : DecoderState.initial.lowerBoundary = (0x80 : Byte) := rfl
private theorem initial_upper : DecoderState.initial.upperBoundary = (0xBF : Byte) := rfl

private theorem scalar_not_surrogate (s : ScalarValue) :
    s.val.val < 0xD800 ∨ 0xDFFF < s.val.val := by
  have hp : CodePoint.isSurrogate s.val = false := s.property
  rw [CodePoint.isSurrogate, CodePoint.isLeadingSurrogate, CodePoint.isTrailingSurrogate,
    CodePoint.inRange, CodePoint.inRange, Bool.or_eq_false_iff] at hp
  have h1 := of_decide_eq_false hp.1
  have h2 := of_decide_eq_false hp.2
  omega

private theorem processQueueFuel_convertTo (l : ByteSequence) :
    processQueueFuel (IoQueue.convertTo l) = 2 * List.length l + 3 := by
  rw [processQueueFuel, IoQueue.convertTo]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

private theorem pushItems_singleton (output : IoQueue CodePoint) (c : CodePoint) :
    IoQueue.pushItems output ([c].map Item.value) = IoQueue.push output (Item.value c) := rfl

private theorem run_scalar_one (mode : Encoding.DecoderErrorMode) (s : ScalarValue)
    (rest : ByteSequence) (output : IoQueue CodePoint) (h : s.val.val ≤ 0x7F) (fuel : Nat)
    (hfuel : 2 * List.length (encodeScalar s ++ rest) + 3 ≤ fuel) :
    processQueue mode DecoderState.initial
        (IoQueue.convertTo (encodeScalar s ++ rest)) output fuel =
      processQueue mode DecoderState.initial
        (IoQueue.convertTo rest) (IoQueue.push output (Item.value s.val))
        (processQueueFuel (IoQueue.convertTo rest)) := by
  rw [encodeScalar_ascii s h] at hfuel ⊢
  have hcat : ([UInt8.ofNat s.val.val] ++ rest) = UInt8.ofNat s.val.val :: rest := rfl
  rw [hcat] at hfuel ⊢
  rw [List.length_cons] at hfuel
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hb0 : (UInt8.ofNat s.val.val).toNat ≤ 0x7F := by rw [toNat_ofNat_lt (by omega)]; omega
  obtain ⟨c, hd, hcv⟩ := decoderHandler_ascii DecoderState.initial (IoQueue.convertTo rest)
    (UInt8.ofNat s.val.val) initial_bytesNeeded hb0
  have hh : (decoderHandler DecoderState.initial (IoQueue.convertTo rest)
      (Item.value (UInt8.ofNat s.val.val))).1 = Encoding.HandlerResult.items [c] := by rw [hd]
  rw [processQueue_of_items _ _ _ _ _ _ _ _ (read_convertTo_cons _ _) hh, hd]
  simp only
  have hcs : c = s.val := CodePoint.ext (by rw [hcv, toNat_ofNat_lt (by omega)])
  rw [hcs, pushItems_singleton]
  exact processQueue_fuel_stable _ _ _ _ _ (by rw [processQueueFuel_convertTo]; omega)

private theorem run_scalar_two (mode : Encoding.DecoderErrorMode) (s : ScalarValue)
    (rest : ByteSequence) (output : IoQueue CodePoint) (h1 : 0x80 ≤ s.val.val)
    (h2 : s.val.val ≤ 0x7FF) (fuel : Nat)
    (hfuel : 2 * List.length (encodeScalar s ++ rest) + 3 ≤ fuel) :
    processQueue mode DecoderState.initial
        (IoQueue.convertTo (encodeScalar s ++ rest)) output fuel =
      processQueue mode DecoderState.initial
        (IoQueue.convertTo rest) (IoQueue.push output (Item.value s.val))
        (processQueueFuel (IoQueue.convertTo rest)) := by
  rw [encodeScalar_two_eq s h1 h2] at hfuel ⊢
  have hcat : ([UInt8.ofNat (s.val.val / 64 + 0xC0), UInt8.ofNat (0x80 + s.val.val % 64)] ++
      rest) = UInt8.ofNat (s.val.val / 64 + 0xC0) ::
        UInt8.ofNat (0x80 + s.val.val % 64) :: rest := rfl
  rw [hcat] at hfuel ⊢
  rw [List.length_cons, List.length_cons] at hfuel
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 := ⟨fuel - 2, by omega⟩
  have hb0 : (UInt8.ofNat (s.val.val / 64 + 0xC0)).toNat = s.val.val / 64 + 0xC0 :=
    toNat_ofNat_lt (by omega)
  have hb1 : (UInt8.ofNat (0x80 + s.val.val % 64)).toNat = 0x80 + s.val.val % 64 :=
    toNat_ofNat_lt (by omega)
  -- step one: the lead byte
  have hlead := decoderHandler_lead_two DecoderState.initial
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (s.val.val / 64 + 0xC0)) initial_bytesNeeded (by rw [hb0]; omega)
    (by rw [hb0]; omega)
  have hhead : (decoderHandler DecoderState.initial
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (s.val.val / 64 + 0xC0)))).1 =
      Encoding.HandlerResult.continues := by rw [hlead]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead, hlead]
  simp only
  -- the state after the lead byte
  have hk : (UInt8.ofNat (s.val.val / 64 + 0xC0)).toNat &&& 0x1F = s.val.val / 64 := by
    rw [hb0, land_five]; omega
  have hinv : decoderInv (s.val.val / 64) DecoderState.initial.bytesSeen 1
      ((0x80 : Byte)).toNat ((0xBF : Byte)).toNat := by
    rw [initial_bytesSeen]
    refine Or.inr ⟨by omega, by omega, by decide, by decide, ?_, ?_⟩
    · rw [show 1 - 0 - 1 = 0 from rfl, Nat.pow_zero]
      have : ((0xBF : Byte)).toNat = 191 := rfl
      omega
    · left
      rw [show 1 - 0 - 1 = 0 from rfl, Nat.pow_zero]
      have : ((0xBF : Byte)).toNat = 191 := rfl
      omega
  rw [hk]
  obtain ⟨hcp, hseen, hneed, hlo, hhi⟩ := mk_fields (s.val.val / 64)
    DecoderState.initial.bytesSeen 1 (0x80 : Byte) (0xBF : Byte) hinv
  -- step two: the continuation byte completes the sequence
  obtain ⟨c, hd, hcv⟩ := decoderHandler_complete
    (DecoderState.mk (s.val.val / 64) DecoderState.initial.bytesSeen 1 (0x80 : Byte)
      (0xBF : Byte)) (IoQueue.convertTo rest) (UInt8.ofNat (0x80 + s.val.val % 64))
    (by rw [hneed]; omega) (by rw [hlo, hb1]; exact Nat.le_add_right _ _)
    (by rw [hhi, hb1]; have : ((0xBF : Byte)).toNat = 191 := rfl; omega)
    (by rw [hseen, hneed, initial_bytesSeen])
  have hh2 : (decoderHandler (DecoderState.mk (s.val.val / 64) DecoderState.initial.bytesSeen 1
      (0x80 : Byte) (0xBF : Byte)) (IoQueue.convertTo rest)
      (Item.value (UInt8.ofNat (0x80 + s.val.val % 64)))).1 =
      Encoding.HandlerResult.items [c] := by rw [hd]
  rw [processQueue_of_items _ _ _ _ _ _ _ _ (read_convertTo_cons _ _) hh2, hd]
  simp only
  have hcs : c = s.val := by
    refine CodePoint.ext ?_
    rw [hcv, hcp, hb1, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hcs, pushItems_singleton]
  exact processQueue_fuel_stable _ _ _ _ _ (by rw [processQueueFuel_convertTo]; omega)

private theorem run_scalar_three (mode : Encoding.DecoderErrorMode) (s : ScalarValue)
    (rest : ByteSequence) (output : IoQueue CodePoint) (h1 : 0x800 ≤ s.val.val)
    (h2 : s.val.val ≤ 0xFFFF) (fuel : Nat)
    (hfuel : 2 * List.length (encodeScalar s ++ rest) + 3 ≤ fuel) :
    processQueue mode DecoderState.initial
        (IoQueue.convertTo (encodeScalar s ++ rest)) output fuel =
      processQueue mode DecoderState.initial
        (IoQueue.convertTo rest) (IoQueue.push output (Item.value s.val))
        (processQueueFuel (IoQueue.convertTo rest)) := by
  have hns := scalar_not_surrogate s
  rw [encodeScalar_three_eq s h1 h2] at hfuel ⊢
  have hcat : ([UInt8.ofNat (s.val.val / 4096 + 0xE0), UInt8.ofNat (0x80 + s.val.val / 64 % 64),
      UInt8.ofNat (0x80 + s.val.val % 64)] ++ rest) =
      UInt8.ofNat (s.val.val / 4096 + 0xE0) :: UInt8.ofNat (0x80 + s.val.val / 64 % 64) ::
        UInt8.ofNat (0x80 + s.val.val % 64) :: rest := rfl
  rw [hcat] at hfuel ⊢
  rw [List.length_cons, List.length_cons, List.length_cons] at hfuel
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
  have hb0 : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = s.val.val / 4096 + 0xE0 :=
    toNat_ofNat_lt (by omega)
  have hb1 : (UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat = 0x80 + s.val.val / 64 % 64 :=
    toNat_ofNat_lt (by omega)
  have hb2 : (UInt8.ofNat (0x80 + s.val.val % 64)).toNat = 0x80 + s.val.val % 64 :=
    toNat_ofNat_lt (by omega)
  have hk : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat &&& 0xF = s.val.val / 4096 := by
    rw [hb0, land_four]; omega
  -- step one: the lead byte installs the boundary table
  have hlead := decoderHandler_lead_three DecoderState.initial
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 64 % 64) ::
      UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (s.val.val / 4096 + 0xE0)) initial_bytesNeeded (by rw [hb0]; omega)
    (by rw [hb0]; omega)
  have hhead : (decoderHandler DecoderState.initial
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 64 % 64) ::
        UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (s.val.val / 4096 + 0xE0)))).1 =
      Encoding.HandlerResult.continues := by rw [hlead]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead, hlead]
  simp only
  rw [hk, initial_bytesSeen]
  have hinv1 : decoderInv (s.val.val / 4096) 0 2
      ((if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte)
        else (0x80 : Byte))).toNat
      ((if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte)
        else (0xBF : Byte))).toNat := by
    refine Or.inr ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
    · by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0
      · rw [if_pos he]; exact (by decide : (0x80 : Nat) ≤ ((0xA0 : Byte)).toNat)
      · rw [if_neg he]; exact (by decide : (0x80 : Nat) ≤ ((0x80 : Byte)).toNat)
    · by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED
      · rw [if_pos he]; exact (by decide : ((0x9F : Byte)).toNat ≤ 0xBF)
      · rw [if_neg he]; exact (by decide : ((0xBF : Byte)).toNat ≤ 0xBF)
    · rw [show (2 : Nat) - 0 - 1 = 1 from rfl, Nat.pow_one]
      by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED
      · rw [if_pos he, hb0] at *
        show s.val.val / 4096 * 64 * 64 + (159 - 0x80) * 64 + (64 - 1) ≤ 0x10FFFF
        omega
      · rw [if_neg he]
        show s.val.val / 4096 * 64 * 64 + (191 - 0x80) * 64 + (64 - 1) ≤ 0x10FFFF
        omega
    · rw [show (2 : Nat) - 0 - 1 = 1 from rfl, Nat.pow_one]
      by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED
      · left
        rw [if_pos he, hb0] at *
        show s.val.val / 4096 * 64 * 64 + (159 - 0x80) * 64 + (64 - 1) < 0xD800
        omega
      · rw [if_neg he]
        rw [hb0] at he
        by_cases he0 : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0
        · rw [if_pos he0]
          rw [hb0] at he0
          left
          show s.val.val / 4096 * 64 * 64 + (191 - 0x80) * 64 + (64 - 1) < 0xD800
          omega
        · rw [if_neg he0]
          rw [hb0] at he0
          rcases Nat.lt_or_ge (s.val.val / 4096) 14 with hkk | hkk
          · left
            show s.val.val / 4096 * 64 * 64 + (191 - 0x80) * 64 + (64 - 1) < 0xD800
            omega
          · right
            show 0xDFFF < s.val.val / 4096 * 64 * 64 + (128 - 0x80) * 64
            omega
  obtain ⟨hcp1, hseen1, hneed1, hlo1, hhi1⟩ := mk_fields (s.val.val / 4096) 0 2
    (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte) else (0x80 : Byte))
    (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte) else (0xBF : Byte))
    hinv1
  -- step two: the first continuation byte accumulates
  have hlow : (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte)
      else (0x80 : Byte)).toNat ≤ (UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat := by
    rw [hb1]
    by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0
    · rw [if_pos he, hb0] at *
      show (0xA0 : Nat) ≤ 0x80 + s.val.val / 64 % 64
      omega
    · rw [if_neg he]
      show (0x80 : Nat) ≤ 0x80 + s.val.val / 64 % 64
      omega
  have hhigh : (UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat ≤
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte)
        else (0xBF : Byte)).toNat := by
    rw [hb1]
    by_cases he : (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED
    · rw [if_pos he, hb0] at *
      show 0x80 + s.val.val / 64 % 64 ≤ (0x9F : Nat)
      omega
    · rw [if_neg he]
      show 0x80 + s.val.val / 64 % 64 ≤ (0xBF : Nat)
      omega
  have hacc := decoderHandler_accumulate
    (DecoderState.mk (s.val.val / 4096) 0 2
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte)
        else (0xBF : Byte)))
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (0x80 + s.val.val / 64 % 64)) (by rw [hneed1]; omega)
    (by rw [hlo1]; exact hlow) (by rw [hhi1]; exact hhigh) (by rw [hseen1, hneed1]; omega)
  have hhead2 : (decoderHandler (DecoderState.mk (s.val.val / 4096) 0 2
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte)
        else (0xBF : Byte)))
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (0x80 + s.val.val / 64 % 64)))).1 =
      Encoding.HandlerResult.continues := by rw [hacc]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead2, hacc]
  simp only
  have hmid : ((DecoderState.mk (s.val.val / 4096) 0 2
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xE0 then (0xA0 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 4096 + 0xE0)).toNat = 0xED then (0x9F : Byte)
        else (0xBF : Byte))).codePoint <<< 6) |||
      ((UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat &&& 0x3F) = s.val.val / 64 := by
    rw [hcp1, hb1, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hmid, hseen1, hneed1]
  have hinv2 : decoderInv (s.val.val / 64) (0 + 1) 2 ((0x80 : Byte)).toNat
      ((0xBF : Byte)).toNat := by
    refine Or.inr ⟨by omega, by omega, by decide, by decide, ?_, ?_⟩
    · rw [show (2 : Nat) - (0 + 1) - 1 = 0 from rfl, Nat.pow_zero]
      show s.val.val / 64 * 64 * 1 + (191 - 0x80) * 1 + (1 - 1) ≤ 0x10FFFF
      omega
    · rw [show (2 : Nat) - (0 + 1) - 1 = 0 from rfl, Nat.pow_zero]
      rcases hns with hlt | hgt
      · left
        show s.val.val / 64 * 64 * 1 + (191 - 0x80) * 1 + (1 - 1) < 0xD800
        omega
      · right
        show 0xDFFF < s.val.val / 64 * 64 * 1 + (128 - 0x80) * 1
        omega
  obtain ⟨hcp2, hseen2, hneed2, hlo2, hhi2⟩ :=
    mk_fields (s.val.val / 64) (0 + 1) 2 (0x80 : Byte) (0xBF : Byte) hinv2
  -- step three: the second continuation byte completes the sequence
  obtain ⟨c, hd, hcv⟩ := decoderHandler_complete
    (DecoderState.mk (s.val.val / 64) (0 + 1) 2 (0x80 : Byte) (0xBF : Byte))
    (IoQueue.convertTo rest) (UInt8.ofNat (0x80 + s.val.val % 64))
    (by rw [hneed2]; omega) (by rw [hlo2, hb2]; exact Nat.le_add_right _ _)
    (by rw [hhi2, hb2]; show 0x80 + s.val.val % 64 ≤ (0xBF : Nat); omega)
    (by rw [hseen2, hneed2])
  have hh3 : (decoderHandler
      (DecoderState.mk (s.val.val / 64) (0 + 1) 2 (0x80 : Byte) (0xBF : Byte))
      (IoQueue.convertTo rest) (Item.value (UInt8.ofNat (0x80 + s.val.val % 64)))).1 =
      Encoding.HandlerResult.items [c] := by rw [hd]
  rw [processQueue_of_items _ _ _ _ _ _ _ _ (read_convertTo_cons _ _) hh3, hd]
  simp only
  have hcs : c = s.val := by
    refine CodePoint.ext ?_
    rw [hcv, hcp2, hb2, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hcs, pushItems_singleton]
  exact processQueue_fuel_stable _ _ _ _ _ (by rw [processQueueFuel_convertTo]; omega)

private theorem run_scalar_four (mode : Encoding.DecoderErrorMode) (s : ScalarValue)
    (rest : ByteSequence) (output : IoQueue CodePoint) (h1 : 0x10000 ≤ s.val.val) (fuel : Nat)
    (hfuel : 2 * List.length (encodeScalar s ++ rest) + 3 ≤ fuel) :
    processQueue mode DecoderState.initial
        (IoQueue.convertTo (encodeScalar s ++ rest)) output fuel =
      processQueue mode DecoderState.initial
        (IoQueue.convertTo rest) (IoQueue.push output (Item.value s.val))
        (processQueueFuel (IoQueue.convertTo rest)) := by
  have h2 : s.val.val ≤ 0x10FFFF := s.val.isLe
  rw [encodeScalar_four_eq s h1] at hfuel ⊢
  have hcat : ([UInt8.ofNat (s.val.val / 262144 + 0xF0), UInt8.ofNat (0x80 + s.val.val / 4096 % 64),
      UInt8.ofNat (0x80 + s.val.val / 64 % 64), UInt8.ofNat (0x80 + s.val.val % 64)] ++ rest) =
      UInt8.ofNat (s.val.val / 262144 + 0xF0) :: UInt8.ofNat (0x80 + s.val.val / 4096 % 64) ::
        UInt8.ofNat (0x80 + s.val.val / 64 % 64) :: UInt8.ofNat (0x80 + s.val.val % 64) ::
          rest := rfl
  rw [hcat] at hfuel ⊢
  rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons] at hfuel
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 + 1 + 1 := ⟨fuel - 4, by omega⟩
  have hb0 : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = s.val.val / 262144 + 0xF0 :=
    toNat_ofNat_lt (by omega)
  have hb1 : (UInt8.ofNat (0x80 + s.val.val / 4096 % 64)).toNat = 0x80 + s.val.val / 4096 % 64 :=
    toNat_ofNat_lt (by omega)
  have hb2 : (UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat = 0x80 + s.val.val / 64 % 64 :=
    toNat_ofNat_lt (by omega)
  have hb3 : (UInt8.ofNat (0x80 + s.val.val % 64)).toNat = 0x80 + s.val.val % 64 :=
    toNat_ofNat_lt (by omega)
  have hk : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat &&& 0x7 = s.val.val / 262144 := by
    rw [hb0, land_three]; omega
  -- step one: the lead byte installs the boundary table
  have hlead := decoderHandler_lead_four DecoderState.initial
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 4096 % 64) ::
      UInt8.ofNat (0x80 + s.val.val / 64 % 64) :: UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (s.val.val / 262144 + 0xF0)) initial_bytesNeeded (by rw [hb0]; omega)
    (by rw [hb0]; omega)
  have hhead : (decoderHandler DecoderState.initial
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 4096 % 64) ::
        UInt8.ofNat (0x80 + s.val.val / 64 % 64) :: UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (s.val.val / 262144 + 0xF0)))).1 =
      Encoding.HandlerResult.continues := by rw [hlead]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead, hlead]
  simp only
  rw [hk, initial_bytesSeen]
  have hinv1 : decoderInv (s.val.val / 262144) 0 3
      ((if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
        else (0x80 : Byte))).toNat
      ((if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
        else (0xBF : Byte))).toNat := by
    refine Or.inr ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
    · by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0
      · rw [if_pos he]; exact (by decide : (0x80 : Nat) ≤ ((0x90 : Byte)).toNat)
      · rw [if_neg he]; exact (by decide : (0x80 : Nat) ≤ ((0x80 : Byte)).toNat)
    · by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4
      · rw [if_pos he]; exact (by decide : ((0x8F : Byte)).toNat ≤ 0xBF)
      · rw [if_neg he]; exact (by decide : ((0xBF : Byte)).toNat ≤ 0xBF)
    · rw [show (3 : Nat) - 0 - 1 = 2 from rfl, show (64 : Nat) ^ 2 = 4096 from rfl]
      by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4
      · rw [if_pos he]
        rw [hb0] at he
        show s.val.val / 262144 * 64 * 4096 + (143 - 0x80) * 4096 + (4096 - 1) ≤ 0x10FFFF
        omega
      · rw [if_neg he]
        rw [hb0] at he
        show s.val.val / 262144 * 64 * 4096 + (191 - 0x80) * 4096 + (4096 - 1) ≤ 0x10FFFF
        omega
    · rw [show (3 : Nat) - 0 - 1 = 2 from rfl, show (64 : Nat) ^ 2 = 4096 from rfl]
      right
      by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0
      · rw [if_pos he]
        rw [hb0] at he
        show 0xDFFF < s.val.val / 262144 * 64 * 4096 + (144 - 0x80) * 4096
        omega
      · rw [if_neg he]
        rw [hb0] at he
        show 0xDFFF < s.val.val / 262144 * 64 * 4096 + (128 - 0x80) * 4096
        omega
  obtain ⟨hcp1, hseen1, hneed1, hlo1, hhi1⟩ := mk_fields (s.val.val / 262144) 0 3
    (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
      else (0x80 : Byte))
    (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
      else (0xBF : Byte)) hinv1
  -- step two: the first continuation byte accumulates
  have hlow : (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
      else (0x80 : Byte)).toNat ≤ (UInt8.ofNat (0x80 + s.val.val / 4096 % 64)).toNat := by
    rw [hb1]
    by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0
    · rw [if_pos he]
      rw [hb0] at he
      show (0x90 : Nat) ≤ 0x80 + s.val.val / 4096 % 64
      omega
    · rw [if_neg he]
      show (0x80 : Nat) ≤ 0x80 + s.val.val / 4096 % 64
      omega
  have hhigh : (UInt8.ofNat (0x80 + s.val.val / 4096 % 64)).toNat ≤
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
        else (0xBF : Byte)).toNat := by
    rw [hb1]
    by_cases he : (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4
    · rw [if_pos he]
      rw [hb0] at he
      show 0x80 + s.val.val / 4096 % 64 ≤ (0x8F : Nat)
      omega
    · rw [if_neg he]
      show 0x80 + s.val.val / 4096 % 64 ≤ (0xBF : Nat)
      omega
  have hacc1 := decoderHandler_accumulate
    (DecoderState.mk (s.val.val / 262144) 0 3
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
        else (0xBF : Byte)))
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 64 % 64) ::
      UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (0x80 + s.val.val / 4096 % 64)) (by rw [hneed1]; omega)
    (by rw [hlo1]; exact hlow) (by rw [hhi1]; exact hhigh) (by rw [hseen1, hneed1]; omega)
  have hhead2 : (decoderHandler (DecoderState.mk (s.val.val / 262144) 0 3
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
        else (0xBF : Byte)))
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val / 64 % 64) ::
        UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (0x80 + s.val.val / 4096 % 64)))).1 =
      Encoding.HandlerResult.continues := by rw [hacc1]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead2, hacc1]
  simp only
  have hmid1 : ((DecoderState.mk (s.val.val / 262144) 0 3
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF0 then (0x90 : Byte)
        else (0x80 : Byte))
      (if (UInt8.ofNat (s.val.val / 262144 + 0xF0)).toNat = 0xF4 then (0x8F : Byte)
        else (0xBF : Byte))).codePoint <<< 6) |||
      ((UInt8.ofNat (0x80 + s.val.val / 4096 % 64)).toNat &&& 0x3F) = s.val.val / 4096 := by
    rw [hcp1, hb1, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hmid1, hseen1, hneed1]
  have hinv2 : decoderInv (s.val.val / 4096) (0 + 1) 3 ((0x80 : Byte)).toNat
      ((0xBF : Byte)).toNat := by
    refine Or.inr ⟨by omega, by omega, by decide, by decide, ?_, ?_⟩
    · rw [show (3 : Nat) - (0 + 1) - 1 = 1 from rfl, Nat.pow_one]
      show s.val.val / 4096 * 64 * 64 + (191 - 0x80) * 64 + (64 - 1) ≤ 0x10FFFF
      omega
    · rw [show (3 : Nat) - (0 + 1) - 1 = 1 from rfl, Nat.pow_one]
      right
      show 0xDFFF < s.val.val / 4096 * 64 * 64 + (128 - 0x80) * 64
      omega
  obtain ⟨hcp2, hseen2, hneed2, hlo2, hhi2⟩ :=
    mk_fields (s.val.val / 4096) (0 + 1) 3 (0x80 : Byte) (0xBF : Byte) hinv2
  -- step three: the second continuation byte accumulates
  have hacc2 := decoderHandler_accumulate
    (DecoderState.mk (s.val.val / 4096) (0 + 1) 3 (0x80 : Byte) (0xBF : Byte))
    (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
    (UInt8.ofNat (0x80 + s.val.val / 64 % 64)) (by rw [hneed2]; omega)
    (by rw [hlo2, hb2]; exact Nat.le_add_right _ _)
    (by rw [hhi2, hb2]; show 0x80 + s.val.val / 64 % 64 ≤ (0xBF : Nat); omega)
    (by rw [hseen2, hneed2]; omega)
  have hhead3 : (decoderHandler
      (DecoderState.mk (s.val.val / 4096) (0 + 1) 3 (0x80 : Byte) (0xBF : Byte))
      (IoQueue.convertTo (UInt8.ofNat (0x80 + s.val.val % 64) :: rest))
      (Item.value (UInt8.ofNat (0x80 + s.val.val / 64 % 64)))).1 =
      Encoding.HandlerResult.continues := by rw [hacc2]
  rw [processQueue_of_continues _ _ _ _ _ _ _ (read_convertTo_cons _ _) hhead3, hacc2]
  simp only
  have hmid2 : ((DecoderState.mk (s.val.val / 4096) (0 + 1) 3 (0x80 : Byte)
      (0xBF : Byte)).codePoint <<< 6) |||
      ((UInt8.ofNat (0x80 + s.val.val / 64 % 64)).toNat &&& 0x3F) = s.val.val / 64 := by
    rw [hcp2, hb2, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hmid2, hseen2, hneed2]
  have hinv3 : decoderInv (s.val.val / 64) (0 + 1 + 1) 3 ((0x80 : Byte)).toNat
      ((0xBF : Byte)).toNat := by
    refine Or.inr ⟨by omega, by omega, by decide, by decide, ?_, ?_⟩
    · rw [show (3 : Nat) - (0 + 1 + 1) - 1 = 0 from rfl, Nat.pow_zero]
      show s.val.val / 64 * 64 * 1 + (191 - 0x80) * 1 + (1 - 1) ≤ 0x10FFFF
      omega
    · rw [show (3 : Nat) - (0 + 1 + 1) - 1 = 0 from rfl, Nat.pow_zero]
      right
      show 0xDFFF < s.val.val / 64 * 64 * 1 + (128 - 0x80) * 1
      omega
  obtain ⟨hcp3, hseen3, hneed3, hlo3, hhi3⟩ :=
    mk_fields (s.val.val / 64) (0 + 1 + 1) 3 (0x80 : Byte) (0xBF : Byte) hinv3
  -- step four: the third continuation byte completes the sequence
  obtain ⟨c, hd, hcv⟩ := decoderHandler_complete
    (DecoderState.mk (s.val.val / 64) (0 + 1 + 1) 3 (0x80 : Byte) (0xBF : Byte))
    (IoQueue.convertTo rest) (UInt8.ofNat (0x80 + s.val.val % 64))
    (by rw [hneed3]; omega) (by rw [hlo3, hb3]; exact Nat.le_add_right _ _)
    (by rw [hhi3, hb3]; show 0x80 + s.val.val % 64 ≤ (0xBF : Nat); omega)
    (by rw [hseen3, hneed3])
  have hh4 : (decoderHandler
      (DecoderState.mk (s.val.val / 64) (0 + 1 + 1) 3 (0x80 : Byte) (0xBF : Byte))
      (IoQueue.convertTo rest) (Item.value (UInt8.ofNat (0x80 + s.val.val % 64)))).1 =
      Encoding.HandlerResult.items [c] := by rw [hd]
  rw [processQueue_of_items _ _ _ _ _ _ _ _ (read_convertTo_cons _ _) hh4, hd]
  simp only
  have hcs : c = s.val := by
    refine CodePoint.ext ?_
    rw [hcv, hcp3, hb3, land_six, lor_shift_six _ _ (by omega)]
    omega
  rw [hcs, pushItems_singleton]
  exact processQueue_fuel_stable _ _ _ _ _ (by rw [processQueueFuel_convertTo]; omega)

/-- The run over one encoded scalar value: PROCQ [14785,15508) started in the
initial state over `encodeScalar s ++ rest` consumes exactly `encodeScalar s`,
pushes `s`'s code point, and returns to the initial state. -/
private theorem run_scalar (mode : Encoding.DecoderErrorMode) (s : ScalarValue)
    (rest : ByteSequence) (output : IoQueue CodePoint) (fuel : Nat)
    (hfuel : 2 * List.length (encodeScalar s ++ rest) + 3 ≤ fuel) :
    processQueue mode DecoderState.initial
        (IoQueue.convertTo (encodeScalar s ++ rest)) output fuel =
      processQueue mode DecoderState.initial
        (IoQueue.convertTo rest) (IoQueue.push output (Item.value s.val))
        (processQueueFuel (IoQueue.convertTo rest)) := by
  have hle : s.val.val ≤ 0x10FFFF := s.val.isLe
  rcases Nat.lt_or_ge s.val.val 0x80 with h1 | h1
  · exact run_scalar_one mode s rest output (by omega) fuel hfuel
  · rcases Nat.lt_or_ge s.val.val 0x800 with h2 | h2
    · exact run_scalar_two mode s rest output h1 (by omega) fuel hfuel
    · rcases Nat.lt_or_ge s.val.val 0x10000 with h3 | h3
      · exact run_scalar_three mode s rest output h2 (by omega) fuel hfuel
      · exact run_scalar_four mode s rest output h3 fuel hfuel

/-- `Whatwg.Url.Boundary.Utf8DecodeOrFail.failed`, as
`requirement.percent-encoded-utf8-advice` of `vendor/whatwg-url-55d66993/url.bs`
[16325,16862) reads it: the boundary's `failed` field is a function of the bytes,
and this is that function. -/
theorem u3Profile_decodeOrFail (b : ByteSequence) :
    (decodeWithoutBomOrFail b).isNone = true ↔ isWellFormed b = false := by
  rw [isWellFormed]
  cases decodeWithoutBomOrFail b <;> simp

end Utf8

end Whatwg.Infra
