import Whatwg.Infra

/-!
Breaker-owned law battery for the Infra UTF-8 codec packet.

Contract: `test/contracts/infra-utf8.contract.md`.
Graph: `INFRA-PG-UTF8` (`docs/INFRA-UTF8-DAG.md`).
Interface: `WhatwgTest/Infra/Utf8Contract.lean`.
Receipts: `WhatwgTest/Infra/Utf8AxiomReport.lean`.
Attacks: `test/counterexamples/infra/UTF8.md` (`INFRA-UTF8-CE-001` …).

Every proposition below is frozen by `#check (@name : proposition)` ascription
and cites its `[byte-start,byte-end)` span into
`vendor/whatwg-encoding-67494fce/encoding.bs`, SHA-256
`43cb027a611580ad07b5cd3a96e82ee4303594e6b24b8b7c5b903cd2e50f19ad`, or into
`vendor/whatwg-infra-3f984adc/infra.bs`, SHA-256
`7c38e6e25ef21f536142cfc6d94954c41bc9889cd0b6fd67ab34571215acd8eb`, where the
row is Infra's. The contract holds the recomputed digest of every span. No line
number is cited.

**Observation mask.** This family is equational and names no mask. DB-04's M1
and M2 are Streams' consumer observations over decision tapes; a codec is a
Stratum V deliverable (RS-1: "carriers, codecs, canonical forms, and the laws
connecting decoded, encoded, and representation views"), so
`docs/SPEC-COVERAGE.md`'s green criterion applies in its "an equational family
whose contract states no mask records that instead" form. The one place a
decision appears is the foreign encoder profile, and it appears as first-order
data on `Whatwg.Infra.Encoding.EncoderTape`, not as a mask.

**Evidence classes.** Names ending `_example` are finite probes. Four are
transcribed from the pin's own examples; the rest are the discriminating
witnesses of `test/counterexamples/infra/UTF8.md`. A passing finite probe is a
probe, never a general law, which is why every malformed class below carries a
quantified law as well as its probe.

**Constructive target.** `docs/CHOICE-REMOVAL.md` records the Infra lane's
standard: receipts choice-free where possible, following
`docs/INFRA-SCALAR-ASSURANCE.md` and `docs/INFRA-INTEGER-CONSTRUCTIVE.md`. The
target ceiling for every receipt here is `[propext, Quot.sound]`, strictly
inside the repository ceiling of ruling R-11. The contract names the two places
where `Classical.choice` may be unavoidable and why.
-/

set_option autoImplicit false


/-! ## 1. The I/O queue

Section `terminology` [4710,12179) of the Encoding pin. -/

/-! `op.io-queue-read` [6610,7078) step 1, "wait until its size is at least 1",
on the empty queue: the read is unanswered. A live frontier, never an error. -/
#check (@Whatwg.Infra.IoQueue.read_nil :
  (α : Type) → Whatwg.Infra.IoQueue.read ([] : Whatwg.Infra.IoQueue α) = none)

/-! `op.io-queue-read` [6610,7078) step 2: "If ioQueue[0] is end-of-queue, then
return end-of-queue." Step 3's removal is *not* reached, so the queue is
unchanged and every later read of an immediate queue keeps answering
`end-of-queue`. -/
#check (@Whatwg.Infra.IoQueue.read_endOfQueue :
  (α : Type) → (rest : Whatwg.Infra.IoQueue α) →
    Whatwg.Infra.IoQueue.read (Whatwg.Infra.Item.endOfQueue :: rest) =
      some (Whatwg.Infra.Item.endOfQueue, Whatwg.Infra.Item.endOfQueue :: rest))

/-! `op.io-queue-read` [6610,7078) step 3: "Remove ioQueue[0] and return it." -/
#check (@Whatwg.Infra.IoQueue.read_value :
  (α : Type) → (a : α) → (rest : Whatwg.Infra.IoQueue α) →
    Whatwg.Infra.IoQueue.read (Whatwg.Infra.Item.value a :: rest) =
      some (Whatwg.Infra.Item.value a, rest))

/-! `op.io-queue-read-items` [7079,7650) steps 2 to 4: `number` reads, then
"Remove end-of-queue from readItems". Reading past an `end-of-queue` therefore
yields the values before it and leaves the queue's terminator in place. -/
#check (@Whatwg.Infra.IoQueue.readItems_endOfQueue :
  (α : Type) → (l : List α) → (n : Nat) → l.length ≤ n →
    Whatwg.Infra.IoQueue.readItems
        (l.map Whatwg.Infra.Item.value ++ [Whatwg.Infra.Item.endOfQueue]) n =
      some (l, [Whatwg.Infra.Item.endOfQueue]))

/-! `op.io-queue-push` [8448,9041) step 2: "Otherwise, append item to
ioQueue." -/
#check (@Whatwg.Infra.IoQueue.push_append :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) → (item : Whatwg.Infra.Item α) →
    q.getLast? ≠ some Whatwg.Infra.Item.endOfQueue →
      Whatwg.Infra.IoQueue.push q item = q ++ [item])

/-! `op.io-queue-push` [8448,9041) step 1.2: "Otherwise, insert item before the
last item in ioQueue." -/
#check (@Whatwg.Infra.IoQueue.push_before_endOfQueue :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) → (a : α) →
    Whatwg.Infra.IoQueue.push (q ++ [Whatwg.Infra.Item.endOfQueue])
        (Whatwg.Infra.Item.value a) =
      q ++ [Whatwg.Infra.Item.value a, Whatwg.Infra.Item.endOfQueue])

/-! `op.io-queue-push` [8448,9041) step 1.1: "If item is end-of-queue, do
nothing." A queue never carries two terminators. -/
#check (@Whatwg.Infra.IoQueue.push_endOfQueue_idem :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) →
    Whatwg.Infra.IoQueue.push (q ++ [Whatwg.Infra.Item.endOfQueue])
        Whatwg.Infra.Item.endOfQueue =
      q ++ [Whatwg.Infra.Item.endOfQueue])

/-! `op.io-queue-restore` [9271,9726): "perform the list prepend operation". -/
#check (@Whatwg.Infra.IoQueue.restore_eq :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) → (a : α) →
    Whatwg.Infra.IoQueue.restore q a = Whatwg.Infra.Item.value a :: q)

/-! `op.io-queue-restore` [9271,9726), second sentence: "insert those items, in
the given order, before the first item in the queue". -/
#check (@Whatwg.Infra.IoQueue.restoreItems_eq :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) → (l : List α) →
    Whatwg.Infra.IoQueue.restoreItems q l = l.map Whatwg.Infra.Item.value ++ q)

/-! The pin's own example, `example.io-queue-restore` [9727,9981): "Inserting
the bytes « 0xF0, 0x9F » in an I/O queue « 0x92 0xA9, end-of-queue », results in
an I/O queue « 0xF0, 0x9F, 0x92 0xA9, end-of-queue ». The next item to be read
would be 0xF0." The four bytes are U+1F4A9's UTF-8 encoding. -/
#check (@Whatwg.Infra.IoQueue.restoreItems_example :
  Whatwg.Infra.IoQueue.restoreItems
      [Whatwg.Infra.Item.value (0x92 : Whatwg.Infra.Byte),
        Whatwg.Infra.Item.value (0xA9 : Whatwg.Infra.Byte),
        Whatwg.Infra.Item.endOfQueue]
      [(0xF0 : Whatwg.Infra.Byte), (0x9F : Whatwg.Infra.Byte)] =
    [Whatwg.Infra.Item.value (0xF0 : Whatwg.Infra.Byte),
      Whatwg.Infra.Item.value (0x9F : Whatwg.Infra.Byte),
      Whatwg.Infra.Item.value (0x92 : Whatwg.Infra.Byte),
      Whatwg.Infra.Item.value (0xA9 : Whatwg.Infra.Byte),
      Whatwg.Infra.Item.endOfQueue])

/-! `op.to-io-queue-convert` [10286,10769) step 2: "an I/O queue containing the
items in input, in order, followed by end-of-queue". -/
#check (@Whatwg.Infra.IoQueue.convertTo_eq :
  (α : Type) → (l : List α) →
    Whatwg.Infra.IoQueue.convertTo l =
      l.map Whatwg.Infra.Item.value ++ [Whatwg.Infra.Item.endOfQueue])

/-! The queue round trip: `op.from-io-queue-convert` [9982,10285) after
`op.to-io-queue-convert` [10286,10769) is the identity on lists. This is RS-1's
codec round trip at the container level. -/
#check (@Whatwg.Infra.IoQueue.convertFrom_convertTo :
  (α : Type) → (l : List α) →
    Whatwg.Infra.IoQueue.convertFrom (Whatwg.Infra.IoQueue.convertTo l) = l)

/-! Every converted queue is an immediate queue. -/
#check (@Whatwg.Infra.IoQueue.containsEndOfQueue_convertTo :
  (α : Type) → (l : List α) →
    Whatwg.Infra.IoQueue.containsEndOfQueue (Whatwg.Infra.IoQueue.convertTo l) = true)

/-! `op.io-queue-peek` [7651,8447), the zero-based reading: the values of the
first `number` items, cut at the terminator. -/
#check (@Whatwg.Infra.IoQueue.peekPrefix_convertTo :
  (α : Type) → (l : List α) → (n : Nat) →
    Whatwg.Infra.IoQueue.peekPrefix (Whatwg.Infra.IoQueue.convertTo l) n = l.take n)

/-! **INFRA-R15, stated as a theorem.** The literal transcription of
`op.io-queue-peek` [7651,8447) — "For each n in the range 1 to number,
inclusive … append ioQueue[n]" over Infra's zero-based indexing
(`vendor/whatwg-infra-3f984adc/infra.bs` [67159,67540)) — is the zero-based peek
of the queue with its first item dropped. The two disagree on every nonempty
queue, and `op.utf-8-decode` [45059,45762) step 2 is stated over
`peekPrefix`. -/
#check (@Whatwg.Infra.IoQueue.peek_eq_peekPrefix_tail :
  (α : Type) → (q : Whatwg.Infra.IoQueue α) → (n : Nat) →
    Whatwg.Infra.IoQueue.peek q n = Whatwg.Infra.IoQueue.peekPrefix (q.drop 1) n)

/-! The discriminating witness for INFRA-R15: under the literal reading the
byte order mark is not the first three bytes and `op.utf-8-decode`
[45059,45762) would never strip one. -/
#check (@Whatwg.Infra.IoQueue.peek_bom_example :
  Whatwg.Infra.IoQueue.peek
      (Whatwg.Infra.IoQueue.convertTo [(0xEF : Whatwg.Infra.Byte), 0xBB, 0xBF]) 3 =
    [(0xBB : Whatwg.Infra.Byte), 0xBF])


/-! ## 2. The four Infra candidates adopted from the U3 builder

Four facts the U3 packet's laws needed did not exist under `Whatwg/Infra/`; the
U3 builder proved them as private lemmas in `Whatwg/Url/PercentEncoding.lean`
and recorded them as Infra candidates in
`test/contracts/url-percent-encoding.contract.md`. This packet adopts them with
their exact statements, at the homes that contract named:
`codePoints_of_no_lead` and `isAsciiString_of_units` in
`Whatwg/Infra/Text/String.lean`, `isomorphicEncode_eq` and `asciiEncode?_eq` in
`Whatwg/Infra/Text/Codec.lean`. The UTF-8 packet needs all four for its own
ASCII-agreement law, which is why it is the packet that adopts them. -/

/-! Infra `op.string-code-points` reading: a string with no leading surrogate
has one code point per code unit. -/
#check (@Whatwg.Infra.JsString.codePoints_of_no_lead :
  (input : Whatwg.Infra.JsString) → (∀ unit ∈ input, unit.toNat < 0xD800) →
    Whatwg.Infra.JsString.codePoints input =
      List.map Whatwg.Infra.CodePoint.ofUnit input)

/-! Infra `type.ascii-string` [44424,44569) neighbourhood: units below 0x80
make an ASCII string. -/
#check (@Whatwg.Infra.JsString.isAsciiString_of_units :
  (input : Whatwg.Infra.JsString) → (∀ unit ∈ input, unit.toNat ≤ 0x7F) →
    Whatwg.Infra.JsString.isAsciiString input = true)

/-! Infra `op.isomorphic-encode` [55919,56325) in computed form.
`isomorphicEncode` is written with `List.pmap` and is otherwise opaque to
rewriting. -/
#check (@Whatwg.Infra.JsString.isomorphicEncode_eq :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isIsomorphicString input = true) →
      Whatwg.Infra.JsString.isomorphicEncode input h =
        List.map (fun codePoint => UInt8.ofNat codePoint.val)
          (Whatwg.Infra.JsString.codePoints input))

/-! Infra `op.ascii-encode` [56961,57243) in computed form. This is the
load-bearing one: `asciiEncode?` is a `dite` over `isAsciiString` wrapping the
`pmap`, and without a computed form no law stated through it can be
discharged. -/
#check (@Whatwg.Infra.JsString.asciiEncode?_eq :
  (input : Whatwg.Infra.JsString) → (∀ unit ∈ input, unit.toNat ≤ 0x7F) →
    Whatwg.Infra.JsString.asciiEncode? input =
      some (List.map (fun unit => UInt8.ofNat unit.toNat) input))


/-! ## 3. The UTF-8 encoder

`op.utf-8-encoder` [90407,91744). -/

/-! Step 3's switch, with the ASCII case of step 2 folded in as count 0. -/
#check (@Whatwg.Infra.Utf8.encoderCount_eq :
  (c : Whatwg.Infra.CodePoint) →
    Whatwg.Infra.Utf8.encoderCount c =
      (if c.val ≤ 0x7F then 0 else if c.val ≤ 0x7FF then 1 else if c.val ≤ 0xFFFF then 2 else 3))

/-! Step 3's switch, offsets: "1 and 0xC0", "2 and 0xE0", "3 and 0xF0", with the
ASCII case of step 2 folded in as offset 0x00. -/
#check (@Whatwg.Infra.Utf8.encoderOffset_eq :
  (c : Whatwg.Infra.CodePoint) →
    Whatwg.Infra.Utf8.encoderOffset c =
      (if c.val ≤ 0x7F then 0x00 else if c.val ≤ 0x7FF then 0xC0
        else if c.val ≤ 0xFFFF then 0xE0 else 0xF0))

/-! Step 5's `While count is greater than 0` loop, at zero. -/
#check (@Whatwg.Infra.Utf8.encoderTail_zero :
  (v : Nat) → Whatwg.Infra.Utf8.encoderTail v 0 = [])

/-! Step 5's loop body: "Set temp to codePoint >> (6 × (count − 1)). Append to
bytes 0x80 | (temp & 0x3F). Decrease count by one." The byte at shift
`6 × count` is appended first, so the recursion peels the *high* group. -/
#check (@Whatwg.Infra.Utf8.encoderTail_succ :
  (v : Nat) → (n : Nat) →
    Whatwg.Infra.Utf8.encoderTail v (n + 1) =
      UInt8.ofNat (0x80 ||| ((v >>> (6 * n)) &&& 0x3F)) :: Whatwg.Infra.Utf8.encoderTail v n)

#check (@Whatwg.Infra.Utf8.encoderTail_length :
  (v : Nat) → (n : Nat) → (Whatwg.Infra.Utf8.encoderTail v n).length = n)

/-! Every byte step 5 appends is a continuation byte. -/
#check (@Whatwg.Infra.Utf8.encoderTail_continuation :
  (v : Nat) → (n : Nat) → (b : Whatwg.Infra.Byte) →
    b ∈ Whatwg.Infra.Utf8.encoderTail v n → (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF))

/-! Steps 4 to 6 assembled: "Let bytes be a byte sequence whose first byte is
(codePoint >> (6 × count)) + offset", then step 5's loop, then "Return bytes
bytes, in order." -/
#check (@Whatwg.Infra.Utf8.encodeScalar_eq :
  (s : Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.encodeScalar s =
      UInt8.ofNat ((s.val.val >>> (6 * Whatwg.Infra.Utf8.encoderCount s.val)) +
          Whatwg.Infra.Utf8.encoderOffset s.val) ::
        Whatwg.Infra.Utf8.encoderTail s.val.val (Whatwg.Infra.Utf8.encoderCount s.val))

/-! Step 2: "If codePoint is an ASCII code point, then return a byte whose value
is codePoint." -/
#check (@Whatwg.Infra.Utf8.encodeScalar_ascii :
  (s : Whatwg.Infra.ScalarValue) → s.val.val ≤ 0x7F →
    Whatwg.Infra.Utf8.encodeScalar s = [UInt8.ofNat s.val.val])

/-! The four-length shape, one law per row of step 3's switch. -/
#check (@Whatwg.Infra.Utf8.encodeScalar_length_one :
  (s : Whatwg.Infra.ScalarValue) → s.val.val ≤ 0x7F →
    (Whatwg.Infra.Utf8.encodeScalar s).length = 1)

#check (@Whatwg.Infra.Utf8.encodeScalar_length_two :
  (s : Whatwg.Infra.ScalarValue) → 0x80 ≤ s.val.val → s.val.val ≤ 0x7FF →
    (Whatwg.Infra.Utf8.encodeScalar s).length = 2)

#check (@Whatwg.Infra.Utf8.encodeScalar_length_three :
  (s : Whatwg.Infra.ScalarValue) → 0x800 ≤ s.val.val → s.val.val ≤ 0xFFFF →
    (Whatwg.Infra.Utf8.encodeScalar s).length = 3)

#check (@Whatwg.Infra.Utf8.encodeScalar_length_four :
  (s : Whatwg.Infra.ScalarValue) → 0x10000 ≤ s.val.val →
    (Whatwg.Infra.Utf8.encodeScalar s).length = 4)

/-! The shape is exactly four lengths and never zero: there is no fifth row in
step 3's switch, and step 4 always emits a first byte. -/
#check (@Whatwg.Infra.Utf8.encodeScalar_length_mem :
  (s : Whatwg.Infra.ScalarValue) → (Whatwg.Infra.Utf8.encodeScalar s).length ∈ [1, 2, 3, 4])

#check (@Whatwg.Infra.Utf8.encodeScalar_ne_nil :
  (s : Whatwg.Infra.ScalarValue) → Whatwg.Infra.Utf8.encodeScalar s ≠ [])

/-! The lead byte lies in exactly the four ranges `op.utf-8-decoder`
[86515,90406) step 3 accepts, and in no other. 0xC0 and 0xC1 are unreachable,
which is the encoder half of "no overlong encoding exists"; 0xF5 to 0xFF are
unreachable, which is the encoder half of "nothing above U+10FFFF is
encodable". -/
#check (@Whatwg.Infra.Utf8.encodeScalar_head_range :
  (s : Whatwg.Infra.ScalarValue) → (b : Whatwg.Infra.Byte) →
    (Whatwg.Infra.Utf8.encodeScalar s).head? = some b →
      (b.toNat ≤ 0x7F ∨ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF) ∨
        (0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF) ∨ (0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4)))

/-! Every byte after the first is a continuation byte, so no encoded scalar
value contains a lead byte anywhere but at its head. -/
#check (@Whatwg.Infra.Utf8.encodeScalar_tail_continuation :
  (s : Whatwg.Infra.ScalarValue) → (b : Whatwg.Infra.Byte) →
    b ∈ (Whatwg.Infra.Utf8.encodeScalar s).drop 1 → (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF))

/-! Canonical-form injectivity (RS-1): distinct scalar values have distinct
encodings. -/
#check (@Whatwg.Infra.Utf8.encodeScalar_injective :
  (a : Whatwg.Infra.ScalarValue) → (b : Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.encodeScalar a = Whatwg.Infra.Utf8.encodeScalar b → a = b)

/-! The byte order mark is emitted by exactly one scalar value, U+FEFF. -/
#check (@Whatwg.Infra.Utf8.encodeScalar_bom_iff :
  (s : Whatwg.Infra.ScalarValue) →
    (Whatwg.Infra.Utf8.encodeScalar s = Whatwg.Infra.Utf8.bom ↔ s.val.val = 0xFEFF))

#check (@Whatwg.Infra.Utf8.bom_eq :
  Whatwg.Infra.Utf8.bom = [(0xEF : Whatwg.Infra.Byte), 0xBB, 0xBF])

/-! `op.encode` [50170,50822) run to completion over UTF-8's encoder is the
concatenation of the per-scalar encodings: the encoder is stateless, so
`op.process-a-queue` [14785,15508) is a `flatMap`. -/
#check (@Whatwg.Infra.Utf8.encodeScalars_eq :
  (ss : List Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.encodeScalars ss = ss.flatMap Whatwg.Infra.Utf8.encodeScalar)

#check (@Whatwg.Infra.Utf8.encodeScalars_append :
  (a : List Whatwg.Infra.ScalarValue) → (b : List Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.encodeScalars (a ++ b) =
      Whatwg.Infra.Utf8.encodeScalars a ++ Whatwg.Infra.Utf8.encodeScalars b)

/-! `op.utf-8-encode` [46912,47215) at the queue face. -/
#check (@Whatwg.Infra.Utf8.encodeQueue_convertTo :
  (ss : List Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.encodeQueue (Whatwg.Infra.IoQueue.convertTo ss) =
      Whatwg.Infra.IoQueue.convertTo (Whatwg.Infra.Utf8.encodeScalars ss))

/-! The string face and its bridge to `Whatwg.Infra.JsString.codePoints`. -/
#check (@Whatwg.Infra.Utf8.scalars_val :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      (Whatwg.Infra.Utf8.scalars input h).map (fun s => s.val) =
        Whatwg.Infra.JsString.codePoints input)

#check (@Whatwg.Infra.Utf8.encode_eq :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Utf8.encode input h =
        Whatwg.Infra.Utf8.encodeScalars (Whatwg.Infra.Utf8.scalars input h))

#check (@Whatwg.Infra.Utf8.encode?_eq_some :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Utf8.encode? input = some (Whatwg.Infra.Utf8.encode input h))

#check (@Whatwg.Infra.Utf8.encode?_eq_none :
  (input : Whatwg.Infra.JsString) →
    Whatwg.Infra.JsString.isScalarValueString input = false →
      Whatwg.Infra.Utf8.encode? input = none)

/-! The encoder never manufactures a byte order mark: its output starts with
0xEF 0xBB 0xBF exactly when the input's first code point is U+FEFF. -/
#check (@Whatwg.Infra.Utf8.encode_startsWith_bom_iff :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      (Whatwg.Infra.ByteSequence.startsWith (Whatwg.Infra.Utf8.encode input h)
            Whatwg.Infra.Utf8.bom = true ↔
        ∃ c : Whatwg.Infra.CodePoint,
          (Whatwg.Infra.JsString.codePoints input).head? = some c ∧ c.val = 0xFEFF))

/-! The note of Infra's `op.ascii-encode` [56961,57243) of
`vendor/whatwg-infra-3f984adc/infra.bs`: "Isomorphic encode and UTF-8 encode
return the same byte sequence for input." `docs/INFRA-PROOF-PLAN.md` section 4.6
left this row `partial` with the bridge named "until Encoding has its own pin";
the pin exists now and this is the theorem that closes it. -/
#check (@Whatwg.Infra.Utf8.encode_ascii_eq_asciiEncode :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.JsString.isAsciiString input = true →
        Whatwg.Infra.JsString.asciiEncode? input = some (Whatwg.Infra.Utf8.encode input h))

/-! The other half of the same note, from Infra's byte-sequences prose
[34550,34700): "UTF-8 encode from Encoding is encouraged. In rare circumstances
isomorphic encode might be needed." The two disagree on the first non-ASCII
code point, U+0080, and on the pin's own U+00E9. A finite probe. -/
#check (@Whatwg.Infra.Utf8.encode_ne_isomorphicEncode_example :
  Whatwg.Infra.Utf8.encode? [(0xE9 : Whatwg.Infra.CodeUnit)] =
      some [(0xC3 : Whatwg.Infra.Byte), 0xA9] ∧
    Whatwg.Infra.JsString.isomorphicEncode? [(0xE9 : Whatwg.Infra.CodeUnit)] =
      some [(0xE9 : Whatwg.Infra.Byte)])

/-! The pin's own 💩, the four bytes of `example.io-queue-restore`
[9727,9981). A finite probe. -/
#check (@Whatwg.Infra.Utf8.encode_astral_example :
  Whatwg.Infra.Utf8.encode? [(0xD83D : Whatwg.Infra.CodeUnit), 0xDCA9] =
    some [(0xF0 : Whatwg.Infra.Byte), 0x9F, 0x92, 0xA9])


/-! ## 4. The UTF-8 decoder's state machine

`op.utf-8-decoder` [86515,90406), one law per numbered step or switch row. -/

#check (@Whatwg.Infra.Utf8.DecoderState.initial_eq :
  Whatwg.Infra.Utf8.DecoderState.initial =
    Whatwg.Infra.Utf8.DecoderState.mk 0 0 0 (0x80 : Whatwg.Infra.Byte)
      (0xBF : Whatwg.Infra.Byte))

/-! Step 1: "If byte is end-of-queue and UTF-8 bytes needed is not 0, then set
UTF-8 bytes needed to 0 and return error." Only `bytes needed` is reset; the
accumulator, the count of bytes seen and the boundaries are left as they
were. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_endOfQueue_pending :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    st.bytesNeeded ≠ 0 →
      Whatwg.Infra.Utf8.decoderHandler st q Whatwg.Infra.Item.endOfQueue =
        (Whatwg.Infra.Encoding.HandlerResult.error none,
          Whatwg.Infra.Utf8.DecoderState.mk st.codePoint st.bytesSeen 0
            st.lowerBoundary st.upperBoundary,
          q))

/-! Step 2: "If byte is end-of-queue, then return finished." -/
#check (@Whatwg.Infra.Utf8.decoderHandler_endOfQueue_idle :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    st.bytesNeeded = 0 →
      Whatwg.Infra.Utf8.decoderHandler st q Whatwg.Infra.Item.endOfQueue =
        (Whatwg.Infra.Encoding.HandlerResult.finished, st, q))

/-! Step 3, switch row "0x00 to 0x7F": "Return a code point whose value is
byte." -/
#check (@Whatwg.Infra.Utf8.decoderHandler_ascii :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded = 0 → b.toNat ≤ 0x7F →
      ∃ c : Whatwg.Infra.CodePoint,
        Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
            (Whatwg.Infra.Encoding.HandlerResult.items [c], st, q) ∧
          c.val = b.toNat)

/-! Step 3, switch row "0xC2 to 0xDF": bytes needed 1, code point `byte & 0x1F`,
"the five least significant bits of byte". -/
#check (@Whatwg.Infra.Utf8.decoderHandler_lead_two :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded = 0 → 0xC2 ≤ b.toNat → b.toNat ≤ 0xDF →
      Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
        (Whatwg.Infra.Encoding.HandlerResult.continues,
          Whatwg.Infra.Utf8.DecoderState.mk (b.toNat &&& 0x1F) st.bytesSeen 1
            (0x80 : Whatwg.Infra.Byte) (0xBF : Whatwg.Infra.Byte),
          q))

/-! Step 3, switch row "0xE0 to 0xEF", with the boundary table of its steps 1
and 2: "If byte is 0xE0, then set UTF-8 lower boundary to 0xA0. If byte is 0xED,
then set UTF-8 upper boundary to 0x9F." Those two adjustments are exactly what
excludes the overlong three-byte forms and the surrogate range. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_lead_three :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded = 0 → 0xE0 ≤ b.toNat → b.toNat ≤ 0xEF →
      Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
        (Whatwg.Infra.Encoding.HandlerResult.continues,
          Whatwg.Infra.Utf8.DecoderState.mk (b.toNat &&& 0xF) st.bytesSeen 2
            (if b.toNat = 0xE0 then (0xA0 : Whatwg.Infra.Byte) else (0x80 : Whatwg.Infra.Byte))
            (if b.toNat = 0xED then (0x9F : Whatwg.Infra.Byte) else (0xBF : Whatwg.Infra.Byte)),
          q))

/-! Step 3, switch row "0xF0 to 0xF4", with the boundary table of its steps 1
and 2: "If byte is 0xF0, then set UTF-8 lower boundary to 0x90. If byte is 0xF4,
then set UTF-8 upper boundary to 0x8F." Those two adjustments are exactly what
excludes the overlong four-byte forms and everything above U+10FFFF. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_lead_four :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded = 0 → 0xF0 ≤ b.toNat → b.toNat ≤ 0xF4 →
      Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
        (Whatwg.Infra.Encoding.HandlerResult.continues,
          Whatwg.Infra.Utf8.DecoderState.mk (b.toNat &&& 0x7) st.bytesSeen 3
            (if b.toNat = 0xF0 then (0x90 : Whatwg.Infra.Byte) else (0x80 : Whatwg.Infra.Byte))
            (if b.toNat = 0xF4 then (0x8F : Whatwg.Infra.Byte) else (0xBF : Whatwg.Infra.Byte)),
          q))

/-! Step 3, switch row "Otherwise": every byte from 0x80 to 0xC1 and every byte
from 0xF5 upward is an error at bytes-needed 0, with no state change and no
restore. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_lead_error :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded = 0 →
      ((0x80 ≤ b.toNat ∧ b.toNat ≤ 0xC1) ∨ 0xF5 ≤ b.toNat) →
        Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
          (Whatwg.Infra.Encoding.HandlerResult.error none, st, q))

/-! Step 4: "If byte is not in the range UTF-8 lower boundary to UTF-8 upper
boundary, inclusive: Set UTF-8 code point, UTF-8 bytes needed, and UTF-8 bytes
seen to 0, set UTF-8 lower boundary to 0x80, and set UTF-8 upper boundary to
0xBF. Restore byte to ioQueue. Return error." The restore is why a truncated
sequence followed by a valid byte costs one U+FFFD and not two. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_out_of_boundary :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded ≠ 0 →
      (b.toNat < st.lowerBoundary.toNat ∨ st.upperBoundary.toNat < b.toNat) →
        Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
          (Whatwg.Infra.Encoding.HandlerResult.error none,
            Whatwg.Infra.Utf8.DecoderState.initial,
            Whatwg.Infra.IoQueue.restore q b))

/-! Steps 5 to 8: reset the boundaries to 0x80 and 0xBF, shift the accumulator
left by six and take the byte's six least significant bits, increase bytes seen
by one, and continue while more bytes are needed. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_accumulate :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded ≠ 0 →
      st.lowerBoundary.toNat ≤ b.toNat → b.toNat ≤ st.upperBoundary.toNat →
        st.bytesSeen + 1 ≠ st.bytesNeeded →
          Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
            (Whatwg.Infra.Encoding.HandlerResult.continues,
              Whatwg.Infra.Utf8.DecoderState.mk
                ((st.codePoint <<< 6) ||| (b.toNat &&& 0x3F)) (st.bytesSeen + 1)
                st.bytesNeeded (0x80 : Whatwg.Infra.Byte) (0xBF : Whatwg.Infra.Byte),
              q))

/-! Steps 9 to 11: "Let codePoint be UTF-8 code point. Set UTF-8 code point,
UTF-8 bytes needed, and UTF-8 bytes seen to 0. Return a code point whose value
is codePoint." Step 5 has already reset the boundaries, so the state returned is
the initial state. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_complete :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (b : Whatwg.Infra.Byte) → st.bytesNeeded ≠ 0 →
      st.lowerBoundary.toNat ≤ b.toNat → b.toNat ≤ st.upperBoundary.toNat →
        st.bytesSeen + 1 = st.bytesNeeded →
          ∃ c : Whatwg.Infra.CodePoint,
        Whatwg.Infra.Utf8.decoderHandler st q (Whatwg.Infra.Item.value b) =
                (Whatwg.Infra.Encoding.HandlerResult.items [c],
                  Whatwg.Infra.Utf8.DecoderState.initial, q) ∧
              c.val = (st.codePoint <<< 6) ||| (b.toNat &&& 0x3F))

/-! The decoder never supplies a code point with its error: only an encoder
does, for step 7's "html" arm of `op.process-an-item` [15509,17620) and step 3
of `op.encode-or-fail` [51167,53203). -/
#check (@Whatwg.Infra.Utf8.decoderHandler_error_none :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (item : Whatwg.Infra.Item Whatwg.Infra.Byte) → (c : Whatwg.Infra.CodePoint) →
      (Whatwg.Infra.Utf8.decoderHandler st q item).1 ≠
        Whatwg.Infra.Encoding.HandlerResult.error (some c))

/-! The decoder never returns a surrogate, which is what step 6.1 of
`op.process-an-item` [15509,17620) asserts: "Assert: encoderDecoder is not a
decoder instance or result does not contain any surrogates." It is a theorem of
the 0xED upper-boundary row, not a typing assumption. -/
#check (@Whatwg.Infra.Utf8.decoderHandler_items_isScalarValue :
  (st : Whatwg.Infra.Utf8.DecoderState) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (item : Whatwg.Infra.Item Whatwg.Infra.Byte) → (out : List Whatwg.Infra.CodePoint) →
      st.bytesNeeded ≤ 3 → st.codePoint ≤ 0x10FFFF →
        (Whatwg.Infra.Utf8.decoderHandler st q item).1 =
            Whatwg.Infra.Encoding.HandlerResult.items out →
          out.all Whatwg.Infra.CodePoint.isScalarValue = true)


/-! ## 5. Processing a queue

`op.process-a-queue` [14785,15508) and `op.process-an-item` [15509,17620). -/

#check (@Whatwg.Infra.Utf8.processQueueFuel_eq :
  (q : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    Whatwg.Infra.Utf8.processQueueFuel q = 2 * q.length + 1)

/-! The `While true` of `op.process-a-queue` [14785,15508) terminates on every
immediate queue, and `processQueueFuel` is enough fuel: above it the result no
longer depends on the fuel. Step 4.2 of `op.utf-8-decoder` [86515,90406)
restores a byte, so the queue's length alone is not a decreasing measure; the
restore happens only together with the reset of `UTF-8 bytes needed` to 0, and
the `bytesNeeded = 0` branch never restores. -/
#check (@Whatwg.Infra.Utf8.processQueue_fuel_stable :
  (mode : Whatwg.Infra.Encoding.DecoderErrorMode) → (st : Whatwg.Infra.Utf8.DecoderState) →
    (input : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
      (output : Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint) → (fuel : Nat) →
        Whatwg.Infra.Utf8.processQueueFuel input ≤ fuel →
          Whatwg.Infra.Utf8.processQueue mode st input output fuel =
            Whatwg.Infra.Utf8.processQueue mode st input output
              (Whatwg.Infra.Utf8.processQueueFuel input))

/-! Step 7's "replacement" arm of `op.process-an-item` [15509,17620): "Push
U+FFFD (�) to output." -/
#check (@Whatwg.Infra.Utf8.processItem_replacement :
  (st : Whatwg.Infra.Utf8.DecoderState) → (input : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (output : Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint) →
      (item : Whatwg.Infra.Item Whatwg.Infra.Byte) →
        (Whatwg.Infra.Utf8.decoderHandler st input item).1 =
            Whatwg.Infra.Encoding.HandlerResult.error none →
          (Whatwg.Infra.Utf8.processItem Whatwg.Infra.Encoding.DecoderErrorMode.replacement
              st input output item).2.2.2 =
            Whatwg.Infra.IoQueue.push output
              (Whatwg.Infra.Item.value Whatwg.Infra.replacementCharacter.val))

/-! Step 7's "fatal" arm of `op.process-an-item` [15509,17620): "Return
result." Nothing is pushed. -/
#check (@Whatwg.Infra.Utf8.processItem_fatal :
  (st : Whatwg.Infra.Utf8.DecoderState) → (input : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
    (output : Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint) →
      (item : Whatwg.Infra.Item Whatwg.Infra.Byte) →
        (Whatwg.Infra.Utf8.decoderHandler st input item).1 =
            Whatwg.Infra.Encoding.HandlerResult.error none →
          Whatwg.Infra.Utf8.processItem Whatwg.Infra.Encoding.DecoderErrorMode.fatal
              st input output item =
            (Whatwg.Infra.Encoding.HandlerResult.error none,
              (Whatwg.Infra.Utf8.decoderHandler st input item).2.1,
              (Whatwg.Infra.Utf8.decoderHandler st input item).2.2, output))

/-! Step 5 of `op.process-an-item` [15509,17620): "If result is finished: Push
end-of-queue to output." -/
#check (@Whatwg.Infra.Utf8.processItem_finished :
  (mode : Whatwg.Infra.Encoding.DecoderErrorMode) → (st : Whatwg.Infra.Utf8.DecoderState) →
    (input : Whatwg.Infra.IoQueue Whatwg.Infra.Byte) →
      (output : Whatwg.Infra.IoQueue Whatwg.Infra.CodePoint) →
        st.bytesNeeded = 0 →
          (Whatwg.Infra.Utf8.processItem mode st input output
              Whatwg.Infra.Item.endOfQueue).2.2.2 =
            Whatwg.Infra.IoQueue.push output Whatwg.Infra.Item.endOfQueue)


/-! ## 6. The three decode hooks

`op.utf-8-decode` [45059,45762), `op.utf-8-decode-without-bom` [45763,46180),
`op.utf-8-decode-without-bom-or-fail` [46181,46905), and their byte-sequence
faces. -/

#check (@Whatwg.Infra.Utf8.decodeWithoutBom_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decodeWithoutBom b =
      Whatwg.Infra.IoQueue.convertFrom
        (Whatwg.Infra.Utf8.decodeWithoutBomQueue (Whatwg.Infra.IoQueue.convertTo b)))

#check (@Whatwg.Infra.Utf8.decode_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decode b =
      Whatwg.Infra.IoQueue.convertFrom
        (Whatwg.Infra.Utf8.decodeQueue (Whatwg.Infra.IoQueue.convertTo b)))

#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decodeWithoutBomOrFail b =
      (Whatwg.Infra.Utf8.decodeWithoutBomOrFailQueue
        (Whatwg.Infra.IoQueue.convertTo b)).map Whatwg.Infra.IoQueue.convertFrom)

#check (@Whatwg.Infra.Utf8.decodeWithoutBomString_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decodeWithoutBomString b =
      Whatwg.Infra.JsString.ofCodePoints (Whatwg.Infra.Utf8.decodeWithoutBom b))

#check (@Whatwg.Infra.Utf8.decodeString_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decodeString b =
      Whatwg.Infra.JsString.ofCodePoints (Whatwg.Infra.Utf8.decode b))

#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFailString_eq :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decodeWithoutBomOrFailString b =
      (Whatwg.Infra.Utf8.decodeWithoutBomOrFail b).map Whatwg.Infra.JsString.ofCodePoints)

/-! Decoding yields scalar values only, for **every** byte sequence and not only
for well-formed ones: U+FFFD is itself a scalar value, and the 0xED upper
boundary keeps the surrogate range out of the accepted set. This is the strong
form of the obligation `op.process-an-item` [15509,17620) step 6.1 asserts. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_all_isScalarValue :
  (b : Whatwg.Infra.ByteSequence) →
    (Whatwg.Infra.Utf8.decodeWithoutBom b).all Whatwg.Infra.CodePoint.isScalarValue = true)

#check (@Whatwg.Infra.Utf8.decode_all_isScalarValue :
  (b : Whatwg.Infra.ByteSequence) →
    (Whatwg.Infra.Utf8.decode b).all Whatwg.Infra.CodePoint.isScalarValue = true)


/-! ## 7. Round trips

RS-1's codec round trip, at the scalar, code point and string faces, in both
error modes. -/

#check (@Whatwg.Infra.Utf8.decodeWithoutBom_encodeScalars :
  (ss : List Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Utf8.decodeWithoutBom (Whatwg.Infra.Utf8.encodeScalars ss) =
      ss.map (fun s => s.val))

#check (@Whatwg.Infra.Utf8.decodeWithoutBom_encode :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Utf8.decodeWithoutBom (Whatwg.Infra.Utf8.encode input h) =
        Whatwg.Infra.JsString.codePoints input)

/-! The fatal mode agrees with the replacement mode on the encoder's image: it
succeeds there and returns the same code points. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail_encode :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Utf8.decodeWithoutBomOrFail (Whatwg.Infra.Utf8.encode input h) =
        some (Whatwg.Infra.JsString.codePoints input))

/-! Wherever the fatal mode succeeds, the replacement mode gives the same
answer: the two modes differ only at an `error`. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq_some_imp :
  (b : Whatwg.Infra.ByteSequence) → (cs : List Whatwg.Infra.CodePoint) →
    Whatwg.Infra.Utf8.decodeWithoutBomOrFail b = some cs →
      Whatwg.Infra.Utf8.decodeWithoutBom b = cs)

/-! The string round trip. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomString_encode :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Utf8.decodeWithoutBomString (Whatwg.Infra.Utf8.encode input h) = input)

/-! The other direction, on the canonical domain: a well-formed byte sequence is
the encoding of what it decodes to. -/
#check (@Whatwg.Infra.Utf8.encode_decodeWithoutBom :
  (b : Whatwg.Infra.ByteSequence) → Whatwg.Infra.Utf8.isWellFormed b = true →
    Whatwg.Infra.Utf8.encode? (Whatwg.Infra.Utf8.decodeWithoutBomString b) = some b)


/-! ## 8. The failure set

The fail mode returns `none` exactly when the replacement mode substituted at
least one U+FFFD for an `error`. Note that this is *not* "when the output
contains U+FFFD": U+FFFD is a scalar value with a well-formed encoding, so
`errorCount` and not the output's contents is the right observation
(`INFRA-UTF8-CE-011`). -/

#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail_eq_none_iff :
  (b : Whatwg.Infra.ByteSequence) →
    (Whatwg.Infra.Utf8.decodeWithoutBomOrFail b = none ↔ 0 < Whatwg.Infra.Utf8.errorCount b))

#check (@Whatwg.Infra.Utf8.errorCount_eq_zero_iff :
  (b : Whatwg.Infra.ByteSequence) →
    (Whatwg.Infra.Utf8.errorCount b = 0 ↔ Whatwg.Infra.Utf8.isWellFormed b = true))

/-! The failure set is exactly the complement of the encoder's image, which is
`op.utf-8-decode-without-bom-or-fail` [46181,46905) read as a specification
rather than as an algorithm. -/
#check (@Whatwg.Infra.Utf8.isWellFormed_iff :
  (b : Whatwg.Infra.ByteSequence) →
    (Whatwg.Infra.Utf8.isWellFormed b = true ↔
      ∃ ss : List Whatwg.Infra.ScalarValue, b = Whatwg.Infra.Utf8.encodeScalars ss))

/-! U+FFFD in the *input* is not an error: its own encoding is well-formed. -/
#check (@Whatwg.Infra.Utf8.replacement_input_example :
  Whatwg.Infra.Utf8.errorCount [(0xEF : Whatwg.Infra.Byte), 0xBF, 0xBD] = 0 ∧
    Whatwg.Infra.Utf8.decodeWithoutBom [(0xEF : Whatwg.Infra.Byte), 0xBF, 0xBD] =
      [Whatwg.Infra.replacementCharacter.val])


/-! ## 9. The malformed classes

The note of `op.utf-8-decoder` [86515,90406): "The constraints in the UTF-8
decoder above match 'Best Practices for Using U+FFFD' from the Unicode standard.
No other behavior is permitted per the Encoding Standard." Each class carries a
quantified law and a finite probe. -/

/-! An unexpected continuation byte is one error and consumes one byte. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_unexpected_continuation :
  (b : Whatwg.Infra.Byte) → 0x80 ≤ b.toNat → b.toNat ≤ 0xBF →
    Whatwg.Infra.Utf8.decodeWithoutBom [b] = [Whatwg.Infra.replacementCharacter.val])

/-! A lead byte that begins no sequence — 0xC0, 0xC1 (the overlong two-byte
leads) and 0xF5 upward (above U+10FFFF) — is one error. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_invalid_lead :
  (b : Whatwg.Infra.Byte) → ((0xC0 ≤ b.toNat ∧ b.toNat ≤ 0xC1) ∨ 0xF5 ≤ b.toNat) →
    Whatwg.Infra.Utf8.decodeWithoutBom [b] = [Whatwg.Infra.replacementCharacter.val])

/-! A truncated sequence at end of input is **one** U+FFFD, not one per missing
byte: step 1 of `op.utf-8-decoder` [86515,90406) fires once on `end-of-queue`.
Every proper nonempty prefix of one scalar value's encoding decodes to exactly
one U+FFFD. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_truncated_one :
  (s : Whatwg.Infra.ScalarValue) → (n : Nat) → 0 < n →
    n < (Whatwg.Infra.Utf8.encodeScalar s).length →
      Whatwg.Infra.Utf8.decodeWithoutBom ((Whatwg.Infra.Utf8.encodeScalar s).take n) =
        [Whatwg.Infra.replacementCharacter.val])

/-! And a truncated sequence followed by an ASCII byte is one U+FFFD and then
that byte, because step 4.2 restores it (`INFRA-UTF8-CE-012`). -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_truncated_then_ascii_example :
  ∃ c : Whatwg.Infra.CodePoint,
    Whatwg.Infra.Utf8.decodeWithoutBom [(0xE2 : Whatwg.Infra.Byte), 0x82, 0x41] =
        [Whatwg.Infra.replacementCharacter.val, c] ∧
      c.val = 0x41)

/-! The overlong forms, at each of the three boundary rows. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_overlong_two_example :
  Whatwg.Infra.Utf8.decodeWithoutBom [(0xC0 : Whatwg.Infra.Byte), 0x80] =
    [Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val])

#check (@Whatwg.Infra.Utf8.decodeWithoutBom_overlong_three_example :
  Whatwg.Infra.Utf8.decodeWithoutBom [(0xE0 : Whatwg.Infra.Byte), 0x80, 0x80] =
    [Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val,
      Whatwg.Infra.replacementCharacter.val])

#check (@Whatwg.Infra.Utf8.decodeWithoutBom_overlong_four_example :
  Whatwg.Infra.Utf8.decodeWithoutBom [(0xF0 : Whatwg.Infra.Byte), 0x8F, 0xBF, 0xBF] =
    [Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val,
      Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val])

/-! The surrogate range, excluded by the 0xED upper boundary 0x9F. The bytes
0xED 0xA0 0x80 are the CESU-8 encoding of U+D800. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_surrogate_example :
  Whatwg.Infra.Utf8.decodeWithoutBom [(0xED : Whatwg.Infra.Byte), 0xA0, 0x80] =
    [Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val,
      Whatwg.Infra.replacementCharacter.val])

/-! Above U+10FFFF, excluded by the 0xF4 upper boundary 0x8F. The bytes
0xF4 0x90 0x80 0x80 would be U+110000. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_above_max_example :
  Whatwg.Infra.Utf8.decodeWithoutBom [(0xF4 : Whatwg.Infra.Byte), 0x90, 0x80, 0x80] =
    [Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val,
      Whatwg.Infra.replacementCharacter.val, Whatwg.Infra.replacementCharacter.val])

/-! The last valid scalar value, U+10FFFF, is accepted: the 0xF4 boundary is
0x8F inclusive and not exclusive. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_max_example :
  ∃ c : Whatwg.Infra.CodePoint,
    Whatwg.Infra.Utf8.decodeWithoutBom [(0xF4 : Whatwg.Infra.Byte), 0x8F, 0xBF, 0xBF] = [c] ∧
    c.val = 0x10FFFF)

/-! And the last code point below the surrogates, U+D7FF, is accepted by the
0xED boundary. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_before_surrogates_example :
  ∃ c : Whatwg.Infra.CodePoint,
    Whatwg.Infra.Utf8.decodeWithoutBom [(0xED : Whatwg.Infra.Byte), 0x9F, 0xBF] = [c] ∧
    c.val = 0xD7FF)

/-! Each malformed class fails the fatal mode. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBomOrFail_malformed_example :
  Whatwg.Infra.Utf8.decodeWithoutBomOrFail [(0xC0 : Whatwg.Infra.Byte), 0x80] = none ∧
    Whatwg.Infra.Utf8.decodeWithoutBomOrFail [(0xED : Whatwg.Infra.Byte), 0xA0, 0x80] = none ∧
      Whatwg.Infra.Utf8.decodeWithoutBomOrFail
          [(0xF4 : Whatwg.Infra.Byte), 0x90, 0x80, 0x80] = none ∧
        Whatwg.Infra.Utf8.decodeWithoutBomOrFail [(0xE2 : Whatwg.Infra.Byte), 0x82] = none ∧
          Whatwg.Infra.Utf8.decodeWithoutBomOrFail [(0x80 : Whatwg.Infra.Byte)] = none)


/-! ## 10. The byte order mark

`op.utf-8-decode` [45059,45762) steps 1 and 2, against
`op.utf-8-decode-without-bom` [45763,46180). The note of `op.utf-8-decoder`
[86515,90406): "A byte order mark has priority over a label … Therefore it is
not part of the UTF-8 decoder algorithm, but rather the decode and UTF-8 decode
algorithms." -/

#check (@Whatwg.Infra.Utf8.decode_bom_prefix :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decode (Whatwg.Infra.Utf8.bom ++ b) =
      Whatwg.Infra.Utf8.decodeWithoutBom b)

/-! Exactly once. The second byte order mark is data and decodes to U+FEFF. -/
#check (@Whatwg.Infra.Utf8.decode_bom_once :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.Utf8.decode (Whatwg.Infra.Utf8.bom ++ Whatwg.Infra.Utf8.bom ++ b) =
      Whatwg.Infra.Utf8.decodeWithoutBom (Whatwg.Infra.Utf8.bom ++ b))

#check (@Whatwg.Infra.Utf8.decode_bom_twice_example :
  ∃ c : Whatwg.Infra.CodePoint,
    Whatwg.Infra.Utf8.decode (Whatwg.Infra.Utf8.bom ++ Whatwg.Infra.Utf8.bom) = [c] ∧
    c.val = 0xFEFF)

#check (@Whatwg.Infra.Utf8.decode_bom_only_example :
  Whatwg.Infra.Utf8.decode Whatwg.Infra.Utf8.bom = [])

/-! Anything that is not the three-byte mark is left alone, including its own
two-byte prefix, which decodes to one U+FFFD. -/
#check (@Whatwg.Infra.Utf8.decode_no_bom :
  (b : Whatwg.Infra.ByteSequence) →
    Whatwg.Infra.ByteSequence.startsWith b Whatwg.Infra.Utf8.bom = false →
      Whatwg.Infra.Utf8.decode b = Whatwg.Infra.Utf8.decodeWithoutBom b)

#check (@Whatwg.Infra.Utf8.decode_partial_bom_example :
  Whatwg.Infra.Utf8.decode [(0xEF : Whatwg.Infra.Byte), 0xBB] =
    [Whatwg.Infra.replacementCharacter.val])

/-! `op.utf-8-decode-without-bom` [45763,46180) does not strip: that is the
whole difference between the two hooks. -/
#check (@Whatwg.Infra.Utf8.decodeWithoutBom_keeps_bom_example :
  ∃ c : Whatwg.Infra.CodePoint,
    Whatwg.Infra.Utf8.decodeWithoutBom Whatwg.Infra.Utf8.bom = [c] ∧ c.val = 0xFEFF)


/-! ## 11. Get an encoder, encode or fail, and the profiles

`op.get-an-encoder` [50829,51166) and `op.encode-or-fail` [51167,53203). -/

#check (@Whatwg.Infra.Encoding.Name.hasEncoder_iff :
  (n : Whatwg.Infra.Encoding.Name) →
    (Whatwg.Infra.Encoding.Name.hasEncoder n = false ↔
      (n = Whatwg.Infra.Encoding.Name.replacement ∨ n = Whatwg.Infra.Encoding.Name.utf16be ∨
        n = Whatwg.Infra.Encoding.Name.utf16le)))

/-! `rule.iso-2022-jp-encoder-stateful` [123264,124113): the pin names exactly
one stateful encoder. A stateful encoder's answers are not a function of its
input's scalar values taken independently, which is why the caller must keep the
instance alive (`INFRA-UTF8-CE-014`). -/
#check (@Whatwg.Infra.Encoding.Name.isStateful_iff :
  (n : Whatwg.Infra.Encoding.Name) →
    (Whatwg.Infra.Encoding.Name.isStateful n = true ↔
      n = Whatwg.Infra.Encoding.Name.iso2022jp))

/-! This packet owns one encoder algorithm. Everything else is a DB-02
profile. -/
#check (@Whatwg.Infra.Encoding.Name.isOwned_iff :
  (n : Whatwg.Infra.Encoding.Name) →
    (Whatwg.Infra.Encoding.Name.isOwned n = true ↔ n = Whatwg.Infra.Encoding.Name.utf8))

#check (@Whatwg.Infra.Encoding.getAnEncoder?_utf8 :
  Whatwg.Infra.Encoding.getAnEncoder? Whatwg.Infra.Encoding.Name.utf8 =
    some Whatwg.Infra.Encoding.Encoder.utf8)

#check (@Whatwg.Infra.Encoding.getAnEncoder?_eq_none :
  (n : Whatwg.Infra.Encoding.Name) → Whatwg.Infra.Encoding.Name.hasEncoder n = false →
    Whatwg.Infra.Encoding.getAnEncoder? n = none)

#check (@Whatwg.Infra.Encoding.getAnEncoder?_eq_some :
  (n : Whatwg.Infra.Encoding.Name) → (h : Whatwg.Infra.Encoding.Name.hasEncoder n = true) →
    Whatwg.Infra.Encoding.getAnEncoder? n = some (Whatwg.Infra.Encoding.getAnEncoder n h))

#check (@Whatwg.Infra.Encoding.Encoder.name_utf8 :
  Whatwg.Infra.Encoding.Encoder.name Whatwg.Infra.Encoding.Encoder.utf8 =
    Whatwg.Infra.Encoding.Name.utf8)

/-! `op.encode-or-fail` [51167,53203) over UTF-8's encoder on a whole immediate
queue: one answer, the whole encoding, and a null `potentialError`. The note of
`op.encode` [50170,50822) is the reason: "Layering UTF-8 encode on top is safe
as it never triggers errors." -/
#check (@Whatwg.Infra.Encoding.encodeOrFail_utf8 :
  (ss : List Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Encoding.encodeOrFail Whatwg.Infra.Encoding.Encoder.utf8
        (Whatwg.Infra.IoQueue.convertTo ss) =
      some (Whatwg.Infra.Encoding.EncodeAnswer.mk (Whatwg.Infra.Utf8.encodeScalars ss) none,
        Whatwg.Infra.Encoding.Encoder.utf8))

/-! UTF-8 always answers, and never with an error. -/
#check (@Whatwg.Infra.Encoding.encodeOrFail_utf8_never_errors :
  (q : Whatwg.Infra.IoQueue Whatwg.Infra.ScalarValue) →
    (answer : Whatwg.Infra.Encoding.EncodeAnswer) →
      (next : Whatwg.Infra.Encoding.Encoder) →
        Whatwg.Infra.Encoding.encodeOrFail Whatwg.Infra.Encoding.Encoder.utf8 q =
            some (answer, next) →
          Whatwg.Infra.Encoding.EncodeAnswer.potentialError answer = none)

/-! A foreign encoder answers from its tape and the instance advances: this is
DB-02's "the answer is first-order data on a tape" and it is what makes
ISO-2022-JP's retained state observable. -/
#check (@Whatwg.Infra.Encoding.encodeOrFail_foreign_advances :
  (n : Whatwg.Infra.Encoding.Name) → (answer : Whatwg.Infra.Encoding.EncodeAnswer) →
    (rest : Whatwg.Infra.Encoding.EncoderTape) →
      (q : Whatwg.Infra.IoQueue Whatwg.Infra.ScalarValue) →
        Whatwg.Infra.Encoding.encodeOrFail
            (Whatwg.Infra.Encoding.Encoder.foreign n (answer :: rest)) q =
          some (answer, Whatwg.Infra.Encoding.Encoder.foreign n rest))

/-! An exhausted tape is an unanswered decision: a live frontier, never an
error. -/
#check (@Whatwg.Infra.Encoding.encodeOrFail_foreign_frontier :
  (n : Whatwg.Infra.Encoding.Name) → (q : Whatwg.Infra.IoQueue Whatwg.Infra.ScalarValue) →
    Whatwg.Infra.Encoding.encodeOrFail (Whatwg.Infra.Encoding.Encoder.foreign n []) q = none)

/-! The tape's own termination test, in the shape
`Whatwg.Url.Boundary.EncoderTape.terminated_iff` already carries on
`url/u3-builder`: step 7 of `op.percent-encode-after-encoding` of
`vendor/whatwg-url-55d66993/url.bs` [21624,24696) loops "While potentialError is
non-null". -/
#check (@Whatwg.Infra.Encoding.EncoderTape.terminated_iff :
  (tape : Whatwg.Infra.Encoding.EncoderTape) →
    (Whatwg.Infra.Encoding.EncoderTape.terminated tape = true ↔
      ∃ answer : Whatwg.Infra.Encoding.EncodeAnswer, tape.getLast? = some answer ∧
        Whatwg.Infra.Encoding.EncodeAnswer.potentialError answer = none))


/-! ## 12. The U3 tapes' UTF-8 profile, discharged

`Whatwg.Infra` cannot import `Whatwg.Url`, so these two theorems state the
profile in Infra's own vocabulary. They are exactly what
`Whatwg.Url.Boundary.Utf8Encoding.tape` and
`Whatwg.Url.Boundary.Utf8DecodeOrFail.failed` on `url/u3-builder` assume, and
the later URL revision that turns those two records into views onto the owned
codec discharges them by rewriting with these names. That revision, not this
packet, closes the `encoding` obligation of
`docs/URL-PERCENT-ENCODING-DAG.md`. -/

/-! `Whatwg.Url.Boundary.Utf8Encoding.tape`: "UTF-8 encodes every scalar value,
so the run is one answer whose `potentialError` is null and whose output is the
whole encoding; step 7's loop therefore runs exactly once." -/
#check (@Whatwg.Infra.Utf8.u3Profile_encoderTape :
  (input : Whatwg.Infra.JsString) →
    (h : Whatwg.Infra.JsString.isScalarValueString input = true) →
      Whatwg.Infra.Encoding.encodeOrFail Whatwg.Infra.Encoding.Encoder.utf8
            (Whatwg.Infra.IoQueue.convertTo (Whatwg.Infra.Utf8.scalars input h)) =
          some (Whatwg.Infra.Encoding.EncodeAnswer.mk
              (Whatwg.Infra.Utf8.encode input h) none, Whatwg.Infra.Encoding.Encoder.utf8) ∧
        Whatwg.Infra.Encoding.EncoderTape.terminated
            [Whatwg.Infra.Encoding.EncodeAnswer.mk (Whatwg.Infra.Utf8.encode input h) none] =
          true)

/-! `Whatwg.Url.Boundary.Utf8DecodeOrFail.failed`, as
`requirement.percent-encoded-utf8-advice` of
`vendor/whatwg-url-55d66993/url.bs` [16325,16862) reads it: the boundary's
`failed` field is a function of the bytes, and this is that function. -/
#check (@Whatwg.Infra.Utf8.u3Profile_decodeOrFail :
  (b : Whatwg.Infra.ByteSequence) →
    ((Whatwg.Infra.Utf8.decodeWithoutBomOrFail b).isNone = true ↔
      Whatwg.Infra.Utf8.isWellFormed b = false))
