import Whatwg.Css.Syntax.Laws.Number

/-!
# Whatwg.Css.Syntax.Laws.String

Owner: escapes and strings read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph
`CSS-PG-SYNTAX`).

- `consumeEscapedCodePoint_hex`: **an escape as a code point comes back.** The hexadecimal
  digits that CSSOM's "escape a character as code point" writes, and the space after them, are
  read as the code point, for every code point but U+0000.
- `consumeStringValue_text`: **a string comes back**, whatever it holds but U+0000: its
  quotation marks and reverse solidi escaped, its control characters escaped as code points.
-/

namespace Whatwg.Css.Syntax

/-! ## Hexadecimal digits -/

theorem hexDigit_digitChar :
    ∀ k : Nat, k < 16 → isHexDigit (Nat.digitChar k) = true ∧ hexDigitValue (Nat.digitChar k) = k := by
  decide

theorem hexValue_append_singleton (digits : List Char) (d : Char) :
    hexValue (digits ++ [d]) = 16 * hexValue digits + hexDigitValue d := by
  simp only [hexValue, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The hexadecimal digits of a number are hex digits, and they are read as the number. -/
theorem hex_toDigits (n : Nat) :
    (∀ c ∈ Nat.toDigits 16 n, isHexDigit c = true) ∧ hexValue (Nat.toDigits 16 n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · rename_i hlt
      obtain ⟨h₁, h₂⟩ := hexDigit_digitChar n hlt
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [List.mem_singleton] at hc
        rw [hc]
        exact h₁
      · simp only [hexValue, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add, h₂]
    · obtain ⟨ih₁, ih₂⟩ := ih (n / 16) (by omega)
      obtain ⟨h₁, h₂⟩ := hexDigit_digitChar (n % 16) (Nat.mod_lt n (by decide))
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact ih₁ c hc
        · rw [hc]
          exact h₁
      · rw [hexValue_append_singleton, ih₂, h₂]
        omega

theorem takeWhile_take_append (p : Char → Bool) (digits : List Char) (x : Char) (rest : List Char)
    (n : Nat) (hlen : digits.length ≤ n) (hall : ∀ c ∈ digits, p c = true) (hx : p x = false) :
    ((digits ++ x :: rest).take n).takeWhile p = digits := by
  induction digits generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.nil_append, List.take_succ_cons, List.takeWhile_cons, hx, Bool.false_eq_true, if_false]
  | cons d digits ih =>
    cases n with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ n =>
      simp only [List.length_cons] at hlen
      have hd := hall d List.mem_cons_self
      simp only [List.cons_append, List.take_succ_cons, List.takeWhile_cons, hd, if_true,
        ih n (by omega) (fun c hc => hall c (List.mem_cons_of_mem d hc))]

theorem drop_length_append (l₁ l₂ : List Char) : (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ with
  | nil => rfl
  | cons c l₁ ih => simp only [List.cons_append, List.length_cons, List.drop_succ_cons, ih]

/-! ## Escapes -/

theorem consumeEscapedCodePoint_of_not_hex (c : Char) (rest : List Char)
    (h : isHexDigit c = false) : consumeEscapedCodePoint (c :: rest) = (c, rest) := by
  simp only [consumeEscapedCodePoint, h, Bool.false_eq_true, if_false]

/-- **An escape as a code point comes back.** -/
theorem consumeEscapedCodePoint_hex (c : Char) (rest : List Char) (hc : c.toNat ≠ 0) :
    consumeEscapedCodePoint (Nat.toDigits 16 c.toNat ++ ' ' :: rest) = (c, rest) := by
  obtain ⟨hall, hvalue⟩ := hex_toDigits c.toNat
  have hvalid : c.toNat < 55296 ∨ (57343 < c.toNat ∧ c.toNat < 1114112) := c.valid
  have hlen : (Nat.toDigits 16 c.toNat).length ≤ 6 :=
    (Nat.length_toDigits_le_iff (b := 16) (by decide) (by decide)).mpr (by omega)
  cases hdigits : Nat.toDigits 16 c.toNat with
  | nil => exact absurd hdigits Nat.toDigits_ne_nil
  | cons d more =>
    rw [hdigits] at hall hvalue hlen
    simp only [List.length_cons] at hlen
    have hmore : ((more ++ ' ' :: rest).take 5).takeWhile isHexDigit = more :=
      takeWhile_take_append isHexDigit more ' ' rest 5 (by omega)
        (fun x hx => hall x (List.mem_cons_of_mem d hx)) (by decide)
    have hcode : codePointOfHex c.toNat = c := by
      have h₁ : ¬(c.toNat = 0 ∨ (0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF) ∨ 0x10FFFF < c.toNat) := by omega
      simp only [codePointOfHex, h₁, if_false, Char.ofNat_toNat]
    simp only [List.cons_append, consumeEscapedCodePoint, hall d List.mem_cons_self, if_true, hmore,
      hvalue, hcode, drop_length_append, List.getElem?_cons_zero, Option.any_some, List.drop_succ_cons,
      List.drop_zero]
    rfl

/-! ## Strings -/

theorem consumeStringValue_ending (ending : Char) (rest : List Char) :
    consumeStringValue ending (ending :: rest) = (some [], rest) := by
  rw [consumeStringValue.eq_def]
  simp only [if_true]

theorem consumeStringValue_plain (ending c : Char) (rest : List Char) (h₁ : c ≠ ending)
    (h₂ : isNewline c = false) (h₃ : c ≠ '\\') :
    consumeStringValue ending (c :: rest) =
      ((consumeStringValue ending rest).1.map (c :: ·), (consumeStringValue ending rest).2) := by
  rw [consumeStringValue.eq_def]
  simp only [h₁, if_false, h₂, Bool.false_eq_true, h₃]

theorem consumeStringValue_escape (ending d : Char) (rest : List Char) (he : '\\' ≠ ending)
    (hd : isNewline d = false) :
    consumeStringValue ending ('\\' :: d :: rest) =
      ((consumeStringValue ending (consumeEscapedCodePoint (d :: rest)).2).1.map
          ((consumeEscapedCodePoint (d :: rest)).1 :: ·),
        (consumeStringValue ending (consumeEscapedCodePoint (d :: rest)).2).2) := by
  rw [consumeStringValue.eq_def]
  simp only [he, if_false, hd, Bool.false_eq_true, if_true]
  rfl

/-- The text of one code point of a string, read back before the rest of the string. -/
theorem consumeStringValue_codePoint (c : Char) (tail : List Char) (hc : c.toNat ≠ 0) :
    consumeStringValue '"' (serializeStringCodePoint c ++ tail) =
      ((consumeStringValue '"' tail).1.map (c :: ·), (consumeStringValue '"' tail).2) := by
  by_cases hcontrol : isControl c = true
  · have hdigits := hex_toDigits c.toNat
    cases hd : Nat.toDigits 16 c.toNat with
    | nil => exact absurd hd Nat.toDigits_ne_nil
    | cons d more =>
      have hescape := consumeEscapedCodePoint_hex c tail hc
      rw [hd] at hescape hdigits
      have hhex : isHexDigit d = true := hdigits.1 d List.mem_cons_self
      have hnl : isNewline d = false := by
        simp only [isHexDigit, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hhex
        simp only [isNewline, beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [serializeStringCodePoint, hc, if_false, hcontrol, if_true, escapeAsCodePoint, hd,
        List.cons_append, List.append_assoc, List.nil_append]
      rw [consumeStringValue_escape '"' d _ (by decide) hnl]
      rw [List.cons_append] at hescape
      rw [hescape]
  · by_cases hq : c = '"' ∨ c = '\\'
    · have hhex : isHexDigit c = false := by
        rcases hq with rfl | rfl <;> decide
      have hnl : isNewline c = false := by
        rcases hq with rfl | rfl <;> decide
      simp only [serializeStringCodePoint, hc, if_false, hcontrol, Bool.false_eq_true, hq, if_true,
        escapeCharacter, List.cons_append, List.nil_append]
      rw [consumeStringValue_escape '"' c _ (by decide) hnl,
        consumeEscapedCodePoint_of_not_hex c tail hhex]
    · have hnl : isNewline c = false := by
        simp only [isControl, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcontrol
        simp only [isNewline, beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [serializeStringCodePoint, hc, if_false, hcontrol, Bool.false_eq_true, hq, List.cons_append,
        List.nil_append]
      exact consumeStringValue_plain '"' c tail (fun e => hq (Or.inl e)) hnl (fun e => hq (Or.inr e))

/-- **A string comes back.** The value between quotation marks, then the closing quotation
mark and any text: `consumeStringValue` returns the value and that text. -/
theorem consumeStringValue_text (value rest : List Char)
    (hv : (value.all fun c => c.toNat != 0) = true) :
    consumeStringValue '"' (serializeStringValue value ++ '"' :: rest) = (some value, rest) := by
  induction value with
  | nil => exact consumeStringValue_ending '"' rest
  | cons c value ih =>
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
    rw [serializeStringValue, List.append_assoc, consumeStringValue_codePoint c _ hv.1, ih hv.2]
    rfl

theorem consumeToken_quotationMark (rest : List Char) (allowed : Bool) :
    consumeToken ('"' :: rest) allowed = some (consumeStringToken '"' rest) := by
  rw [consumeToken, consumeComments_cons_of_ne '"' rest (by decide)]
  rfl

end Whatwg.Css.Syntax
