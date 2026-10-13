import Whatwg.Css.Syntax.Laws.Name

/-!
# Whatwg.Css.Syntax.Laws.Number

Owner: numbers read back (slice K2 of `docs/CSS-PACKAGE-PLAN.md`; proof graph
`CSS-PG-SYNTAX`).

- `consumeNumber_integer`, `consumeNumber_fraction`: what `consumeNumber` returns for a sign,
  digits, and a full stop and digits, before a text that does not go on the number. These are
  about the tokenizer alone.
- `decimal_value`: the digits that `Numeric.text` writes are the value, exactly.
- `consumeNumber_text`: **the number comes back**: its value, its type and its sign character.
-/

namespace Whatwg.Css.Syntax

/-! ## Digits -/

theorem isDigit_digitChar {k : Nat} (h : k < 10) : isDigit (Nat.digitChar k) = true := by
  simp only [isDigit, Nat.toNat_digitChar_of_lt_ten h, Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem isDigit_of_mem_toDigits (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    rw [Nat.toDigits_eq_if (by decide)] at hc
    split at hc
    · rename_i hlt
      rw [List.mem_singleton] at hc
      rw [hc]
      exact isDigit_digitChar hlt
    · rw [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · rw [hc]
        exact isDigit_digitChar (Nat.mod_lt n (by decide))

theorem isDigit_of_mem_fixedDigits (k n : Nat) : ∀ c ∈ fixedDigits k n, isDigit c = true := by
  intro c hc
  simp only [fixedDigits, List.mem_append, List.mem_replicate] at hc
  rcases hc with ⟨-, rfl⟩ | hc
  · decide
  · exact isDigit_of_mem_toDigits n c hc

theorem length_fixedDigits (k n : Nat) (hk : 0 < k) (hn : n < 10 ^ k) :
    (fixedDigits k n).length = k := by
  have := (Nat.length_toDigits_le_iff (b := 10) (n := n) (by decide) hk).mpr hn
  simp only [fixedDigits, List.length_append, List.length_replicate]
  omega

theorem ofDigitChars_fixedDigits (k n : Nat) : Nat.ofDigitChars 10 (fixedDigits k n) 0 = n := by
  simp only [fixedDigits, Nat.ofDigitChars_append, Nat.ofDigitChars_replicate_zero, Nat.mul_zero,
    Nat.ofDigitChars_ten_toDigits]

/-- The digits of a whole part and of `k` places after the full stop, read as one number. -/
theorem ofDigitChars_toDigits_fixedDigits (a b k : Nat) (hk : 0 < k) (hb : b < 10 ^ k) :
    Nat.ofDigitChars 10 (Nat.toDigits 10 a ++ fixedDigits k b) 0 = 10 ^ k * a + b := by
  rw [Nat.ofDigitChars_append, Nat.ofDigitChars_ten_toDigits, Nat.ofDigitChars_eq_ofDigitChars_zero,
    length_fixedDigits k b hk hb, ofDigitChars_fixedDigits]

/-! ## The steps of `consume-number` -/

theorem consumeSign_text (sign : Option Sign) (d : Char) (rest : List Char)
    (hd : isDigit d = true) : consumeSign (signText sign ++ d :: rest) = (sign, d :: rest) := by
  cases sign with
  | none =>
    have h₁ : d ≠ '+' := by rintro rfl; exact absurd hd (by decide)
    have h₂ : d ≠ '-' := by rintro rfl; exact absurd hd (by decide)
    simp only [signText, List.nil_append, consumeSign, List.getElem?_cons_zero, Option.some.injEq, h₁,
      h₂, if_false]
  | some s => cases s <;> rfl

theorem consumeDigits_append (digits rest : List Char) (hd : ∀ c ∈ digits, isDigit c = true)
    (hr : rest[0]?.any isDigit = false) : consumeDigits (digits ++ rest) = (digits, rest) := by
  have h₁ : rest.takeWhile isDigit = [] := by
    cases rest with
    | nil => rfl
    | cons c rest =>
      simp only [List.getElem?_cons_zero, Option.any_some] at hr
      simp only [List.takeWhile_cons, hr, Bool.false_eq_true, if_false]
  have h₂ : rest.dropWhile isDigit = rest := by
    cases rest with
    | nil => rfl
    | cons c rest =>
      simp only [List.getElem?_cons_zero, Option.any_some] at hr
      simp only [List.dropWhile_cons, hr, Bool.false_eq_true, if_false]
  simp only [consumeDigits, List.takeWhile_append_of_pos hd, List.dropWhile_append_of_pos hd, h₁, h₂,
    List.append_nil]

theorem consumeFraction_none (rest : List Char)
    (h : ¬(rest[0]? = some '.' ∧ rest[1]?.any isDigit = true)) :
    consumeFraction rest = (none, rest) := by
  simp only [consumeFraction, h, if_false]

theorem consumeFraction_text (d : Char) (digits rest : List Char) (hd : isDigit d = true)
    (hds : ∀ c ∈ digits, isDigit c = true) (hr : rest[0]?.any isDigit = false) :
    consumeFraction ('.' :: d :: (digits ++ rest)) = (some (d :: digits), rest) := by
  have hall : ∀ c ∈ d :: digits, isDigit c = true := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact hds c hc
  have := consumeDigits_append (d :: digits) rest hall hr
  rw [List.cons_append] at this
  simp only [consumeFraction, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.any_some, hd,
    and_self, if_true, List.drop_succ_cons, List.drop_zero, this]

/-- A text that does not start with `E` or `e` starts no exponent. -/
theorem consumeExponent_none (rest : List Char)
    (h : rest[0]? ≠ some 'E' ∧ rest[0]? ≠ some 'e') : consumeExponent rest = (none, rest) := by
  simp only [consumeExponent, h.1, h.2, or_self, if_false]

/-- **The tokenizer reads a whole number**: a sign, digits, and then a text that does not go
on the number. -/
theorem consumeNumber_integer (sign : Option Sign) (d : Char) (digits tail : List Char)
    (hd : isDigit d = true) (hds : ∀ c ∈ digits, isDigit c = true)
    (h₁ : tail[0]?.any isDigit = false)
    (h₂ : ¬(tail[0]? = some '.' ∧ tail[1]?.any isDigit = true))
    (h₃ : consumeExponent tail = (none, tail)) :
    consumeNumber (signText sign ++ d :: (digits ++ tail)) =
      ((decimal (sign == some .minus) (d :: digits) [], .integer, sign), tail) := by
  have hall : ∀ c ∈ d :: digits, isDigit c = true := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact hds c hc
  have hA := consumeSign_text sign d (digits ++ tail) hd
  have hB := consumeDigits_append (d :: digits) tail hall h₁
  rw [List.cons_append] at hB
  simp only [consumeNumber, hA, hB, consumeFraction_none tail h₂, h₃, Option.getD_none,
    Option.isSome_none, Bool.or_self, Bool.false_eq_true, if_false]

/-- **The tokenizer reads a number with a fraction**: a sign, digits, a full stop, digits, and
then a text that does not go on the number. -/
theorem consumeNumber_fraction (sign : Option Sign) (d : Char) (digits : List Char) (e : Char)
    (places tail : List Char) (hd : isDigit d = true) (hds : ∀ c ∈ digits, isDigit c = true)
    (he : isDigit e = true) (hps : ∀ c ∈ places, isDigit c = true)
    (h₁ : tail[0]?.any isDigit = false) (h₃ : consumeExponent tail = (none, tail)) :
    consumeNumber (signText sign ++ d :: (digits ++ '.' :: e :: (places ++ tail))) =
      ((decimal (sign == some .minus) (d :: digits) (e :: places), .number, sign), tail) := by
  have hall : ∀ c ∈ d :: digits, isDigit c = true := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact hds c hc
  have hA := consumeSign_text sign d (digits ++ '.' :: e :: (places ++ tail)) hd
  have hB := consumeDigits_append (d :: digits) ('.' :: e :: (places ++ tail)) hall rfl
  rw [List.cons_append] at hB
  simp only [consumeNumber, hA, hB, consumeFraction_text e places tail he hps h₁, h₃,
    Option.getD_some, Option.isSome_some, Bool.true_or, if_true]

/-! ## The value -/

/-- **The digits are the value.** A value whose denominator divides `10 ^ k`, written as its
numerator scaled to `k` places, is read back exactly. -/
theorem decimal_value (v : Rat) (negative : Bool) (k : Nat) (whole fraction : List Char)
    (hsign : (negative = true ∧ v.num ≤ 0) ∨ (negative = false ∧ 0 ≤ v.num))
    (hden : 10 ^ k % v.den = 0) (hk : fraction.length = k)
    (hval : Nat.ofDigitChars 10 (whole ++ fraction) 0 = v.num.natAbs * (10 ^ k / v.den)) :
    decimal negative whole fraction = v := by
  have hq : v.den * (10 ^ k / v.den) = 10 ^ k := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hden)
  have hq0 : 10 ^ k / v.den ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hq
    exact absurd hq.symm (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide)))
  have hmag : ((Nat.ofDigitChars 10 (whole ++ fraction) 0 : Nat) : Rat) /
      ((10 ^ fraction.length : Nat) : Rat) = mkRat (v.num.natAbs : Int) v.den := by
    rw [hval, hk]
    have e₁ : ((v.num.natAbs * (10 ^ k / v.den) : Nat) : Rat) / ((10 ^ k : Nat) : Rat) =
        mkRat ((v.num.natAbs : Int) * ((10 ^ k / v.den : Nat) : Int)) (v.den * (10 ^ k / v.den)) := by
      rw [hq]
      exact (Rat.mkRat_eq_div _ _).symm
    rw [e₁]
    exact Rat.mkRat_mul_right hq0
  unfold decimal
  simp only [hmag]
  rcases hsign with ⟨rfl, hnum⟩ | ⟨rfl, hnum⟩
  · simp only [if_true, Rat.neg_mkRat]
    rw [← Int.eq_neg_natAbs_of_nonpos hnum, Rat.mkRat_self]
  · simp only [Bool.false_eq_true, if_false]
    rw [Int.natAbs_of_nonneg hnum, Rat.mkRat_self]

theorem Numeric.sign_cases (n : Numeric) (flag : NumberFlag) (h : n.writable flag = true) :
    ((n.sign == some .minus) = true ∧ n.value.num ≤ 0) ∨
      ((n.sign == some .minus) = false ∧ 0 ≤ n.value.num) := by
  obtain ⟨value, sign⟩ := n
  simp only [Numeric.writable, Bool.and_eq_true] at h
  obtain ⟨h, -⟩ := h
  cases sign with
  | none => exact Or.inr ⟨rfl, of_decide_eq_true h⟩
  | some s =>
    cases s with
    | plus => exact Or.inr ⟨rfl, of_decide_eq_true h⟩
    | minus => exact Or.inl ⟨rfl, of_decide_eq_true h⟩

/-- The digits of a whole number start with a digit. -/
theorem toDigits_cons (n : Nat) :
    ∃ d digits, Nat.toDigits 10 n = d :: digits ∧ isDigit d = true ∧
      ∀ c ∈ digits, isDigit c = true := by
  have hall := isDigit_of_mem_toDigits n
  cases h : Nat.toDigits 10 n with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons d digits =>
    rw [h] at hall
    exact ⟨d, digits, rfl, hall d (List.mem_cons_self), fun c hc => hall c (List.mem_cons_of_mem d hc)⟩

/-- **A number comes back**: before a text that does not go on it, `consumeNumber` returns the
value, the type and the sign character that `Numeric.text` wrote. -/
theorem consumeNumber_text (n : Numeric) (flag : NumberFlag) (tail : List Char)
    (hn : n.writable flag = true) (h₁ : tail[0]?.any isDigit = false)
    (h₂ : ¬(tail[0]? = some '.' ∧ tail[1]?.any isDigit = true))
    (h₃ : consumeExponent tail = (none, tail)) :
    consumeNumber (n.text flag ++ tail) = ((n.value, flag, n.sign), tail) := by
  have hsign := n.sign_cases flag hn
  cases flag with
  | integer =>
    have hden : n.value.den = 1 := by
      simp only [Numeric.writable, Bool.and_eq_true, beq_iff_eq] at hn
      exact hn.2
    obtain ⟨d, digits, hdigits, hd, hds⟩ := toDigits_cons n.value.num.natAbs
    have htext : n.text .integer = signText n.sign ++ (d :: digits) := by
      simp only [Numeric.text, Numeric.places, hden, Nat.pow_zero, Nat.div_one, Nat.mul_one, ↓reduceIte,
        List.append_nil, hdigits]
    have hvalue : decimal (n.sign == some .minus) (d :: digits) [] = n.value := by
      refine decimal_value n.value _ 0 _ _ hsign ?_ rfl ?_
      · rw [hden]
      · rw [List.append_nil, ← hdigits, Nat.ofDigitChars_ten_toDigits, hden, Nat.pow_zero, Nat.div_one,
          Nat.mul_one]
    rw [htext, List.append_assoc, List.cons_append,
      consumeNumber_integer n.sign d digits tail hd hds h₁ h₂ h₃, hvalue]
  | number =>
    have hk : 0 < n.places .number := by
      simp only [Numeric.places]
      omega
    have hden : 10 ^ n.places .number % n.value.den = 0 := by
      simp only [Numeric.writable, Bool.and_eq_true, beq_iff_eq] at hn
      exact hn.2
    have hlt : n.value.num.natAbs * (10 ^ n.places .number / n.value.den) % 10 ^ n.places .number <
        10 ^ n.places .number := Nat.mod_lt _ (Nat.pow_pos (by decide))
    obtain ⟨d, digits, hdigits, hd, hds⟩ := toDigits_cons
      (n.value.num.natAbs * (10 ^ n.places .number / n.value.den) / 10 ^ n.places .number)
    have hplaces := isDigit_of_mem_fixedDigits (n.places .number)
      (n.value.num.natAbs * (10 ^ n.places .number / n.value.den) % 10 ^ n.places .number)
    have hlen := length_fixedDigits (n.places .number) _ hk hlt
    cases hfixed : fixedDigits (n.places .number)
        (n.value.num.natAbs * (10 ^ n.places .number / n.value.den) % 10 ^ n.places .number) with
    | nil =>
      rw [hfixed] at hlen
      exact absurd hlen (by simp only [List.length_nil]; omega)
    | cons e places =>
      rw [hfixed] at hplaces
      have htext : n.text .number = signText n.sign ++ (d :: digits ++ '.' :: e :: places) := by
        simp only [Numeric.text, hdigits, hfixed, Nat.ne_of_gt hk, if_false]
      have hvalue : decimal (n.sign == some .minus) (d :: digits) (e :: places) = n.value := by
        apply decimal_value n.value _ (n.places .number) _ _ hsign hden
        · rw [← hfixed]
          exact hlen
        · rw [← hdigits, ← hfixed, ofDigitChars_toDigits_fixedDigits _ _ _ hk hlt, Nat.mul_comm (10 ^ _)]
          exact Nat.div_add_mod' _ _
      simp only [htext, List.append_assoc, List.cons_append]
      rw [consumeNumber_fraction n.sign d digits e places tail hd hds
          (hplaces e (List.mem_cons_self)) (fun c hc => hplaces c (List.mem_cons_of_mem e hc)) h₁ h₃, hvalue]

end Whatwg.Css.Syntax
