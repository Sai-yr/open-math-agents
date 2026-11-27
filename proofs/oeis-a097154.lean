import OMAStatements.S_oeis_a097154

open OMA.S_oeis_a097154

namespace ReverseMaxDigit

private lemma ofDigits_zero_iff (l : List ℕ) :
    Nat.ofDigits 10 l = 0 ↔ ∀ d ∈ l, d = 0 := by
  induction l with
  | nil => simp
  | cons d l ih => simp [Nat.ofDigits_cons, ih]

/-- In a decimal word of at least three digits, a strictly larger reversal
exceeds the original by at least ten. -/
private lemma gap_at_ends {a b : ℕ} {middle : List ℕ}
    (ha : a < 10) (hb : b < 10) (hd : ∀ d ∈ middle, d < 10) :
    let n := Nat.ofDigits 10 (b :: (middle ++ [a]))
    let r := Nat.ofDigits 10 (a :: (middle.reverse ++ [b]))
    100 ≤ n → n < r → n + 10 ≤ r := by
  dsimp only
  simp only [Nat.ofDigits_cons, Nat.ofDigits_append, List.length_reverse]
  intro hn hlt
  by_cases hempty : middle = []
  · subst middle
    simp at hn
    omega
  let q := 10 ^ middle.length
  let u := Nat.ofDigits 10 middle
  let v := Nat.ofDigits 10 middle.reverse
  change 100 ≤ b + 10 * (u + q * a) at hn
  change b + 10 * (u + q * a) < a + 10 * (v + q * b) at hlt
  change b + 10 * (u + q * a) + 10 ≤ a + 10 * (v + q * b)
  have hq : 10 ≤ q := by
    exact (Nat.pow_one 10).symm.le.trans
      (Nat.pow_le_pow_right (by decide) (List.length_pos_iff.mpr hempty))
  have hu : u < q := Nat.ofDigits_lt_base_pow_length (by decide) hd
  have hv : v < q := by
    have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10)
      (l := middle.reverse) (by simpa using hd)
    simpa [v, q] using h
  rcases lt_trichotomy a b with hab | heq | hba
  · have hp := Nat.mul_le_mul_left q (show a + 1 ≤ b from hab)
    rw [Nat.mul_add, Nat.mul_one] at hp
    by_cases hv0 : v = 0
    · have hu0 : u = 0 := by
        apply (ofDigits_zero_iff middle).2
        simpa using (ofDigits_zero_iff middle.reverse).1 hv0
      omega
    · omega
  · subst b
    omega
  · have hp := Nat.mul_le_mul_left q (show b + 1 ≤ a from hba)
    rw [Nat.mul_add, Nat.mul_one] at hp
    omega

private lemma gap (l : List ℕ) (hd : ∀ d ∈ l, d < 10)
    (hn : 100 ≤ Nat.ofDigits 10 l) (hlt : Nat.ofDigits 10 l < Nat.ofDigits 10 l.reverse) :
    Nat.ofDigits 10 l + 10 ≤ Nat.ofDigits 10 l.reverse := by
  cases l with
  | nil => simp at hn
  | cons b rest =>
    cases hx : rest.reverse with
    | nil =>
      have : rest = [] := by simpa using congrArg List.reverse hx
      simp [this] at hlt
    | cons a inside =>
      have he : rest = inside.reverse ++ [a] := by simpa using congrArg List.reverse hx
      subst rest
      have hb := hd b (by simp)
      have ha := hd a (by simp)
      have hmid : ∀ d ∈ inside.reverse, d < 10 := fun d h => hd d (by simp [h])
      have hrev : (b :: (inside.reverse ++ [a])).reverse = a :: (inside.reverse.reverse ++ [b]) := by
        simp [List.reverse_cons]
      rw [hrev] at hlt ⊢
      exact gap_at_ends ha hb hmid hn hlt

private lemma small : ∀ x : Fin 100, f x = x → x.val = 0 ∨ x.val = 89 := by
  decide

end ReverseMaxDigit

theorem OMA.solution : type_of% @OMA.S_oeis_a097154.main := by
  ext x
  change f x = x ↔ x = 0 ∨ x = 89
  constructor
  · intro h
    by_cases hx : x < 100
    · exact ReverseMaxDigit.small ⟨x, hx⟩ h
    have digits_bound : ∀ d ∈ Nat.digits 10 x, d < 10 :=
      fun d hd => Nat.digits_lt_base (by decide) hd
    have hmax : maxDigit x ≤ 9 := by
      exact List.max_le_of_forall_le _ _ fun d hd => Nat.le_of_lt_succ (digits_bound d hd)
    have hpos : 0 < maxDigit x := by
      by_contra! hzero
      have hz : Nat.ofDigits 10 (Nat.digits 10 x) = 0 := by
        apply (ReverseMaxDigit.ofDigits_zero_iff _).2
        intro d hd
        have hle : d ≤ maxDigit x := List.le_max_of_le hd le_rfl
        omega
      rw [Nat.ofDigits_digits] at hz
      omega
    change reverse x - maxDigit x = x at h
    have hrev : x < reverse x := by omega
    have hgap := ReverseMaxDigit.gap (Nat.digits 10 x) digits_bound
      (by rw [Nat.ofDigits_digits]; omega)
      (by simpa only [Nat.ofDigits_digits, reverse] using hrev)
    rw [Nat.ofDigits_digits] at hgap
    change x + 10 ≤ reverse x at hgap
    omega
  · rintro (rfl | rfl) <;> decide
