import OMAStatements.S_oeis_a349958
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace PascalRows

private lemma triangle_dvd {n m : ℕ} (h : 2 * n ∣ m * (m - 1)) :
    n ∣ m.choose 2 := by
  obtain ⟨c, hc⟩ := h
  use c
  rw [Nat.choose_two_right, hc, Nat.mul_assoc]
  omega

/-- The complementary CRT residues r and 2ab+1-r yield triangular numbers
divisible by ab. At least one of their rows is strictly between 1 and ab. -/
private lemma earlier_of_odd {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (hab : a.Coprime b) (hbo : Odd b) :
    ∃ m : ℕ, 2 ≤ m ∧ m < a*b ∧ a*b ∣ m.choose 2 := by
  let n := a*b
  have hmod : (2*a).Coprime b := Nat.coprime_mul_iff_left.mpr ⟨hbo.coprime_two_left, hab⟩
  let x := Nat.chineseRemainder hmod 0 1
  let r : ℕ := x.val
  have hbound : r < 2*n := by
    simpa [n, Nat.mul_assoc] using Nat.chineseRemainder_lt_mul hmod 0 1 (by positivity) (by omega)
  have hz : 2*a ∣ r := Nat.modEq_zero_iff_dvd.mp x.property.1
  have hone : r ≡ 1 [MOD b] := x.property.2
  have ha_r : a ∣ r := dvd_trans (dvd_mul_left a 2) hz
  have hr0 : r ≠ 0 := by
    intro h
    have heq : 0 % b = 1 % b := h ▸ hone
    simp [Nat.mod_eq_of_lt hb] at heq
  have hr1 : r ≠ 1 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 1) (h ▸ ha_r)
    omega
  have hb_r : b ∣ r - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ r)).mp hone.symm
  have ha_n : a ∣ n := dvd_mul_right _ _
  have hb_n : b ∣ n := dvd_mul_left _ _
  have hrn : r ≠ n := by
    intro h
    simp [Nat.ModEq, h, Nat.mod_eq_zero_of_dvd hb_n, Nat.mod_eq_of_lt hb] at hone
  have hrn1 : r ≠ n + 1 := by
    intro h
    have had : a ∣ n + 1 := h ▸ ha_r
    have had1 : a ∣ 1 := by simpa using Nat.dvd_sub had ha_n
    have := Nat.le_of_dvd (by decide : 0 < 1) had1
    omega
  by_cases hlt : r < n
  · refine ⟨r, by omega, hlt, triangle_dvd ?_⟩
    simpa [n, Nat.mul_assoc] using Nat.mul_dvd_mul hz hb_r
  · let s := 2*n + 1 - r
    have hs0 : 2 ≤ s := by dsimp [s]; omega
    have hsn : s < n := by dsimp [s]; omega
    have h2an : 2*a ∣ 2*n := by
      change 2*a ∣ 2*(a*b)
      exact Nat.mul_dvd_mul_left _ ha_n
    have hbs : b ∣ s := by
      have h := Nat.dvd_sub (dvd_mul_of_dvd_right hb_n 2) hb_r
      convert h using 1
      dsimp [s]
      omega
    have has : 2*a ∣ s-1 := by
      have h := Nat.dvd_sub h2an hz
      convert h using 1
      dsimp [s]
      omega
    refine ⟨s, hs0, hsn, triangle_dvd ?_⟩
    simpa [n, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_dvd_mul hbs has

private lemma earlier {n : ℕ} (hn : 1 < n) (hnp : ¬ IsPrimePow n) :
    ∃ m : ℕ, 2 ≤ m ∧ m < n ∧ n ∣ m.choose 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    exact (hnp ((isPrimePow_nat_iff _).2 ⟨p, e, hp, he, rfl⟩)).elim
  | zero => omega
  | one => omega
  | coprime a b ha hb hab _ _ =>
    by_cases ho : Odd b
    · exact earlier_of_odd ha hb hab ho
    · have hb2 : 2 ∣ b := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
      have haodd : Odd a := by
        apply Nat.coprime_two_right.mp
        exact hab.coprime_dvd_right hb2
      simpa [mul_comm] using earlier_of_odd hb ha hab.symm haodd

end PascalRows

open OMA.S_oeis_a349958

theorem OMA.solution : type_of% @OMA.S_oeis_a349958.main := by
  intro n hn
  constructor
  · intro hmin
    by_contra hnp
    by_cases h1 : n = 1
    · subst n
      have h : 1 ≤ 0 := hmin.2 (show containsMultiple 1 0 from ⟨0, by decide, by decide⟩)
      omega
    obtain ⟨m, hm, hmn, hd⟩ := PascalRows.earlier (by omega) hnp
    have h : n ≤ m := hmin.2 (show containsMultiple n m from ⟨2, hm, hd⟩)
    omega
  · intro hpp
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    refine ⟨⟨1, hn, by simp⟩, ?_⟩
    rintro m ⟨k, hk, hd⟩
    have hp1 : 1 < p^e := one_lt_pow₀ hp.one_lt he.ne'
    have hm : 0 < m := by
      by_contra! hm
      have hm0 : m = 0 := by omega
      have hk0 : k = 0 := by omega
      have h1 : p ^ e ∣ 1 := by simpa [hm0, hk0] using hd
      have := Nat.le_of_dvd (by decide : 0 < 1) h1
      omega
    have hexp := (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hk)).mp hd
    exact (Nat.pow_le_pow_right hp.pos hexp).trans (Nat.pow_factorization_choose_le hm)
