import OMAStatements.S_oeis_a328002
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open OMA.S_oeis_a328002

namespace AdjacentRatios

private def w (n : ℕ) : ℚ := 2^n * ∏ i ∈ Finset.range n, factor (i+1)

private lemma w_pos (n : ℕ) : 0 < w n := by
  apply mul_pos (by positivity) (Finset.prod_pos ?_)
  intro i _
  unfold factor
  split <;> positivity

private lemma w_succ (n : ℕ) : w (n+1) = 2 * w n * factor (n+1) := by
  simp only [w, Finset.prod_range_succ, pow_succ]
  ring

private lemma a_succ (n : ℕ) : a (n+1) = 2 * a n + w (n+1) := by
  unfold a w
  rw [Finset.sum_range_succ, pow_succ]
  ring

private lemma w_odd (m : ℕ) : w (2*m+1) = (2*(m:ℚ)+1)*w (2*m) := by
  rw [w_succ]
  simp [factor]
  ring

private lemma w_next (m : ℕ) : w (2*m+1+1) = 2 / ((m:ℚ)+1) * w (2*m+1) := by
  rw [w_succ]
  have h : (2*m+1+1)%2 = 0 := by omega
  simp [factor, h]
  field_simp
  ring

private lemma a_even (m : ℕ) :
    a (2*m) = ((m:ℚ)+3) * (2*m+1) / 3 * w (2*m) := by
  induction m with
  | zero => norm_num [a, w]
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega, a_succ, a_succ, ih, w_next, w_odd]
    push_cast
    field_simp
    ring

private lemma a_odd (m : ℕ) :
    a (2*m+1) = (2*(m:ℚ)+9)*(2*m+1)/3*w (2*m) := by
  rw [a_succ, a_even, w_odd]
  ring

private lemma ratio_even (m : ℕ) : q (2*m) = 2 + (3:ℚ)/((m:ℚ)+3) := by
  rw [q, a_odd, a_even]
  have h := (w_pos (2*m)).ne'
  have h₁ : (2*(m:ℚ)+1) ≠ 0 := by positivity
  have h₃ : ((m:ℚ)+3) ≠ 0 := by positivity
  field_simp
  ring

private lemma ratio_odd (m : ℕ) : q (2*m+1) = 2 + (6:ℚ)/(((m:ℚ)+1)*(2*m+9)) := by
  rw [q, a_succ, a_odd, w_next, w_odd]
  have h := (w_pos (2*m)).ne'
  have h₁ : (2*(m:ℚ)+1) ≠ 0 := by positivity
  have h₉ : (2*(m:ℚ)+9) ≠ 0 := by positivity
  field_simp
  ring

private lemma num_mul (r : ℚ) : (r.num : ℚ) = r * r.den :=
  (div_eq_iff (Nat.cast_ne_zero.mpr r.den_ne_zero)).mp r.num_div_den

private lemma diff_two (r : ℚ) : (2+r).num - 2*((2+r).den:ℤ) = r.num := by
  have h := num_mul (2+r)
  simp only [Rat.ofNat_add_den] at h ⊢
  exact_mod_cast (by rw [h, num_mul r]; ring : ((2+r).num:ℚ) - 2*(r.den:ℚ) = (r.num:ℚ))

private lemma small_num (k b : ℕ) (hb : 0 < b) :
    ((k:ℚ)/b).num = (k:ℤ) / (Nat.gcd (b%k) k : ℕ) := by
  rw [Rat.natCast_div_eq_divInt, Rat.divInt_ofNat, Rat.num_mkRat, if_neg hb.ne']
  simp only [Int.natAbs_natCast]
  rw [Nat.gcd_comm b k, Nat.gcd_rec k b]

private lemma even_values (m : ℕ) :
    d (2*m) = ([1,2,3,3,3,2,1,1,3,6,3,1] : List ℤ)[(2*m)%12]! := by
  rw [d, ratio_even, diff_two]
  have he := small_num 3 (m+3) (by omega)
  push_cast at he
  rw [he]
  have h : (m+3)%3 = (m%6+3)%3 := by omega
  rw [h]
  have ht : (2*m)%12 = (2*(m%6))%12 := by omega
  rw [ht]
  have hm : m%6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases m%6 <;> decide

private lemma odd_values (m : ℕ) :
    d (2*m+1) = ([1,2,3,3,3,2,1,1,3,6,3,1] : List ℤ)[(2*m+1)%12]! := by
  rw [d, ratio_odd, diff_two]
  have he := small_num 6 ((m+1)*(2*m+9)) (by positivity)
  push_cast at he
  rw [he]
  have em := (Nat.mod_modEq m 6).symm
  have h : ((m+1)*(2*m+9))%6 = ((m%6+1)*(2*(m%6)+9))%6 :=
    (em.add_right 1).mul ((em.mul_left 2).add_right 9)
  rw [h]
  have ht : (2*m+1)%12 = (2*(m%6)+1)%12 := by omega
  rw [ht]
  have hm : m%6 < 6 := Nat.mod_lt _ (by decide)
  interval_cases m%6 <;> decide

end AdjacentRatios

theorem OMA.solution : type_of% @OMA.S_oeis_a328002.main := by
  intro n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · simpa [show n = 2*m by omega] using AdjacentRatios.even_values m
  · simpa [show n = 2*m+1 by omega] using AdjacentRatios.odd_values m
