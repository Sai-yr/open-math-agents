import OMAStatements.S_mo_449981
import Mathlib.Tactic

open Finset PowerSeries OMA.S_mo_449981

namespace PowerPartitions

private lemma geometric_step {k : ℕ} (hk : 0 < k) :
    geometric k = 1 + geometric k * X^k := by
  ext d
  rw [map_add, coeff_one, coeff_mul_X_pow']
  simp only [geometric, coeff_mk]
  by_cases hd : d=0
  · simp [hd, hk.not_ge]
  · by_cases he : k ≤ d
    · have hdiv : k ∣ d-k ↔ k ∣ d := Nat.dvd_sub_iff_left he (dvd_refl _)
      simp [hd,he,hdiv]
    · have hn : ¬k ∣ d := fun h => he (Nat.le_of_dvd (by omega) h)
      simp [hd,he,hn]

private lemma coefficient_step (F : PowerSeries ℕ) {k : ℕ} (hk : 0 < k) (d : ℕ) :
    coeff d (F*geometric k) = coeff d F +
      if k ≤ d then coeff (d-k) (F*geometric k) else 0 := by
  calc
    _ = coeff d (F*(1+geometric k*X^k)) := congrArg (fun G => coeff d (F*G)) (geometric_step hk)
    _ = _ := by rw [mul_add,mul_one,← mul_assoc,map_add,coeff_mul_X_pow']

/-- Repeatedly remove one copy of the largest allowed part. -/
private lemma split_largest (F : PowerSeries ℕ) {k : ℕ} (hk : 0 < k) (q : ℕ) :
    coeff (k*(q+1)-1) (F*geometric k) =
      ∑ i ∈ range (q+1), coeff (k*(i+1)-1) F := by
  induction q with
  | zero =>
    simp only [zero_add,mul_one,sum_range_one]
    rw [coefficient_step F hk, if_neg (by omega), add_zero]
  | succ q ih =>
    have hkp : 0 < k*(q+1) := Nat.mul_pos hk (by omega)
    have hsum : k*(q+1+1) = k*(q+1)+k := by ring
    rw [coefficient_step F hk, if_pos (by omega : k ≤ k*(q+1+1)-1),
      show k*(q+1+1)-1-k = k*(q+1)-1 by omega, ih, sum_range_succ (n := q+1)]
    exact add_comm _ _

private lemma count (m : ℕ) (hm : 0 < m) (n q : ℕ) :
    R m n q = coeff (m^(n+1)*(q+1)-1) (series m n) := by
  induction n generalizing q with
  | zero => simp [R,series,geometric,coeff_mk]
  | succ n ih =>
    let k := m^(n+1)
    have hk : 0 < k := pow_pos hm _
    have hmQ : 0 < m*(q+1) := Nat.mul_pos hm (by omega)
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero hmQ.ne'
    have he : m^(n+1+1)*(q+1) = k*(b+1) := by
      rw [pow_succ, mul_assoc,hb]
    rw [R,series,he,hb]
    exact (sum_congr rfl (fun i _ => ih i)).trans (split_largest (series m n) hk b).symm

end PowerPartitions

theorem OMA.solution : type_of% @OMA.S_mo_449981.main := by
  intro m n hm
  simpa using PowerPartitions.count m hm n 0
