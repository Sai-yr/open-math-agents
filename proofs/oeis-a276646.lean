import OMAStatements.S_oeis_a276646
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

open OMA.S_oeis_a276646

namespace DecimalMeans

private lemma sum_linear (A : ℚ) (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (A+i)) = (m:ℚ)*(2*A+m-1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    linear_combination ih

private lemma block_bound (d m : ℕ) (hm : m ≤ 9*10^d) :
    (∑ i ∈ Finset.range m, decimalFraction (10^d+i)) ≤ (m:ℚ)*11/20 := by
  let A : ℚ := 10^d
  have ha : 0 < A := by dsimp [A]; positivity
  have hterm (i : ℕ) (hi : i < m) : decimalFraction (10^d+i) = (A+i)/(10*A) := by
    have hl : Nat.log 10 (10^d+i) = d := Nat.log_eq_of_pow_le_of_lt_pow (by omega)
      (by rw [pow_succ]; omega)
    simp [decimalFraction,hl,A,pow_succ',Nat.cast_add]
  have hs : (∑ i ∈ Finset.range m, decimalFraction (10^d+i)) =
      (∑ i ∈ Finset.range m, (A+i))/(10*A) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i hi => hterm i (Finset.mem_range.mp hi))
  rw [hs,div_le_iff₀ (by positivity)]
  have hmq : (m:ℚ) ≤ 9*A := by dsimp [A]; exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left (by linarith : 2*A+m-1 ≤ 11*A) (by positivity : 0 ≤ (m:ℚ))
  nlinarith [sum_linear A m]

private lemma all_sums (n : ℕ) : (∑ i ∈ Finset.range n, decimalFraction (i+1)) ≤ (n:ℚ)*11/20 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · simp [hn]
    let d := Nat.log 10 n
    let a := 10^d
    let m := n-a+1
    have hz : 0<a := by dsimp [a]; positivity
    have hlo : a ≤ n := Nat.pow_log_le_self _ hn
    have hhi : n < a*10 := by simpa [a,d,pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 10) n
    have hm : m ≤ 9*10^d := by change m ≤ 9*a; dsimp [m]; omega
    have he : n = (a-1)+m := by dsimp [m]; omega
    have hA := ih (a-1) (by omega)
    have hB := block_bound d m hm
    change (∑ i ∈ Finset.range m, decimalFraction (a+i)) ≤ _ at hB
    have hidx (i : ℕ) : a-1+i+1 = a+i := by omega
    rw [he, Finset.sum_range_add, Nat.cast_add]
    simp only [hidx]
    linarith

end DecimalMeans

theorem OMA.solution : type_of% @OMA.S_oeis_a276646.main := by
  intro n hn
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  linarith [DecimalMeans.all_sums n]
