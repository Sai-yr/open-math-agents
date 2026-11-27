import OMAStatements.S_oeis_a220181
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.FieldTheory.Finite.Basic

open Finset OMA.S_oeis_a220181

namespace ToppleablePeriod

private theorem term_vanishes {n k : ℕ} (h : n < k) : term n k = 0 := by
  have hz := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h) 0
  rw [fwdDiff_iter_eq_sum_shift] at hz
  have hsum : (∑ i ∈ range (k+1), (-1 : ℤ)^(k-i) *
      (k.choose i : ℤ) * (i : ℤ)^n) = 0 := by
    simpa [zsmul_eq_mul] using hz
  simp [term, hsum]

private theorem pow_period {p : ℕ} [Fact p.Prime] (x : ZMod p) {n : ℕ}
    (hn : 1 ≤ n) : x^(n+(p-1)) = x^n := by
  rw [pow_add]
  by_cases hx : x = 0
  · simp [hx, zero_pow (by omega : n ≠ 0)]
  · rw [ZMod.pow_card_sub_one_eq_one hx, mul_one]

private theorem term_period {p : ℕ} [Fact p.Prime] (n k : ℕ) (hn : 1 ≤ n) :
    (term (n+(p-1)) k : ZMod p) = (term n k : ZMod p) := by
  simp only [term, Int.cast_mul, Int.cast_pow, Int.cast_sum, pow_period _ hn]

theorem periodic (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    (a (n+(p-1)) : ZMod p) = (a n : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  simp only [a, Int.cast_sum]
  simp_rw [term_period n _ hn]
  symm
  apply sum_subset (range_mono (by omega))
  intro k _ hk
  rw [term_vanishes (by simpa [Nat.succ_le_iff] using hk), Int.cast_zero]

end ToppleablePeriod

theorem OMA.solution : type_of% @OMA.S_oeis_a220181.main :=
  ToppleablePeriod.periodic
