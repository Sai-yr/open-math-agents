import OMAStatements.S_oeis_a073642

namespace OMA.S_oeis_a073642

private def v (k : ℕ) := padicValNat 2 k
private def first (n : ℕ) := ∑ j ∈ Finset.range n, v (j+1)
private def second (n : ℕ) := ∑ j ∈ Finset.range n, (v (j+1))^2

private theorem first_succ (n : ℕ) : first (n+1)=first n+v (n+1) := Finset.sum_range_succ _ _
private theorem second_succ (n : ℕ) : second (n+1)=second n+(v (n+1))^2 := Finset.sum_range_succ _ _

private theorem v_odd (m : ℕ) : v (2*m+1)=0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

private theorem v_double (m : ℕ) (hm : 0 < m) : v (2*m)=1+v m := by
  unfold v
  rw [padicValNat.mul (by decide) (by omega), padicValNat_self]

-- Pair the valuations at 2j-1 and 2j. In the square moment the
-- extra mixed term is exactly twice the first moment.
private theorem doubled (m : ℕ) :
    first (2*m)=first m+m ∧ second (2*m)=second m+2*first m+m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega,first_succ (2*m+1),first_succ (2*m),
      second_succ (2*m+1),second_succ (2*m),v_odd,show 2*m+1+1=2*(m+1) by omega,
      v_double _ (by omega),ih.1,ih.2,first_succ m,second_succ m]
    constructor <;> ring

private theorem position_shift (L : List ℕ) : (L.map (·+1)).sum=L.sum+L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]; omega

private theorem digital (n : ℕ) :
    n.bitIndices.length+first n=n ∧ 2*n.bitIndices.sum+second n=3*first n := by
  induction n using Nat.binaryRec with
  | zero => decide
  | bit b m ih =>
    have h := doubled m
    cases b
    · simp only [Nat.bit_false,Nat.bitIndices_two_mul,List.length_map,position_shift,h.1,h.2]
      constructor <;> omega
    · simp only [Nat.bit_true,Nat.bitIndices_two_mul_add_one,first_succ (2*m),second_succ (2*m),v_odd,h.1,h.2]
      simp only [List.length_cons,List.length_map,List.sum_cons,zero_add,zero_pow (by decide : 2 ≠ 0),
        add_zero,position_shift]
      constructor <;> omega

end OMA.S_oeis_a073642

open OMA.S_oeis_a073642 in
theorem OMA.solution : type_of% @OMA.S_oeis_a073642.main := by
  intro n _
  have h := digital n
  change 2*n.bitIndices.sum+second n=3*(n-n.bitIndices.length)
  rw [h.2]
  omega
