import OMAStatements.S_oeis_a184894

namespace OMA.S_oeis_a184894

open Polynomial

private noncomputable def reduced (n : ℕ) := (iteratePoly n).map (Nat.castRingHom (ZMod 3))

private theorem reduce_coeff (n k : ℕ) :
    (reduced n).coeff k = ((iteratePoly n).coeff k : ZMod 3) := by simp [reduced]

-- In characteristic three, cubing replaces X by X³ and fixes the coefficients.
private theorem step (n k : ℕ) : (reduced (n+1)).coeff k =
    (reduced n).coeff k + if 3 ∣ k then (reduced n).coeff (k/3) else 0 := by
  have h : (reduced n)^3=expand (ZMod 3) 3 (reduced n) := by
    rw [← map_frobenius_expand 3,ZMod.frobenius_zmod,map_id]
  have hi : reduced (n+1)=reduced n+(reduced n)^3 := by simp [reduced,iteratePoly]
  rw [hi,h,coeff_add,coeff_expand (by decide : 0 < 3)]

private theorem support_at (n k : ℕ) (h : ∀ j : ℕ, k≠3^j) : (reduced n).coeff k=0 := by
  induction n generalizing k with
  | zero =>
    have h1 : k≠1 := by simpa using h 0
    simp [reduced,iteratePoly,coeff_X,Ne.symm h1]
  | succ n ih =>
    rw [step,ih k h,zero_add]
    by_cases hd : 3 ∣ k
    · rw [if_pos hd]
      apply ih
      intro j hq
      apply h (j+1)
      rw [pow_succ,← hq,Nat.div_mul_cancel hd]
    · simp [hd]

-- On the remaining powers of three the coefficients obey Pascal's recurrence.
private theorem powers (n j : ℕ) : (reduced n).coeff (3^j)=(n.choose j : ZMod 3) := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [reduced,iteratePoly]
    | succ j =>
      have h : 1 < (3:ℕ)^(j+1) := Nat.one_lt_pow (by omega) (by decide)
      simp [reduced,iteratePoly,coeff_X,h.ne]
  | succ n ih =>
    cases j with
    | zero => simpa [step] using ih 0
    | succ j =>
      rw [step,if_pos (dvd_pow_self 3 (by omega)),ih,show (3:ℕ)^(j+1)/3=3^j by
        rw [pow_succ,Nat.mul_div_cancel _ (by decide)],ih,Nat.choose_succ_succ,Nat.cast_add,add_comm]

private theorem at_candidate (j : ℕ) :
    (term ((3^j+1)/2) : ZMod 3)=(((3^j+1)/2 : ℕ).choose j : ZMod 3) := by
  have odd : Odd ((3:ℕ)^j) := (by decide : Odd (3:ℕ)).pow
  obtain ⟨u,hu⟩ := odd
  unfold term
  rw [show 2*((3^j+1)/2)-1=3^j by omega,← reduce_coeff,powers]

end OMA.S_oeis_a184894

open OMA.S_oeis_a184894 in
theorem OMA.solution : type_of% @OMA.S_oeis_a184894.main := by
  refine ⟨?_,at_candidate,?_⟩
  · intro m hm h
    by_contra! hh
    apply h
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    unfold term
    rw [← reduce_coeff]
    apply support_at
    intro j he
    apply hh j
    omega
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    have h := at_candidate 6
    change (term 365 : ZMod 3) = ((365:ℕ).choose 6 : ZMod 3) at h
    rw [h]
    norm_num [Nat.choose_eq_descFactorial_div_factorial]
    decide +kernel
