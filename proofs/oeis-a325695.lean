import OMAStatements.S_oeis_a325695

namespace OMA.S_oeis_a325695

private def parts (n u : ℕ) := (Finset.range (n+7)).filter (fun v => 3*u+2*v ≤ n)
private def P (n : ℕ) := ∑ u ∈ Finset.range (n/3+1), ((n-3*u)/2+1)
private def Q (n : ℕ) := if n%2=0 then n/4+1 else 0

-- At weight n+6, write a=u+1, b=u+v+2, c=u+v+w+3.
-- The unrestricted condition is 3u+2v≤n; the forbidden equality is 4u+2v=n.
private theorem good_row (n u : ℕ) :
    (Finset.range (n+6+1)).filter (fun v => allowed (n+6) u v) =
      (parts n u).filter (fun v => ¬ 4*u+2*v=n) := by
  ext v
  simp only [Finset.mem_filter,Finset.mem_range,parts,allowed,decide_eq_true_eq]
  omega

private theorem counted_row (n u : ℕ) :
    ((parts n u).filter (fun v => 4*u+2*v=n)).card =
      if n%2=0 ∧ u<n/4+1 then 1 else 0 := by
  split_ifs with h
  · have heq : (parts n u).filter (fun v => 4*u+2*v=n) = {(n-4*u)/2} := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton,parts]
      omega
    rw [heq,Finset.card_singleton]
  · have heq : (parts n u).filter (fun v => 4*u+2*v=n) = ∅ := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_range,parts,Finset.notMem_empty,iff_false]
      omega
    rw [heq,Finset.card_empty]

private theorem all_row (n u : ℕ) : (parts n u).card =
    if u<n/3+1 then (n-3*u)/2+1 else 0 := by
  split_ifs with h
  · have heq : parts n u = Finset.range ((n-3*u)/2+1) := by
      ext v
      simp only [parts,Finset.mem_filter,Finset.mem_range]
      omega
    rw [heq,Finset.card_range]
  · have heq : parts n u = ∅ := by
      ext v
      simp only [parts,Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false]
      omega
    simp [heq]

private theorem restrict_sum (N k : ℕ) (hk : k≤N) (f : ℕ → ℕ) :
    (∑ u ∈ Finset.range N, if u<k then f u else 0) = ∑ u ∈ Finset.range k, f u := by
  rw [← Finset.sum_filter]
  congr 1
  ext u
  simp [Finset.mem_filter,Finset.mem_range]
  omega

private theorem count (n : ℕ) : Q n+term (n+6)=P n := by
  have hall : ∑ u ∈ Finset.range (n+7), (parts n u).card = P n := by
    simp_rw [all_row]
    exact restrict_sum _ _ (by omega) _
  have hbad : ∑ u ∈ Finset.range (n+7), ((parts n u).filter (fun v => 4*u+2*v=n)).card = Q n := by
    simp_rw [counted_row]
    by_cases h : n%2=0
    · simp only [h,true_and,Q,if_true]
      rw [restrict_sum _ _ (by omega)]
      simp
    · simp [h,Q]
  rw [← hbad,term,← hall]
  simp_rw [good_row]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.card_filter_add_card_filter_not (s := parts n u) (fun v => 4*u+2*v=n)

private theorem shiftP (n : ℕ) : P (n+6) = P n+n+6 := by
  unfold P
  rw [show (n+6)/3+1 = 2+(n/3+1) by omega, Finset.sum_range_add]
  have h : (∑ j ∈ Finset.range (n/3+1), ((n+6-3*(2+j))/2+1)) =
      ∑ j ∈ Finset.range (n/3+1), ((n-3*j)/2+1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show n+6-3*(2+j)=n-3*j by omega]
  rw [h]
  simp [Finset.sum_range_succ]
  omega

private theorem shift12 (n : ℕ) (hn : 0<n) :
    (term (n+12) : ℤ) = term n+2*(n:ℤ)+6-(if n%2=0 then 3 else 0) := by
  by_cases hl : n < 6
  · interval_cases n <;> decide +kernel
  · obtain ⟨m,hm⟩ : ∃ m, n=m+6 := ⟨n-6,by omega⟩
    subst n
    have p₁ := shiftP m
    have p₂ := shiftP (m+6)
    have a := count m
    have b := count (m+12)
    rw [show m+12+6=m+6+12 by omega] at b
    rw [show m+6+6=m+12 by omega] at p₂
    unfold Q at a b
    have h₂ : (m+12)%2=m%2 := by omega
    have h₃ : (m+6)%2=m%2 := by omega
    rw [h₂] at b
    rw [h₃]
    split_ifs at * <;> omega

private def recurrenceAt (k : ℕ) : Prop :=
  term (k+10)+term (k+5)+term (k+4)+term (k+3) = term (k+8)+term (k+7)+term (k+6)+term (k+1)

private theorem recurrence (k : ℕ) : recurrenceAt k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hsmall : k < 12
    · interval_cases k <;> unfold recurrenceAt <;> decide +kernel
    · obtain ⟨j,hj⟩ : ∃ j, k=j+12 := ⟨k-12,by omega⟩
      subst k
      have h := ih j (by omega)
      unfold recurrenceAt at h ⊢
      have h' (d : ℕ) (hd : 0<d) : (term (j+12+d) : ℤ) =
          term (j+d)+2*((j+d:ℕ):ℤ)+6-(if (j+d)%2=0 then 3 else 0) := by
        rw [show j+12+d=j+d+12 by omega]
        exact shift12 _ (by omega)
      apply Int.ofNat_inj.mp
      push_cast
      rw [h' 10 (by decide),h' 5 (by decide),h' 4 (by decide),h' 3 (by decide),
        h' 8 (by decide),h' 7 (by decide),h' 6 (by decide),h' 1 (by decide)]
      by_cases he : j%2=0
      · simp only [if_pos (by omega : (j+10)%2=0), if_neg (by omega : (j+5)%2≠0),
          if_pos (by omega : (j+4)%2=0), if_neg (by omega : (j+3)%2≠0),
          if_pos (by omega : (j+8)%2=0), if_neg (by omega : (j+7)%2≠0),
          if_pos (by omega : (j+6)%2=0), if_neg (by omega : (j+1)%2≠0)]
        omega
      · simp only [if_neg (by omega : (j+10)%2≠0), if_pos (by omega : (j+5)%2=0),
          if_neg (by omega : (j+4)%2≠0), if_pos (by omega : (j+3)%2=0),
          if_neg (by omega : (j+8)%2≠0), if_pos (by omega : (j+7)%2=0),
          if_neg (by omega : (j+6)%2≠0), if_pos (by omega : (j+1)%2=0)]
        omega

open PowerSeries in
private theorem generating :
    ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series = X^7*(1+X+2*X^2) := by
  have coeff_s (d : ℕ) : coeff d series = (term d : ℚ) := by simp [series]
  have shift (d j : ℕ) : coeff d ((X: PowerSeries ℚ)^j*series) =
      if j≤d then (term (d-j):ℚ) else 0 := by rw [coeff_X_pow_mul']; simp only [coeff_s]
  have hden : ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series =
      series-X^2*series-X^3*series-X^4*series+X^5*series+X^6*series+X^7*series-X^9*series := by ring
  have hnum : (X^7*(1+X+2*X^2) : PowerSeries ℚ) = X^7+X^8+X^9+X^9 := by ring
  rw [hden,hnum]
  ext n
  simp only [map_sub,map_add,shift,coeff_X_pow,coeff_s]
  by_cases hl : n<10
  · interval_cases n <;> decide +kernel
  · obtain ⟨k,hk⟩ : ∃ k, n=k+10 := ⟨n-10,by omega⟩
    subst n
    have h := recurrence k
    unfold recurrenceAt at h
    have hc : (term (k+10) : ℚ)+term (k+5)+term (k+4)+term (k+3) =
        term (k+8)+term (k+7)+term (k+6)+term (k+1) := by exact_mod_cast h
    simp (disch := omega) only [if_pos,if_neg]
    simp only [show k+10-2=k+8 by omega, show k+10-3=k+7 by omega, show k+10-4=k+6 by omega,
      show k+10-5=k+5 by omega, show k+10-6=k+4 by omega, show k+10-7=k+3 by omega,
      show k+10-9=k+1 by omega]
    linarith

end OMA.S_oeis_a325695

open OMA.S_oeis_a325695 in
theorem OMA.solution : type_of% @OMA.S_oeis_a325695.main := ⟨recurrence,generating⟩
