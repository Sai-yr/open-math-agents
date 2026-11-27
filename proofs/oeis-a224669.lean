import OMAStatements.S_oeis_a224669

namespace OMA.S_oeis_a224669

-- The nine row states satisfy the same recurrence. Appending one row
-- applies the same linear operator to each of the three vectors.
private theorem vector (k : ℕ) : ∀ r, completions (k+4) r+completions (k+1) r =
    2*completions (k+3) r := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    intro r
    change (∑ s, if compatible r s then completions (k+4) s else 0) +
        (∑ s, if compatible r s then completions (k+1) s else 0) =
      2*(∑ s, if compatible r s then completions (k+3) s else 0)
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    cases h : compatible r s <;> simp [ih]

private theorem recur (k : ℕ) : term (k+4)+term (k+1)=2*term (k+3) := by
  unfold term
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => vector k r)

private theorem recur_all (k : ℕ) : term (k+3)+term k=2*term (k+2) := by
  cases k with
  | zero => decide +kernel
  | succ k => exact recur k

private theorem affine (k : ℕ) : term (k+2)=term (k+1)+term k+4 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    have h := recur_all k
    change term (k+3) = term (k+2)+term (k+1)+4
    omega

private theorem closed (n : ℕ) : (term n : ℝ) =
    -4 + ((1-Real.sqrt 5)^n*(-19+13*Real.sqrt 5)+(1+Real.sqrt 5)^n*(19+13*Real.sqrt 5)) /
      (2^(n+1)*Real.sqrt 5) := by
  let s := Real.sqrt 5
  have hs : s^2=5 := Real.sq_sqrt (by norm_num)
  have hs₀ : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  let h : ℝ := (1-s)/2
  let g : ℝ := (1+s)/2
  have hh : h^2=h+1 := by dsimp [h]; nlinarith [hs]
  have hg : g^2=g+1 := by dsimp [g]; nlinarith [hs]
  let v (m : ℕ) := (h^m*(-19+13*s)+g^m*(19+13*s))/(2*s)
  have step (m : ℕ) : v (m+2)=v (m+1)+v m := by
    dsimp only [v]
    rw [pow_add h m 2,pow_add g m 2,hh,hg,pow_succ h m,pow_succ g m]
    ring
  have pair (m : ℕ) : (term m : ℝ)+4=v m ∧ (term (m+1):ℝ)+4=v (m+1) := by
    induction m with
    | zero =>
      have t₀ : term 0=9 := by decide +kernel
      have t₁ : term 1=12 := by decide +kernel
      rw [t₀,t₁]
      dsimp [v,h,g]
      constructor <;> field_simp <;> nlinarith [hs]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have ha : (term (m+2) : ℝ) = term (m+1)+term m+4 := by exact_mod_cast affine m
      change (term (m+2):ℝ)+4=v (m+2)
      rw [step,← ih.1,← ih.2,ha]
      ring
  have iden : v n = ((1-s)^n*(-19+13*s)+(1+s)^n*(19+13*s))/(2^(n+1)*s) := by
    dsimp only [v,h,g]
    rw [div_pow,div_pow,pow_succ (2:ℝ) n]
    field_simp
  change (term n : ℝ) = -4 + ((1-s)^n*(-19+13*s)+(1+s)^n*(19+13*s))/(2^(n+1)*s)
  rw [← iden,← (pair n).1]
  ring

open PowerSeries in
private theorem generating :
    ((1-X)*(1-X-X^2))*series = X*(12+X-9*X^2) := by
  have coefficient (d : ℕ) : coeff d series = (if d=0 then 0 else (term d : ℚ)) := by
    simp [series]
  have shift (d j : ℕ) : coeff d ((X : PowerSeries ℚ)^j*series) =
      if j≤d then (if d-j=0 then 0 else (term (d-j) : ℚ)) else 0 := by
    rw [coeff_X_pow_mul']
    simp only [coefficient]
  have monomial (d j c : ℕ) : coeff d ((c : PowerSeries ℚ)*X^j) = if d=j then (c:ℚ) else 0 := by
    simpa using coeff_C_mul_X_pow (c:ℚ) j d
  have hl : ((1-X)*(1-X-X^2))*series = series-(X^1*series+X^1*series)+X^3*series := by ring
  have hr : (X*(12+X-9*X^2) : PowerSeries ℚ) = ((12:ℕ):PowerSeries ℚ)*X^1+X^2-((9:ℕ):PowerSeries ℚ)*X^3 := by ring
  rw [hl,hr]
  ext n
  simp only [map_add,map_sub,coefficient,shift,monomial,coeff_X_pow]
  by_cases hn : n<4
  · interval_cases n <;> decide +kernel
  · obtain ⟨k,hk⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
    subst n
    have hc : (term (k+4) : ℚ)+term (k+1)=2*term (k+3) := by exact_mod_cast recur k
    simp (disch := omega) only [if_pos,if_neg]
    simp only [show k+4-1=k+3 by omega,show k+4-3=k+1 by omega]
    linarith

end OMA.S_oeis_a224669

open OMA.S_oeis_a224669 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224669.main := ⟨fun n _ => closed n,recur,generating⟩
