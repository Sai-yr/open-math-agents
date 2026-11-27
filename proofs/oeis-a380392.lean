import OMAStatements.S_oeis_a380392
/-!
# The mean number of South-East paths

Sum over paths before summing over binary matrices. A path picks one cell
on each successive antidiagonal, leaving m² independent entries in an
(m+1)-square. Reducing the resulting rational uses the binary valuation
of the central binomial coefficient.
-/
namespace A380392Proof
open OMA.S_oeis_a380392 Finset

private theorem cell_rank (s : Finset ℕ) (t : ℕ) : (cell s t).1+(cell s t).2=t := by
  simp [cell]

private theorem path_card (m : ℕ) (s : Finset ℕ) : (cells m s).card = 2*m+1 := by
  unfold cells
  rw [card_image_of_injective,card_range]
  intro u v he
  have h := congrArg (fun p : ℕ×ℕ=>p.1+p.2) he
  simpa only [cell_rank] using h

private theorem path_in_grid (m : ℕ) {s : Finset ℕ} (hs : s∈paths m) : cells m s ⊆ grid m := by
  obtain ⟨hs,hc⟩ := mem_powersetCard.mp hs
  intro p hp
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
  have h' : t≤2*m := by have := mem_range.mp ht; omega
  have hy : (range t ∩ s).card ≤ m := hc ▸ card_le_card (inter_subset_right)
  have sub : range t \ s ⊆ range (2*m) \ s := sdiff_subset_sdiff (range_mono h') (by rfl)
  have hx := card_le_card sub
  rw [card_sdiff_of_subset hs,card_range,hc] at hx
  simp only [grid,cell,mem_product,mem_range]
  exact ⟨by omega,by omega⟩

private theorem completions (m : ℕ) {s : Finset ℕ} (hs : s∈paths m) :
    (((grid m).powerset).filter (fun M=>cells m s ⊆ M)).card = 2^(m*m) := by
  have eq : ((grid m).powerset).filter (fun M=>cells m s ⊆ M) = Icc (cells m s) (grid m) := by
    ext M
    simp only [mem_filter,mem_powerset,mem_Icc]
    tauto
  rw [eq,card_Icc_finset (path_in_grid m hs),path_card]
  simp only [grid,card_product,card_range]
  congr 1
  have : (m+1)*(m+1) = m*m+(2*m+1) := by ring
  omega

private theorem total_paths (m : ℕ) :
    ∑ M ∈ (grid m).powerset, pathCount m M = m.centralBinom * 2^(m*m) := by
  calc
    _ = ∑ M ∈ (grid m).powerset, ∑ s ∈ paths m, (if cells m s⊆M then 1 else 0) := by
      simp [pathCount]
    _ = ∑ s ∈ paths m, ∑ M ∈ (grid m).powerset, (if cells m s⊆M then 1 else 0) := sum_comm
    _ = ∑ _s ∈ paths m, 2^(m*m) := by
      apply sum_congr rfl; intro s hs
      simpa only [sum_boole,Nat.cast_id] using (completions m hs)
    _ = _ := by simp [paths,Nat.centralBinom]


private theorem sum_twice (m : ℕ) : (Nat.digits 2 (2*m)).sum = (Nat.digits 2 m).sum := by
  cases m with
  | zero => rfl
  | succ m => rw [Nat.digits_base_mul (by decide) (by omega)]; simp

private theorem binom_valuation (m : ℕ) : padicValNat 2 m.centralBinom = (Nat.digits 2 m).sum := by
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p:=2) (k:=m) (n:=m)
  rw [←two_mul,sum_twice] at h
  simpa [Nat.centralBinom] using h

private theorem normalized (m : ℕ) :
    (m.centralBinom : ℚ)/(2:ℚ)^(2*m+1) = (A001790 m : ℚ)/A101926 m := by
  let w := (Nat.digits 2 m).sum
  have hw : w ≤ m := Nat.digit_sum_le _ _
  have hd : 2^w ∣ m.centralBinom := by
    change 2^(Nat.digits 2 m).sum ∣ _
    rw [←binom_valuation]
    exact pow_padicValNat_dvd
  have hn : A001790 m * 2^w = m.centralBinom := by
    simpa only [A001790,binom_valuation] using (Nat.div_mul_cancel hd)
  have hr : ((A001790 m : ℕ) : ℚ) * 2^w = (m.centralBinom : ℚ) := by exact_mod_cast hn
  have exp : 2*m+1 = w+(2*m-w+1) := by omega
  change (m.centralBinom : ℚ)/(2:ℚ)^(2*m+1) =
    (A001790 m : ℚ)/(↑(2^(2*m-w+1) : ℕ))
  rw [←hr,exp,pow_add]
  push_cast
  field_simp


private theorem average (m : ℕ) :
    (∑ M ∈ (grid m).powerset, (pathCount m M : ℚ)) / ((grid m).powerset.card : ℚ) =
      (A001790 m : ℚ) / A101926 m := by
  rw [←normalized,←Nat.cast_sum,total_paths,card_powerset]
  simp only [grid,card_product,card_range,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_mul]
  have h : (m+1)*(m+1)=m*m+(2*m+1) := by ring
  rw [h,pow_add]
  field_simp


end A380392Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380392.main :=
  A380392Proof.average
