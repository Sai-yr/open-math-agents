import OMAStatements.S_oeis_a051195

namespace OMA.S_oeis_a051195

open scoped Classical

private def doubleBlock (l : ℕ) (b : Finset ℕ) : Finset ℕ :=
  b ∪ b.image (fun i => l+i)

private theorem twice_copies (l : ℕ) (b : Finset ℕ) : copies 2 l b = doubleBlock l b := by
  have indices : Finset.range 2 = {0,1} := by decide
  simp [copies, doubleBlock, indices, Finset.biUnion_insert]

-- The number of repetitions divides the length and the weight, hence it divides two.
private theorem period (n : ℕ) (w : Finset ℕ) : repeated n w ↔
    ∃ b ⊆ Finset.range (n+1), n = 2*b.card ∧ w = doubleBlock (n+1) b := by
  constructor
  · rintro ⟨r,l,b,hr,hl,hb,hL,hN,hw⟩
    have h₁ : r ∣ 2*n+2 := ⟨l,hL⟩
    have h₂ : r ∣ 2*n := dvd_mul_of_dvd_right (show r ∣ n from ⟨b.card,hN⟩) 2
    have h₃ : r ∣ 2 := by simpa using Nat.dvd_sub h₁ h₂
    have hr' := Nat.le_of_dvd (by decide : 0 < 2) h₃
    have : r = 2 := by omega
    subst r
    have : l = n+1 := by omega
    subst l
    exact ⟨b,hb,hN,hw.trans (twice_copies _ _)⟩
  · rintro ⟨b,hb,hN,hw⟩
    exact ⟨2,n+1,b,by omega,by omega,hb,by omega,hN,hw.trans (twice_copies _ _).symm⟩

private theorem mem_lower (l i : ℕ) (b : Finset ℕ) (hi : i < l) :
    i ∈ doubleBlock l b ↔ i ∈ b := by
  simp only [doubleBlock, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨j, _, hj⟩)
    · exact h
    · omega
  · exact Or.inl

private theorem double_card {l : ℕ} {b : Finset ℕ} (hb : b ⊆ Finset.range l) :
    (doubleBlock l b).card = 2*b.card := by
  have hd : Disjoint b (b.image (fun i => l+i)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    have := Finset.mem_range.mp (hb hi)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi'
    omega
  rw [doubleBlock, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h), two_mul]

private theorem double_subset {l : ℕ} {b : Finset ℕ} (hb : b ⊆ Finset.range l) :
    doubleBlock l b ⊆ Finset.range (2*l) := by
  intro i hi
  apply Finset.mem_range.mpr
  rcases Finset.mem_union.mp hi with hi | hi
  · have := Finset.mem_range.mp (hb hi)
    omega
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp (hb hj)
    omega

private theorem count_periodic (k : ℕ) :
    ((words (2*k)).filter (repeated (2*k))).card = (2*k+1).choose k := by
  classical
  let B := (Finset.range (2*k+1)).powersetCard k
  have eqset : (words (2*k)).filter (repeated (2*k)) = B.image (doubleBlock (2*k+1)) := by
    ext w
    constructor
    · intro hw
      obtain ⟨b,hb,hN,hW⟩ := (period _ _).mp (Finset.mem_filter.mp hw).2
      exact Finset.mem_image.mpr ⟨b,Finset.mem_powersetCard.mpr ⟨hb,by omega⟩,hW.symm⟩
    · intro hw
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hb
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        exact ⟨by simpa [Nat.mul_add] using double_subset hsub, by rw [double_card hsub,hcard]⟩
      · exact (period _ _).mpr ⟨b,hsub,by rw [hcard],rfl⟩
  rw [eqset, Finset.card_image_of_injOn]
  · simp [B, Finset.card_powersetCard]
  · intro a ha b hb h
    have ha' := (Finset.mem_powersetCard.mp (show a ∈ B from ha)).1
    have hb' := (Finset.mem_powersetCard.mp (show b ∈ B from hb)).1
    ext i
    by_cases hi : i < 2*k+1
    · rw [← mem_lower _ _ _ hi, h, mem_lower _ _ _ hi]
    · have h₀ : i ∉ a := fun hi' => hi (Finset.mem_range.mp (ha' hi'))
      have h₁ : i ∉ b := fun hi' => hi (Finset.mem_range.mp (hb' hi'))
      simp [h₀,h₁]

private theorem count_odd (k : ℕ) :
    ((words (2*k+1)).filter (repeated (2*k+1))).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨b, _, hn, _⟩ := (period _ _).mp (Finset.mem_filter.mp hw).2
  omega

private def R (p q : ℕ) : ℚ := ((p+q).choose p : ℚ)
private def C (n : ℕ) : ℚ := R n (n+2)
private def H (n : ℕ) : ℚ := if n%2=0 then R (n/2) (n/2+1) else 0

private theorem counted (n : ℕ) : (term n : ℚ) = C n - H n := by
  classical
  have ht := Finset.card_filter_add_card_filter_not (s := words n) (repeated n)
  change _ + term n = _ at ht
  have hw : (words n).card = (2*n+2).choose n := by simp [words, Finset.card_powersetCard]
  rw [hw] at ht
  obtain ⟨k, hk | hk⟩ := n.even_or_odd'
  · subst n
    rw [count_periodic] at ht
    have hq : (((2*k+1).choose k : ℕ) : ℚ) + term (2*k) = ((2*(2*k)+2).choose (2*k) : ℕ) := by exact_mod_cast ht
    have h₁ : (2*k)%2 = 0 := by omega
    have h₂ : (2*k)/2 = k := by omega
    simp only [C,H,R,h₁,h₂,if_true]
    rw [show 2*k+(2*k+2) = 2*(2*k)+2 by omega, show k+(k+1) = 2*k+1 by omega]
    linarith
  · subst n
    rw [count_odd, zero_add] at ht
    have hq : (term (2*k+1) : ℚ) = ((2*(2*k+1)+2).choose (2*k+1) : ℕ) := by exact_mod_cast ht
    have hmod : (2*k+1)%2 ≠ 0 := by omega
    simp only [C,H,R,hmod,if_false,sub_zero]
    rwa [show 2*k+1+(2*k+1+2) = 2*(2*k+1)+2 by omega]

private theorem symmetric (p q : ℕ) : R p q = R q p := by
  unfold R
  rw [Nat.choose_symm_add, Nat.add_comm p q]

private theorem R_left (p q : ℕ) : R (p+1) q = ((p:ℚ)+q+1)/(p+1)*R p q := by
  have hp := Nat.add_one_mul_choose_eq (p+q) p
  have idx : p+1+q = p+q+1 := by omega
  unfold R
  rw [idx]
  have h : ((p:ℚ)+q+1)*((p+q).choose p : ℚ) =
      (((p+q+1).choose (p+1)) : ℚ)*(p+1) := by exact_mod_cast hp
  field_simp
  linarith

private theorem R_right (p q : ℕ) : R p (q+1) = ((p:ℚ)+q+1)/(q+1)*R p q := by
  rw [symmetric p (q+1), R_left q p, symmetric q p]
  ring

private theorem diagonal (p q : ℕ) :
    R (p+1) (q+1) = (((p:ℚ)+q+2)*((p:ℚ)+q+1))/((p+1)*(q+1))*R p q := by
  rw [R_left p (q+1), R_right p q]
  push_cast
  field_simp
  ring

private theorem C_step (n : ℕ) :
    C (n+1) = ((2*(n:ℚ)+4)*(2*n+3))/((n+1)*(n+3))*C n := by
  change R (n+1) ((n+2)+1) = _ * R n (n+2)
  rw [diagonal]
  push_cast
  ring

private theorem H_step (n : ℕ) : H (n+2) = 4*((n:ℚ)+3)/(n+4)*H n := by
  obtain ⟨k,hk | hk⟩ := n.even_or_odd'
  · subst n
    have h₀ : (2*k)%2 = 0 := by omega
    have h₁ : (2*k+2)%2 = 0 := by omega
    have h₂ : (2*k)/2 = k := by omega
    have h₃ : (2*k+2)/2 = k+1 := by omega
    simp only [H,h₀,h₁,h₂,h₃,if_true]
    rw [diagonal k (k+1)]
    push_cast
    field_simp
    ring
  · subst n
    simp [H]

private theorem C_rec (k : ℕ) :
    recurrence k (C k) (C (k+1)) (C (k+2)) (C (k+3)) (C (k+4)) = 0 := by
  rw [C_step (k+3), C_step (k+2), C_step (k+1), C_step k]
  unfold recurrence
  push_cast
  field_simp
  ring

private theorem H_rec (k : ℕ) :
    recurrence k (H k) (H (k+1)) (H (k+2)) (H (k+3)) (H (k+4)) = 0 := by
  rw [H_step (k+2), H_step (k+1), H_step k]
  unfold recurrence
  push_cast
  field_simp
  ring

end OMA.S_oeis_a051195

open OMA.S_oeis_a051195

theorem OMA.solution : type_of% @OMA.S_oeis_a051195.main := by
  intro k
  simp only [counted]
  unfold recurrence
  have hc := C_rec k
  have hh := H_rec k
  unfold recurrence at hc hh
  linear_combination hc - hh
