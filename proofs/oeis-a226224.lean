import OMAStatements.S_oeis_a226224

namespace OMA.S_oeis_a226224

-- In base b+3, (b+2)^2 has the two digits b+1 and 1.
private theorem witness (b : ℕ) : (b+2)^2 ∈ solutions (b+3) := by
  refine ⟨by positivity, b+2, rfl, ?_⟩
  have hsq : (b+2)^2 = 1 + (b+3)*(b+1) := by ring
  rw [hsq, Nat.digits_add _ (by omega) _ _ (by omega) (Or.inl one_ne_zero)]
  rw [Nat.digits_of_lt _ _ (by omega) (by omega)]
  simp
  omega

private theorem exponent_bound (i : ℕ) : (i+7)^2 < 2^(i+6) := by
  induction i with
  | zero => decide
  | succ i ih =>
    calc
      (i+8)^2 ≤ 2*(i+7)^2 := by
        rw [show 2*(i+7)^2 = (i+8)^2 + (i^2+12*i+34) by ring]
        exact Nat.le_add_right _ _
      _ < 2*2^(i+6) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = 2^(i+7) := (pow_succ' _ _).symm

private theorem binary {k : ℕ} (hk : k ∈ solutions 2) : k = 1 := by
  obtain ⟨hpos,r,rfl,hs⟩ := hk
  have ht : (Nat.digits 2 (r^2)).sum ≤ (Nat.digits 2 (r^2)).length := by
    have := List.sum_le_card_nsmul (Nat.digits 2 (r^2)) 1 (fun x hx =>
      show x ≤ 1 from Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1<2) hx))
    simpa using this
  rw [hs] at ht
  by_cases hr : 7 ≤ r
  · obtain ⟨i,hi⟩ : ∃ i, r=i+7 := ⟨r-7,by omega⟩
    subst r
    have hlen : (Nat.digits 2 ((i+7)^2)).length ≤ i+6 :=
      (Nat.digits_length_le_iff (by decide) _).mpr (exponent_bound i)
    omega
  · have hsmall : ∀ s : Fin 7, 0 < s.val^2 →
        (Nat.digits 2 (s.val^2)).sum = s.val → s.val^2=1 := by decide +kernel
    exact hsmall ⟨r,by omega⟩ hpos hs

end OMA.S_oeis_a226224

open OMA.S_oeis_a226224 in
theorem OMA.solution : type_of% @OMA.S_oeis_a226224.main := by
  intro b hb
  constructor
  · intro h
    by_contra hne
    obtain ⟨x,hx⟩ : ∃ x, b=x+3 := ⟨b-3,by omega⟩
    subst b
    have hle := h.2 (witness x)
    change (x+2)^2 ≤ 1 at hle
    nlinarith
  · rintro rfl
    refine ⟨⟨by decide, 1, by decide, by decide⟩, ?_⟩
    intro k hk
    exact (binary hk).le
