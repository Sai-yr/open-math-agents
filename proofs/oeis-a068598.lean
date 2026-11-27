import OMAStatements.S_oeis_a068598

namespace OMA.S_oeis_a068598

-- Label each used part by the least part of its unique block.
-- Unused parts get the additional symbol none.
private noncomputable def label {n : ℕ} (s : Family n) (i : Fin n) : Option (Fin n) := by
  classical
  exact if h : ∃ b ∈ s, i ∈ b then some (h.choose.min' ⟨i,h.choose_spec.2⟩) else none

private theorem label_used {n : ℕ} {s : Family n} (hs : admissible s)
    {b : Block n} (hb : b∈s) {i : Fin n} (hi : i∈b) :
    label s i=some (b.min' ⟨i,hi⟩) := by
  classical
  have h : ∃ b ∈ s, i∈b := ⟨b,hb,hi⟩
  have he := hs.2 _ h.choose_spec.1 b hb i h.choose_spec.2 hi
  simp [label,h,he]

private theorem from_label {n : ℕ} {s : Family n} {i v : Fin n}
    (h : label s i=some v) : ∃ b ∈ s, i∈b ∧ v∈b := by
  classical
  unfold label at h
  split_ifs at h with he
  · obtain rfl := Option.some.inj h
    exact ⟨he.choose,he.choose_spec.1,he.choose_spec.2,Finset.min'_mem _ _⟩

private theorem fiber {n : ℕ} {s : Family n} (hs : admissible s) {b : Block n}
    (hb : b∈s) {i : Fin n} (hi : i∈b) (j : Fin n) : j∈b ↔ label s j=label s i := by
  rw [label_used hs hb hi]
  constructor
  · exact fun hj => label_used hs hb hj
  · intro h
    obtain ⟨d,hd,hj,hm⟩ := from_label h
    have he := hs.2 d hd b hb _ hm (Finset.min'_mem b ⟨i,hi⟩)
    exact he ▸ hj

private theorem recover {n : ℕ} {s t : Family n} (hs : admissible s) (ht : admissible t)
    (h : label s=label t) : s ⊆ t := by
  intro b hb
  obtain ⟨i,hi⟩ := (hs.1 b hb).1
  have htag := label_used hs hb hi
  rw [h] at htag
  obtain ⟨d,hd,hid,_⟩ := from_label htag
  have he : b=d := by
    ext j
    rw [fiber hs hb hi j,fiber ht hd hid j,h]
  exact he ▸ hd

private theorem upper (n : ℕ) : term n ≤ (n+1)^n := by
  classical
  by_cases hn : n=0
  · simp [hn,term]
  let s := Finset.univ.filter (fun s : Family n => admissible s ∧
    ∀ t : Family n, s ⊆ t → admissible t → t=s)
  have inj : Function.Injective (fun a : s => label a.val) := by
    intro a b he
    have ha := (Finset.mem_filter.mp a.property).2.1
    have hb := (Finset.mem_filter.mp b.property).2.1
    exact Subtype.ext (Finset.Subset.antisymm (recover ha hb he) (recover hb ha he.symm))
  have hcard := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_coe] at hcard
  change (if n=0 then 1 else s.card) ≤ (n+1)^n
  simpa [hn,Fintype.card_option] using hcard

open Filter Topology

-- The logarithm of the counting bound is at most 2n log n for n≥2.
-- Every B n^C with B>0, C>1 eventually dominates it.
private theorem growth (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 1 < c) :
    Tendsto (fun n : ℕ => (term n : ℝ)/(a*Real.exp (b*(n:ℝ)^c))) atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (r := c-1) (by linarith)).bound (show 0 < b/4 by positivity)
  have hncast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop, (term n : ℝ)/(a*Real.exp (b*(n:ℝ)^c)) ≤
      Real.exp (-(b/2*(n:ℝ)^c))/a := by
    filter_upwards [hncast.eventually hlog,eventually_ge_atTop 2] with n hlog hn
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    have H : (n:ℝ)^c = (n:ℝ)^(c-1)*n := by
      conv_lhs => rw [show c=(c-1)+1 by ring]
      rw [Real.rpow_add (by positivity),Real.rpow_one]
    have hn₀ : (0:ℝ)<n := by linarith
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ n)),
      abs_of_nonneg (Real.rpow_nonneg hn₀.le _)] at hlog
    have key : 2*(n:ℝ)*Real.log n ≤ b/2*(n:ℝ)^c := by
      rw [H]
      nlinarith [mul_le_mul_of_nonneg_right hlog hn₀.le]
    have nn : n+1 ≤ n^2 := by nlinarith
    have hu : (term n:ℝ) ≤ ((n:ℝ)^2)^n := by exact_mod_cast (upper n).trans (Nat.pow_le_pow_left nn n)
    have hpow : ((n:ℝ)^2)^n = Real.exp (2*(n:ℝ)*Real.log n) := by
      rw [show (2:ℝ)*n*Real.log n=(n:ℝ)*(2*Real.log n) by ring]
      rw [Real.exp_nat_mul,show (2:ℝ)*Real.log n = ((2:ℕ):ℝ)*Real.log n by norm_num,Real.exp_nat_mul,Real.exp_log hn₀]
    rw [hpow] at hu
    have hsmall := hu.trans (Real.exp_le_exp.mpr key)
    apply (div_le_div_iff₀ (mul_pos ha (Real.exp_pos _)) ha).mpr
    calc
      (term n:ℝ)*a ≤ Real.exp (b/2*(n:ℝ)^c)*a := mul_le_mul_of_nonneg_right hsmall ha.le
      _ = Real.exp (-(b/2*(n:ℝ)^c))*(a*Real.exp (b*(n:ℝ)^c)) := by
        rw [mul_left_comm,← Real.exp_add]
        ring_nf
  have hlim : Tendsto (fun n : ℕ => b/2*(n:ℝ)^c) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) ((tendsto_rpow_atTop (by linarith)).comp hncast)
  have hexp := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim).div_const a
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ => 0) tendsto_const_nhds
      (by simpa using hexp) _ hbound
  exact Filter.Eventually.of_forall (fun _ => by positivity)

end OMA.S_oeis_a068598

open OMA.S_oeis_a068598 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068598.main) := by
  rintro ⟨a,b,c,ha,hb,hc,h⟩
  have H := tendsto_nhds_unique (growth a b c ha hb hc) h
  norm_num at H
