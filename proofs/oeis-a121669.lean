import OMAStatements.S_oeis_a121669

namespace OMA.S_oeis_a121669

open scoped Classical
open Filter Topology

private abbrev Match (n : ℕ) := {w : Word n // qualifies w}

private theorem matches_card (n : ℕ) : Fintype.card (Match n) = count n :=
  Fintype.card_subtype qualifies

-- Choose the two consecutive positions occupied by the distinguished 19.
private noncomputable def mark {n : ℕ} (w : Match n) := w.property.2.2.choose
private noncomputable def nextPos {n : ℕ} (w : Match n) := w.property.2.2.choose_spec.choose

private theorem marked {n : ℕ} (w : Match n) :
    (nextPos w : ℕ) = (mark w : ℕ)+1 ∧ w.val (mark w) = 9 ∧ w.val (nextPos w) = 1 :=
  w.property.2.2.choose_spec.choose_spec

private noncomputable def residual {n : ℕ} (w : Match n) (i : Fin n) : ℕ :=
  if i=mark w ∨ i=nextPos w then 0 else w.val i

private theorem recover {n : ℕ} (w : Match n) (i : Fin n) : (w.val i : ℕ) =
    residual w i + (if i=mark w then 9 else 0) + (if i=nextPos w then 1 else 0) := by
  obtain ⟨h,ha,hb⟩ := marked w
  have hne : mark w ≠ nextPos w := by intro hn; rw [hn] at h; omega
  by_cases hi : i=mark w
  · subst i; simp [residual,hne,ha]
  by_cases hj : i=nextPos w
  · subst i; simp [residual,hi,hb]
  simp [residual,hi,hj]

private theorem residual_sum {n : ℕ} (w : Match n) : ∑ i, residual w i = 9 := by
  have h := w.property.1
  simp_rw [recover w] at h
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  omega

private def bag {n : ℕ} (f : Fin n → ℕ) : Multiset (Fin n) :=
  ∑ i, Multiset.replicate (f i) i

private theorem bag_count {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : (bag f).count i = f i := by
  change (Multiset.countAddMonoidHom i) (∑ j, Multiset.replicate (f j) j) = _
  rw [map_sum]
  simp [Multiset.coe_countAddMonoidHom, Multiset.count_replicate]

-- A starting position for the block and an unordered list of nine unit
-- positions determine all digits, including the digits equal to zero.
private noncomputable def encode {n : ℕ} (w : Match n) : Fin n × Sym (Fin n) 9 :=
  (mark w, ⟨bag (residual w), by simpa [bag, Multiset.card_sum] using residual_sum w⟩)

private theorem encode_inj {n : ℕ} : Function.Injective (@encode n) := by
  intro u v h
  have hm : mark u = mark v := congrArg Prod.fst h
  have hn : nextPos u = nextPos v := by
    apply Fin.ext
    rw [(marked u).1,hm,(marked v).1]
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [recover u i, recover v i,hm,hn]
  have hc := congrArg (fun p : Fin n × Sym (Fin n) 9 => p.2.val.count i) h
  change (bag (residual u)).count i = (bag (residual v)).count i at hc
  rw [bag_count,bag_count] at hc
  rw [hc]

private theorem polynomial_bound (n : ℕ) : count n ≤ n^10 := by
  have h := Fintype.card_le_of_injective (@encode n) encode_inj
  rw [matches_card, Fintype.card_prod, Sym.card_sym_eq_choose, Fintype.card_fin] at h
  have hh := Nat.choose_le_sub_pow (n+9-1) 9
  rw [show n+9-1+1-9 = n by omega] at hh
  exact h.trans ((Nat.mul_le_mul_left n hh).trans_eq (pow_succ' n 9).symm)

-- Eleven nonzero digits in distinct residue classes modulo eighteen.
-- The first two form the block 19 and move together. The remaining
-- nine positions move independently while preserving divisibility by 19.
private def offset : Fin 11 → ℕ := ![0,1,2,3,4,5,6,7,8,9,15]
private def group : Fin 11 → Fin 10 := ![0,0,1,2,3,4,5,6,7,8,9]
private def weight (j : Fin 11) : Fin 10 := if j=0 then 9 else 1

private abbrev Locations (n : ℕ) := Fin 10 → Fin (n/18)

private def position {n : ℕ} (t : Locations n) (j : Fin 11) : Fin n :=
  ⟨18*(t (group j) : ℕ) + offset j, by
    have h₁ := (t (group j)).isLt
    have h₂ : ∀ k, offset k < 18 := by decide +kernel
    have := h₂ j
    omega⟩

private theorem position_mod {n : ℕ} (t : Locations n) (j : Fin 11) :
    (position t j : ℕ)%18 = offset j := by
  have h : ∀ k, offset k < 18 := by decide +kernel
  simp [position,Nat.add_mod,Nat.mod_eq_of_lt (h j)]

private theorem offset_inj : Function.Injective offset := by decide +kernel

private theorem position_inj {n : ℕ} (t : Locations n) : Function.Injective (position t) := by
  intro i j h
  apply offset_inj
  rw [← position_mod t i, ← position_mod t j, h]

private noncomputable def layout {n : ℕ} (t : Locations n) : Word n :=
  Function.extend (position t) weight (fun _ => 0)

private theorem at_position {n : ℕ} (t : Locations n) (j : Fin 11) :
    layout t (position t j) = weight j := (position_inj t).extend_apply _ _ _

private theorem off_position {n : ℕ} (t : Locations n) (i : Fin n)
    (h : ¬∃ j, position t j = i) : layout t i = 0 := Function.extend_apply' _ _ _ h

private theorem weighted {n : ℕ} (t : Locations n) (f : Fin n → ℕ) :
    (∑ i, (layout t i : ℕ)*f i) = ∑ j, (weight j : ℕ)*f (position t j) := by
  let s := Finset.univ.image (position t)
  calc
    _ = ∑ i ∈ s, (layout t i : ℕ)*f i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have h : ¬ ∃ j, position t j = i := by simpa [s] using hi
      rw [off_position _ _ h]
      simp
    _ = _ := by
      rw [Finset.sum_image (fun _ _ _ _ h => position_inj t h)]
      simp_rw [at_position]

private theorem valid_layout {n : ℕ} (t : Locations n) : qualifies (layout t) := by
  have hp (j : Fin 11) : 10^(position t j : ℕ) ≡ 10^(offset j) [MOD 19] := by
    have h : 10^18 ≡ 1 [MOD 19] := by decide +kernel
    have h' := (h.pow (t (group j) : ℕ)).mul_right (10^offset j)
    simpa [position, pow_add, pow_mul] using h'
  have hmod := Nat.ModEq.sum (s := Finset.univ) (fun j _ => (hp j).mul_left (weight j : ℕ))
  constructor
  · have h := weighted t (fun _ => 1)
    simpa only [mul_one, show (∑ j, (weight j : ℕ)) = 19 by decide +kernel] using h
  constructor
  · rw [weighted t (fun i => 10^(i:ℕ))]
    have hz : (∑ j, (weight j : ℕ)*10^offset j) ≡ 0 [MOD 19] := by decide +kernel
    exact Nat.modEq_zero_iff_dvd.mp (hmod.trans hz)
  · refine ⟨position t 0, position t 1, ?_, ?_, ?_⟩
    · change 18*(t 0 : ℕ)+1 = (18*(t 0 : ℕ)+0)+1
      omega
    · exact at_position t 0
    · exact at_position t 1

private theorem layout_inj {n : ℕ} : Function.Injective (@layout n) := by
  intro t u h
  funext k
  obtain ⟨j,hj⟩ := (show Function.Surjective group by decide +kernel) k
  have hval : layout u (position t j) ≠ 0 := by
    rw [← h, at_position]
    exact (show ∀ x, weight x ≠ 0 by decide +kernel) j
  obtain ⟨r,hr⟩ : ∃ r, position u r = position t j :=
    by_contra fun hf => hval (off_position _ _ hf)
  have hrj : r = j := offset_inj (by rw [← position_mod u r, ← position_mod t j, hr])
  subst r
  have hpos := congrArg Fin.val hr
  change 18*(u (group j) : ℕ)+offset j = 18*(t (group j) : ℕ)+offset j at hpos
  rw [hj] at hpos
  apply Fin.ext
  omega

private theorem growth_bounds (n : ℕ) : (n/18)^10 ≤ count n ∧ count n ≤ n^10 := by
  refine ⟨?_, polynomial_bound n⟩
  let f (t : Locations n) : Match n := ⟨layout t, valid_layout t⟩
  have hf : Function.Injective f := fun _ _ h => layout_inj (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Locations,Fintype.card_fun,Fintype.card_fin,matches_card] using hc

private theorem zero_ratio : Tendsto (fun n : ℕ => (count n : ℝ)/proposed n) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => (2:ℝ)^11 / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hz
  · filter_upwards [] with n
    unfold proposed
    positivity
  · filter_upwards [eventually_ge_atTop 16] with n hn
    have hp : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
    have h₁ : (1:ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast (by omega : 1≤n-1)
    have h₂ : (1:ℝ) ≤ (n-2 : ℕ) := by exact_mod_cast (by omega : 1≤n-2)
    have hhalf : (n:ℝ)/2 ≤ (n-2 : ℕ) := by
      rw [Nat.cast_sub (by omega : 2≤n)]
      push_cast
      have h₄ : (4:ℝ) ≤ n := by exact_mod_cast (by omega : 4≤n)
      linarith
    have hpow : ((n:ℝ)/2)^11 ≤ proposed n := by
      calc
        ((n:ℝ)/2)^11 ≤ ((n-2 : ℕ) : ℝ)^11 := pow_le_pow_left₀ (by positivity) hhalf _
        _ ≤ ((n-2 : ℕ) : ℝ)^(n-2) := pow_le_pow_right₀ h₂ (by omega)
        _ ≤ proposed n := le_mul_of_one_le_left (by positivity) h₁
    have hpp : 0 < proposed n := (by positivity : 0 < ((n:ℝ)/2)^11).trans_le hpow
    have hc : (count n : ℝ) ≤ (n:ℝ)^10 := by exact_mod_cast (growth_bounds n).2
    apply (div_le_div_iff₀ hpp hp).mpr
    calc
      (count n : ℝ)*n ≤ (n:ℝ)^10*n := mul_le_mul_of_nonneg_right hc hp.le
      _ = 2^11*((n:ℝ)/2)^11 := by ring
      _ ≤ 2^11*proposed n := mul_le_mul_of_nonneg_left hpow (by positivity)

end OMA.S_oeis_a121669

open OMA.S_oeis_a121669 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a121669.main) := by
  rintro ⟨c,hc,ht⟩
  exact hc.ne' (tendsto_nhds_unique ht zero_ratio)
