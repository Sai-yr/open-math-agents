import OMAStatements.S_oeis_a082477
/-!
# Mean of the number of adjacent divisors

For fixed d the admissible n form the progression d + d(d+1)t. The first
member contributes one for each d up to N. The remaining row has weight
1/(d(d+1)), and these weights telescope. Uniform rounding bounds on each
fixed finite set of rows suffice to recover the entire limiting mean.
-/
namespace A082477Proof
open OMA.S_oeis_a082477 Finset Filter Topology

private def qualifies (d n : ℕ) := d ∣ n ∧ d+1 ∣ n+1
private instance (d n : ℕ) : Decidable (qualifies d n) := by unfold qualifies; infer_instance

private theorem progression {d n : ℕ} (hn : 0<n) :
    qualifies d n ↔ ∃ t, n=d+(d*(d+1))*t := by
  constructor
  · rintro ⟨h₁,h₂⟩
    have hd := Nat.le_of_dvd hn h₁
    have a : d ∣ n-d := Nat.dvd_sub h₁ (dvd_refl d)
    have b : d+1 ∣ n-d := by simpa using Nat.dvd_sub h₂ (dvd_refl (d+1))
    have hc : d.Coprime (d+1) := Nat.coprime_self_add_right.mpr (by simp)
    obtain ⟨t,ht⟩ := hc.mul_dvd_of_dvd_of_dvd a b
    exact ⟨t,by omega⟩
  · rintro ⟨t,rfl⟩
    refine ⟨?_,?_⟩
    · exact ⟨1+(d+1)*t,by ring⟩
    · exact ⟨1+d*t,by ring⟩

private def step (d : ℕ) := d*(d+1)
private def off (N d : ℕ) := (N-d)/step d

private theorem fiber (N d : ℕ) (hd : 0<d) (hdN : d≤N) :
    ((range N).filter (fun k=>qualifies d (k+1))).card=off N d+1 := by
  let p := step d
  have hp : 0<p := Nat.mul_pos hd (show 0<d+1 by omega)
  rw [←card_range (off N d+1)]
  symm
  apply card_nbij (fun t=>d+p*t-1)
  · intro t ht
    have hh : t≤(N-d)/p := Nat.lt_succ_iff.mp (mem_range.mp ht)
    have hmul := (Nat.le_div_iff_mul_le hp).mp hh
    rw [mul_comm] at hmul
    have ht' : d+p*t-1+1=d+p*t := by omega
    exact mem_filter.mpr ⟨mem_range.mpr (show d+p*t-1<N by omega), (progression (by omega)).mpr ⟨t,ht'⟩⟩
  · intro a ha b hb he
    apply Nat.mul_left_cancel hp
    change d+p*a-1=d+p*b-1 at he; omega
  · intro k hk
    obtain ⟨hk,hq⟩ := mem_filter.mp hk
    obtain ⟨t,ht⟩ := (progression (Nat.succ_pos k)).mp hq
    change k+1=d+p*t at ht
    have hl := mem_range.mp hk
    have hm : t*p≤N-d := by rw [mul_comm]; omega
    have ht' := (Nat.le_div_iff_mul_le hp).mpr hm
    exact ⟨t,mem_range.mpr (Nat.lt_succ_of_le ht'),show d+p*t-1=k by omega⟩

private theorem term_eq (N k : ℕ) (hk : k<N) : term (k+1) =
    ((range N).filter (fun j=>qualifies (j+1) (k+1))).card := by
  symm
  apply card_nbij (fun j=>j+1)
  · intro j hj
    obtain ⟨_,h⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h.1,by omega⟩,h.2⟩
  · intro a ha b hb he; change a+1=b+1 at he; omega
  · intro d hd
    obtain ⟨hd,hq⟩ := mem_filter.mp hd
    obtain ⟨hd,_⟩ := Nat.mem_divisors.mp hd
    have hpos : 0<d := Nat.pos_of_dvd_of_pos hd (Nat.succ_pos k)
    have hle := Nat.le_of_dvd (Nat.succ_pos k) hd
    cases d with
    | zero => omega
    | succ j => exact ⟨j,mem_filter.mpr ⟨mem_range.mpr (by omega),hd,hq⟩,rfl⟩

private theorem total (N : ℕ) : (∑ k ∈ range N, term (k+1)) =
    N+∑ j ∈ range N, off N (j+1) := by
  calc _ = ∑ k ∈ range N, ∑ j ∈ range N, if qualifies (j+1) (k+1) then 1 else 0 := by
         apply sum_congr rfl; intro k hk; rw [term_eq N k (mem_range.mp hk),card_filter]
       _ = ∑ j ∈ range N,(off N (j+1)+1) := by
         rw [sum_comm]; apply sum_congr rfl; intro j hj
         rw [←card_filter]; exact fiber N (j+1) (by omega) (mem_range.mp hj)
       _ = _ := by simp [sum_add_distrib,add_comm]


private noncomputable def w (j : ℕ) : ℝ := 1/(step (j+1):ℝ)

private theorem telescope (L : ℕ) : (∑ j ∈ range L,w j) = 1-1/((L:ℝ)+1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ,ih,w,step]
    push_cast
    field_simp
    ring

private theorem bounds (N j : ℕ) :
    (off N (j+1):ℝ) ≤ (N:ℝ)*w j ∧ (N:ℝ)*w j ≤ (off N (j+1):ℝ)+2 := by
  let d := j+1
  let p := step d
  have hd : 0<d := by dsimp [d]; omega
  have hp : 0<p := Nat.mul_pos hd (show 0<d+1 by omega)
  have hdp : d≤p := Nat.le_mul_of_pos_right d (show 0<d+1 by omega)
  have h1 : (off N d)*p≤N := (Nat.div_mul_le_self (N-d) p).trans (Nat.sub_le ..)
  have h2 : N≤((off N d)+2)*p := by
    have h := Nat.lt_div_mul_add (a:=N-d) hp
    change N-d<off N d*p+p at h
    rw [Nat.add_mul]; omega
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  change _≤(N:ℝ)*(1/(p:ℝ)) ∧ (N:ℝ)*(1/(p:ℝ))≤_
  rw [←mul_div_assoc,mul_one]
  exact ⟨(le_div_iff₀ hp').mpr (by exact_mod_cast h1),(div_le_iff₀ hp').mpr (by exact_mod_cast h2)⟩

private noncomputable def mass (N : ℕ) : ℝ := (∑ j ∈ range N,(off N (j+1):ℝ))/N

private theorem upper (N : ℕ) : mass N ≤ 1 := by
  by_cases hN : N=0
  · simp [hN,mass]
  have hn0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  apply (div_le_iff₀ hn0).mpr
  calc _ ≤ ∑ j ∈ range N,(N:ℝ)*w j := sum_le_sum fun j _=>(bounds N j).1
       _ = (N:ℝ)*(1-1/((N:ℝ)+1)) := by rw [←mul_sum,telescope]
       _ ≤ _ := by
         have h : 0≤1/((N:ℝ)+1) := by positivity
         nlinarith [mul_nonneg hn0.le h]

private theorem lower {N L : ℕ} (hN : 0<N) (hL : L≤N) :
    1-1/((L:ℝ)+1)-2*L/N ≤ mass N := by
  have hn0 : (0:ℝ)<N := by exact_mod_cast hN
  have h := sum_le_sum (s:=range L) (fun j _=>(bounds N j).2)
  rw [←mul_sum,telescope,sum_add_distrib] at h
  simp only [sum_const,card_range,nsmul_eq_mul] at h
  have hm : (∑ j ∈ range L,(off N (j+1):ℝ)) ≤ ∑ j ∈ range N,(off N (j+1):ℝ) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hL) (fun _ _ _=>by positivity)
  unfold mass
  apply (le_div_iff₀ hn0).mpr
  rw [sub_mul,div_mul_cancel₀ _ hn0.ne']
  linarith

private theorem mean_limit : Tendsto mass atTop (𝓝 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  obtain ⟨m,hm⟩ := Metric.tendsto_atTop.mp ht (ε/2) (by positivity)
  let L := m
  have hL : 1/((L:ℝ)+1)<ε/2 := by
    have h := hm (L+1) (by dsimp [L]; omega)
    simpa [Real.dist_eq,abs_of_nonneg (show 0 ≤ (L:ℝ)+1 by positivity)] using h
  obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp
    (tendsto_const_div_atTop_nhds_zero_nat (2*(L:ℝ))) (ε/2) (by positivity)
  refine ⟨max (max n L) 1,fun N hN=>?_⟩
  have hn' : 2*(L:ℝ)/N<ε/2 := by
    have hh := hn N (by omega)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hh
    exact hh
  have hlo := lower (N:=N) (L:=L) (by omega) (by omega)
  have hhi := upper N
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end A082477Proof

open OMA.S_oeis_a082477 A082477Proof Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a082477.main := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).add mean_limit
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [←Nat.cast_sum,total,Nat.cast_add,add_div,div_self (by exact_mod_cast (show N≠0 by omega))]
  simp [mass]

