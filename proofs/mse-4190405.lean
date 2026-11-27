import OMAStatements.S_mse_4190405

/-!
# A convergent product for the amplitude of the running standard deviation

The ratio of the running mean to the standard deviation obeys a scalar
recurrence. Each step contracts by the square-root ratio of successive sample
sizes, and moves the limiting fixed point by only a second-order error.
-/

open OMA.S_mse_4190405 Filter
open scoped BigOperators Topology

private noncomputable def D (t a : ℝ) := Real.sqrt (1+t*(1+(a-1)^2))
private noncomputable def F (t a : ℝ) := (a+t)/D t a

private lemma denominator {t a : ℝ} (ht : 0 ≤ t) :
    0 < D t a ∧ (D t a)^2 = 1+t*(1+(a-1)^2) ∧ Real.sqrt (1+t) ≤ D t a := by
  have hp : 0 < 1+t*(1+(a-1)^2) := by positivity
  refine ⟨Real.sqrt_pos.2 hp, Real.sq_sqrt hp.le, Real.sqrt_le_sqrt ?_⟩
  nlinarith [mul_nonneg ht (sq_nonneg (a-1))]

private lemma ordered_step {t a b : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    0 ≤ F t b - F t a ∧ F t b - F t a ≤ (b-a)/Real.sqrt (1+t) := by
  obtain ⟨hA,hAA,hAS⟩ := denominator (a := a) ht
  obtain ⟨hB,hBB,hBS⟩ := denominator (a := b) ht
  have hS : 0 < Real.sqrt (1+t) := Real.sqrt_pos.2 (by linarith)
  have hAB : D t a ≤ D t b := by
    apply Real.sqrt_le_sqrt
    have := mul_nonneg (sub_nonneg.mpr hab) (by linarith : 0 ≤ a+b-2)
    nlinarith [mul_nonneg ht (show 0 ≤ (b-1)^2-(a-1)^2 by linarith)]
  have hp : (a+t)*t ≤ 1+t := by
    nlinarith [mul_nonneg (show 0 ≤ 2-a by linarith) ht,
      mul_nonneg (show 0 ≤ 1-t by linarith) (show 0 ≤ 1/2-t by linarith)]
  have hcap : (a+t)*t*(a+b-2) ≤ D t a*(D t b + D t a) := by
    calc
      _ ≤ (1+t)*2 := mul_le_mul hp (by linarith) (by linarith) (by linarith)
      _ ≤ _ := by nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hAB), mul_nonneg ht (sq_nonneg (a-1))]
  have hm : (a+t)*(D t b - D t a) ≤ (b-a)*D t a := by
    apply le_of_mul_le_mul_right (a := D t b + D t a)
    · calc
        _ = (b-a)*((a+t)*t*(a+b-2)) := by
          linear_combination (a+t)*(hBB - hAA)
        _ ≤ (b-a)*(D t a*(D t b + D t a)) := mul_le_mul_of_nonneg_left hcap (sub_nonneg.mpr hab)
        _ = _ := by ring
    · positivity
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hA hB).2
    linarith
  · calc
      F t b - F t a ≤ (b+t)/D t b - (a+t)/D t b := by
        unfold F
        gcongr
      _ = (b-a)/D t b := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hS hBS

private lemma step_range {t a : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2) (ha : a ∈ Set.Icc 1 2) :
    F t a ∈ Set.Icc 1 2 := by
  have h1 : 1 ≤ F t 1 := by
    obtain ⟨hA,hAA,-⟩ := denominator (a := 1) ht
    apply (le_div_iff₀ hA).2
    nlinarith [sq_nonneg t]
  have h2 : F t 2 ≤ 2 := by
    obtain ⟨hB,hBB,-⟩ := denominator (a := 2) ht
    apply (div_le_iff₀ hB).2
    nlinarith [mul_nonneg ht (show 0 ≤ 4-t by linarith)]
  exact ⟨h1.trans (sub_nonneg.mp (ordered_step ht ht' le_rfl ha.1 ha.2).1),
    (sub_nonneg.mp (ordered_step ht ht' ha.1 ha.2 le_rfl).1).trans h2⟩

private lemma step_lipschitz {t a b : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/2)
    (ha : a ∈ Set.Icc 1 2) (hb : b ∈ Set.Icc 1 2) :
    |F t a - F t b| ≤ |a-b| / Real.sqrt (1+t) := by
  rcases le_total a b with h | h
  · obtain ⟨h0, h1⟩ := ordered_step ht ht' ha.1 h hb.2
    rwa [abs_sub_comm,abs_of_nonneg h0,abs_sub_comm a,abs_of_nonneg (sub_nonneg.mpr h)]
  · obtain ⟨h0, h1⟩ := ordered_step ht ht' hb.1 h ha.2
    simpa [abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr h)] using h1

private lemma tbound (n : ℕ) : 0 < ((n : ℝ)+2)⁻¹ ∧ ((n : ℝ)+2)⁻¹ ≤ 1/2 :=
  ⟨by positivity, by simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n] : (2:ℝ) ≤ n+2))⟩

private lemma ratio_range (n : ℕ) : ratio n ∈ Set.Icc (1 : ℝ) 2 := by
  induction n with
  | zero => norm_num [ratio]
  | succ n ih => exact step_range (tbound n).1.le (tbound n).2 ih

private lemma fixed_error {t r : ℝ} (ht : 0 ≤ t) (hr : r ∈ Set.Icc 1 2)
    (hroot : r*(1+(r-1)^2) = 2) : |F t r - r| ≤ t^2 := by
  obtain ⟨hD,hDD,hS⟩ := denominator (a := r) ht
  have hD1 : 1 ≤ D t r := le_trans (by simpa using (Real.sqrt_le_sqrt (show 1 ≤ 1+t by linarith))) hS
  have h : (r+t)^2 - (r*D t r)^2 = t^2 := by
    linear_combination -(r^2)*hDD - (t*r)*hroot
  have hp : 0 < r+t+r*D t r := by nlinarith [hr.1,mul_pos (by linarith [hr.1] : 0 < r) hD]
  have hpos : 0 ≤ r+t-r*D t r := by
    apply nonneg_of_mul_nonneg_left (b := r+t+r*D t r)
    · nlinarith [sq_nonneg t]
    · exact hp
  have hle : r+t-r*D t r ≤ t^2 := by
    nlinarith [mul_nonneg hpos (show 0 ≤ r+t+r*D t r-1 by nlinarith [hr.1, mul_nonneg (by linarith [hr.1] : 0 ≤ r) hD.le])]
  unfold F
  rw [abs_of_nonneg ((le_div_iff₀ hD).2 (by linarith) |> sub_nonneg.mpr)]
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ hD).2
  nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hD1)]

private noncomputable def N (n : ℕ) : ℝ := n+2
private noncomputable def weight (n : ℕ) : ℝ := 1/(N n*Real.sqrt (N n))

private lemma npos (n : ℕ) : 0 < N n := by unfold N; positivity
private lemma nsucc (n : ℕ) : N (n+1) = N n+1 := by unfold N; push_cast; ring

private lemma weight_summable : Summable weight := by
  have hh := (Real.summable_one_div_nat_add_rpow 2 (3/2)).2 (by norm_num)
  apply hh.congr
  intro n
  change 1/|N n|^(3/2:ℝ) = 1/(N n*Real.sqrt (N n))
  rw [abs_of_pos (npos n), show (3/2:ℝ)=1+1/2 by norm_num, Real.rpow_add (npos n),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

private lemma contraction {r : ℝ} (hr : r ∈ Set.Icc 1 2) (he : r*(1+(r-1)^2)=2) (n : ℕ) :
    Real.sqrt (N (n+1)) * |ratio (n+1)-r| ≤ Real.sqrt (N n)*|ratio n-r|+2*weight n := by
  let t := (N n)⁻¹
  obtain ⟨ht, ht'⟩ := tbound n
  have hdist : |ratio (n+1)-r| ≤ |ratio n-r|/Real.sqrt (1+t)+t^2 := by
    calc
      _ ≤ |F t (ratio n)-F t r| + |F t r-r| := abs_sub_le .. 
      _ ≤ _ := add_le_add (step_lipschitz ht.le ht' (ratio_range n) hr) (fixed_error ht.le hr he)
  have hN := npos n
  have hR := Real.sqrt_pos.2 hN
  have hS := Real.sqrt_pos.2 (show 0 < 1+t by dsimp [t]; positivity)
  have hrel : Real.sqrt (N (n+1)) = Real.sqrt (N n)*Real.sqrt (1+t) := by
    rw [← Real.sqrt_mul hN.le, nsucc]
    congr 1
    dsimp [t]
    field_simp
  have hleR : Real.sqrt (1+t) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by norm_num, by change 1+(N n)⁻¹ ≤ _; dsimp [N]; linarith⟩
  have hsmall : Real.sqrt (N (n+1))*t^2 ≤ 2*weight n := by
    rw [hrel]
    calc
      _ ≤ (Real.sqrt (N n)*2)*t^2 := by gcongr
      _ = 2*weight n := by
        dsimp [t,weight]
        field_simp [hN.ne', hR.ne']
        rw [Real.sq_sqrt hN.le]
  calc
    _ ≤ Real.sqrt (N (n+1))*(|ratio n-r|/Real.sqrt (1+t)+t^2) :=
      mul_le_mul_of_nonneg_left hdist (Real.sqrt_nonneg _)
    _ = Real.sqrt (N n)*|ratio n-r|+Real.sqrt (N (n+1))*t^2 := by
      rw [hrel]; field_simp
    _ ≤ _ := add_le_add le_rfl hsmall

private lemma ratio_estimate {r : ℝ} (hr : r ∈ Set.Icc 1 2) (he : r*(1+(r-1)^2)=2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |ratio n-r| ≤ C/Real.sqrt (N n) := by
  let A (n : ℕ) := Real.sqrt (N n) * |ratio n-r|
  have hA (n : ℕ) : A n ≤ A 0 + 2 * ∑ j ∈ Finset.range n, weight j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [show A (n+1) ≤ A n + 2*weight n from contraction hr he n]
  have hw (j : ℕ) : 0 ≤ weight j := by unfold weight; exact one_div_nonneg.mpr (mul_nonneg (npos _).le (Real.sqrt_nonneg _))
  have hn : 0 ≤ ∑' j, weight j := tsum_nonneg hw
  refine ⟨A 0+2*∑' j, weight j, by dsimp [A]; positivity, ?_⟩
  intro n
  apply (le_div_iff₀ (Real.sqrt_pos.2 (npos n))).2
  rw [mul_comm]
  exact (hA n).trans (by linarith [weight_summable.sum_le_tsum (Finset.range n) (fun j _ => hw j)])

private lemma ratio_converges {r : ℝ} (hr : r ∈ Set.Icc 1 2) (he : r*(1+(r-1)^2)=2) :
    Tendsto ratio atTop (𝓝 r) := by
  obtain ⟨C,-,hC⟩ := ratio_estimate hr he
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hlim : Tendsto (fun n => C/Real.sqrt (N n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (by simpa [Real.dist_eq] using hC) hlim)

private noncomputable def total (x : ℕ → ℝ) (n : ℕ) := ∑ j ∈ Finset.range (n+2), x j
private noncomputable def squares (x : ℕ → ℝ) (n : ℕ) := ∑ j ∈ Finset.range (n+2), (x j)^2

private lemma total_succ (x : ℕ → ℝ) (n : ℕ) :
    total x (n+1) = total x n+x (n+2) := Finset.sum_range_succ ..
private lemma squares_succ (x : ℕ → ℝ) (n : ℕ) :
    squares x (n+1) = squares x n+(x (n+2))^2 := Finset.sum_range_succ ..

private lemma data_state {x : ℕ → ℝ} (hx : 0 < x 0) (he : evolves x) (n : ℕ) :
    0 < x (n+2) ∧ total x n = N n * ratio n * x (n+2) ∧
      squares x n = N n * (1+(ratio n)^2) * (x (n+2))^2 := by
  have hsig (j : ℕ) : x (j+2) = Real.sqrt (squares x j / N j - (total x j / N j)^2) := by
    convert he (j+1) using 2; norm_num [squares,total,N,add_assoc]
  induction n with
  | zero =>
    have h1 : x 1 = 0 := by simpa [evolves,Finset.sum_range_one] using he 0
    have ht : total x 0 = x 0 := by simp [total,Finset.sum_range_succ,h1]
    have hq : squares x 0 = (x 0)^2 := by simp [squares,Finset.sum_range_succ,h1]
    have h2 : x 2 = x 0/2 := by
      rw [hsig 0,ht,hq]
      rw [show ((x 0)^2 / N 0 - (x 0 / N 0)^2) = (x 0/2)^2 by norm_num [N]; ring, Real.sqrt_sq (by positivity)]
    rw [h2,ht,hq]
    norm_num [N,ratio]
    constructor
    · linarith
    · constructor <;> ring
  | succ n ih =>
    obtain ⟨hs,hS,hQ⟩ := ih
    let z := x (n+2)
    let r := ratio n
    let t := (N n)⁻¹
    let d := D t r
    have hN := npos n
    have hp : 0 < N n + 1 := by linarith
    obtain ⟨hD, hDD, -⟩ := denominator (a := r) (t := t) (inv_nonneg.mpr hN.le)
    have hd : 0 < d := hD
    have hD2 : (N n)^2*d^2 = (N n)^2+N n*(1+(r-1)^2) := by
      dsimp only [t] at hDD
      change (N n)^2*(D t r)^2 = _
      rw [hDD]
      field_simp
    have hS' : total x (n+1) = (N n*r+1)*z := by
      rw [total_succ,hS]; dsimp [r,z]; ring
    have hQ' : squares x (n+1) = (N n*(1+r^2)+1)*z^2 := by
      rw [squares_succ,hQ]; dsimp [r,z]; ring
    have hz : x (n+1+2) = z * N n * d / (N n+1) := by
      rw [hsig (n+1), nsucc, hS', hQ']
      have hz' : 0 < z := hs
      apply (congrArg Real.sqrt ?_).trans (Real.sqrt_sq (by positivity))
      field_simp [hp.ne']
      linear_combination -hD2
    have hn : ratio (n+1) = (r+t)/d := rfl
    have hnextS : total x (n+1) = N (n+1)*ratio (n+1)*x (n+1+2) := by
      rw [hS',nsucc,hn,hz]
      dsimp [t]; field_simp [hp.ne',hN.ne',hd.ne']
    refine ⟨?_, hnextS, ?_⟩
    · rw [hz]
      have hz' : 0 < z := hs
      positivity
    · rw [hQ',nsucc,hn,hz]
      dsimp [t]
      field_simp [hp.ne',hN.ne',hd.ne']
      linear_combination -(z^2)*hD2

private lemma log_between {u : ℝ} (hu : 0 ≤ u) :
    u-u^2 ≤ Real.log (1+u) ∧ Real.log (1+u) ≤ u := by
  constructor
  · apply le_trans _ (Real.le_log_one_add_of_nonneg hu)
    apply (le_div_iff₀ (by linarith : 0 < u+2)).2
    nlinarith [sq_nonneg u, pow_nonneg hu 3]
  · linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1+u)]

private lemma corrections_summable {r : ℝ} (hr : r ∈ Set.Icc 1 2) (he : r*(1+(r-1)^2)=2) :
    Summable fun n => |correction r n| := by
  obtain ⟨C,hC,hE⟩ := ratio_estimate hr he
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (weight_summable.mul_left (2+C))
  intro n
  let t := (N n)⁻¹
  let a := ratio n
  have hN := npos n
  have ht : 0 < t := inv_pos.mpr hN
  have ha : 1 ≤ a := (ratio_range n).1
  have hr' : 1 ≤ r := hr.1
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  have hri : 0 < r⁻¹ := inv_pos.mpr hrp
  have hri' : r⁻¹ ≤ 1 := (inv_le_one₀ hrp).mpr hr'
  have hu : 0 ≤ t/a := (div_pos ht hap).le
  have hut : t/a ≤ t := div_le_self ht.le ha
  have hlog1 := log_between hu
  have hlog2 := log_between ht.le
  have hsq : (t/a)^2 ≤ t^2 := by gcongr
  have hloglo := mul_le_mul_of_nonneg_left hlog2.1 hri.le
  have hloghi := mul_le_mul_of_nonneg_left hlog2.2 hri.le
  have hdiff : |t/a-r⁻¹*t| ≤ t*|a-r| := by
    have hh : t/a-r⁻¹*t=t*(r-a)/(a*r) := by field_simp
    rw [hh,abs_div,abs_mul,abs_of_pos ht,abs_of_pos (mul_pos hap hrp),abs_sub_comm r]
    exact div_le_self (mul_nonneg ht.le (abs_nonneg _)) (by nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hr')])
  have hb : |correction r n| ≤ 2*t^2 + t*|a-r| := by
    change |Real.log (1+t/a)-r⁻¹*Real.log (1+t)| ≤ _
    have hd := abs_le.mp hdiff
    apply abs_le.mpr
    constructor <;> nlinarith [hlog1.1,hlog1.2, hd.1,hd.2,
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hri'), sq_nonneg t]
  have hR : 0 < Real.sqrt (N n) := Real.sqrt_pos.2 hN
  have hNN : 1 ≤ N n := by unfold N; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hle : Real.sqrt (N n) ≤ N n := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hN.le, by nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hNN)]⟩
  have ht2 : t^2 ≤ weight n := by
    dsimp [weight,t]
    field_simp [hN.ne', hR.ne']
    nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hle)]
  have hmul : t*|a-r| ≤ C*weight n := by
    calc
      _ ≤ t*(C/Real.sqrt (N n)) := mul_le_mul_of_nonneg_left (hE n) ht.le
      _ = _ := by dsimp [weight,t]; ring
  linarith

private lemma total_formula {x : ℕ → ℝ} (hx : 0 < x 0) (he : evolves x) {r : ℝ}
    (n : ℕ) : total x n = x 0 * (N n)^r⁻¹ / (2:ℝ)^r⁻¹ *
      Real.exp (∑ j ∈ Finset.range n, correction r j) := by
  induction n with
  | zero =>
    have h1 : x 1 = 0 := by simpa [Finset.sum_range_one] using he 0
    simp [total,Finset.sum_range_succ,h1,N, Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) r⁻¹ |>.ne']
  | succ n ih =>
    let t := (N n)⁻¹
    let a := ratio n
    have hN := npos n
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one (ratio_range n).1
    have ht : 0 < t := inv_pos.mpr hN
    have hplus : 0 < 1+t := by linarith
    have hfactor : 0 < 1+t/a := by positivity
    have hN' : N (n+1) = N n*(1+t) := by rw [nsucc]; dsimp [t]; field_simp
    have hadd : total x (n+1) = total x n*(1+t/a) := by
      obtain ⟨_,hS,_⟩ := data_state hx he n
      rw [total_succ,hS]
      change N n*a*x (n+2)+x (n+2) = N n*a*x (n+2)*(1+(N n)⁻¹/a)
      field_simp
    have hexp : Real.exp (correction r n) = (1+t/a)/(1+t)^r⁻¹ := by
      change Real.exp (Real.log (1+t/a)-r⁻¹*Real.log (1+t))=_
      rw [Real.exp_sub,Real.exp_log hfactor,mul_comm r⁻¹,← Real.rpow_def_of_pos hplus]
    rw [hadd,ih,Finset.sum_range_succ,Real.exp_add,hexp,hN',Real.mul_rpow hN.le hplus.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hplus r⁻¹)]

private lemma scaled_data {x : ℕ → ℝ} (hx : 0 < x 0) (he : evolves x) (r : ℝ) (n : ℕ) :
    ((n:ℝ)+3)^(1-r⁻¹) * x (n+2) / x 0 =
      (1+(N n)⁻¹)^(1-r⁻¹) *
        (Real.exp (∑ j ∈ Finset.range n, correction r j) / ((2:ℝ)^r⁻¹ * ratio n)) := by
  have hN := npos n
  have hR := lt_of_lt_of_le zero_lt_one (ratio_range n).1
  have hD : 0 < (2:ℝ)^r⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hp : (n:ℝ)+3 = N n * (1+(N n)⁻¹) := by
    change _ = ((n:ℝ)+2)*(1+((n:ℝ)+2)⁻¹)
    have hpos : 0 < (n:ℝ)+2 := by positivity
    field_simp
    ring
  have hstep := (data_state hx he n).2.1
  rw [total_formula hx he (r := r)] at hstep
  have hprod : (N n)^(1-r⁻¹)*(N n)^r⁻¹ = N n := by
    rw [← Real.rpow_add hN]; simp
  have hx' : x (n+2) = x 0*(N n)^r⁻¹ * Real.exp (∑ j ∈ Finset.range n, correction r j) /
      ((2:ℝ)^r⁻¹*N n*ratio n) := by
    apply (eq_div_iff (by positivity)).2
    field_simp [hD.ne'] at hstep
    simp only [one_div] at hstep
    linarith
  rw [hx',hp,Real.mul_rpow hN.le (by positivity)]
  field_simp [hN.ne',hD.ne',hx.ne',hR.ne']
  simpa only [one_div] using hprod

private lemma final_limit {r : ℝ} (hr : r ∈ Set.Icc 1 2) (hf : r*(1+(r-1)^2)=2)
    {x : ℕ → ℝ} (hx : 0 < x 0) (he : evolves x) :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)^(1-r⁻¹)*x n/x 0) atTop (𝓝 (amplitude r)) := by
  have hN : Tendsto N atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ht : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hN
  have hpt : Tendsto (fun n => (1+(N n)⁻¹)^(1-r⁻¹)) atTop (𝓝 1) := by
    have ht' : Tendsto (fun n => 1+(N n)⁻¹) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1:ℝ))).add ht
    simpa using (ht'.rpow_const (p := 1-r⁻¹) (Or.inl one_ne_zero))
  have hsum := (corrections_summable hr hf).of_abs.hasSum.tendsto_sum_nat
  have hrat := ratio_converges hr hf
  have hrp := lt_of_lt_of_le zero_lt_one hr.1
  have hp := hpt.mul ((Real.continuous_exp.continuousAt.tendsto.comp hsum).div
    (tendsto_const_nhds.mul hrat) (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) r⁻¹)) hrp.ne'))
  apply (tendsto_add_atTop_iff_nat 2).mp
  convert hp using 1
  · funext n
    push_cast
    simpa only [Pi.div_apply, Function.comp_apply, add_assoc, show (2:ℝ)+1=3 by norm_num] using scaled_data hx he r n
  · simp [amplitude,mul_comm]

private lemma evaluate_exponent {a : ℝ} (ha : a^2 = (1-2*a)*(1-a)^2) :
    a = exponent := by
  let k := ((13+3*Real.sqrt 33)/4 : ℝ)
  let z := k^(1/3:ℝ)
  have hk : 0 < k := by dsimp [k]; positivity
  have hz : 0 < z := Real.rpow_pos_of_pos hk _
  have hz3 : z^3 = k := by
    dsimp [z]
    rw [← Real.rpow_natCast (k^(1/3:ℝ)) 3, ← Real.rpow_mul hk.le]
    norm_num
  have hkpoly : 2*k^2-13*k-16=0 := by
    dsimp [k]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤33)]
  let u := 3*a-2
  let v := 2/z-z
  have hu : 2*u^3+12*u+13=0 := by dsimp [u]; nlinarith [ha]
  have hv : 2*v^3+12*v+13=0 := by
    dsimp [v]
    field_simp [hz.ne']
    rw [← hz3] at hkpoly
    nlinarith [hkpoly]
  have hfac : (u-v)*(2*u^2+2*u*v+2*v^2+12)=0 := by nlinarith [hu,hv]
  have hpos : 0 < 2*u^2+2*u*v+2*v^2+12 := by
    nlinarith [sq_nonneg (u+v),sq_nonneg u,sq_nonneg v]
  have huv := (mul_eq_zero.mp hfac).resolve_right hpos.ne'
  change a = (2+2/z-z)/3
  dsimp [u,v] at huv
  linarith

theorem OMA.solution : type_of% @OMA.S_mse_4190405.main := by
  let f (r : ℝ) := r*(1+(r-1)^2)
  obtain ⟨r, hr, he⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 2)
    (f := f) (by fun_prop) (show (2:ℝ) ∈ Set.Ioo (f 1) (f 2) by norm_num [f])
  change r*(1+(r-1)^2) = 2 at he
  obtain ⟨hl,hu⟩ := hr
  have hrp : 0 < r := by linarith
  have hr' : r ∈ Set.Icc (1:ℝ) 2 := ⟨hl.le,hu.le⟩
  have hpoly : (1-r⁻¹)^2 = (1-2*(1-r⁻¹))*(1-(1-r⁻¹))^2 := by
    field_simp [hrp.ne']
    nlinarith [he]
  refine ⟨r, ⟨hl,hu⟩, he, ⟨?_,?_⟩, hpoly, evaluate_exponent hpoly, corrections_summable hr' he, ?_, fun x hx hx' => final_limit hr' he hx hx'⟩
  · have := (inv_lt_one₀ hrp).2 hl
    linarith
  · have := one_div_lt_one_div_of_lt hrp hu
    simp only [one_div] at this ⊢
    linarith
  · unfold amplitude
    positivity
