import OMAStatements.S_mo_429627

namespace OMA.R_mo_429627_R1
open OMA.S_mo_429627 Filter Topology

def H1 : Prop := ∀ a : ℝ, 0 < a → bounded a
def H2 : Prop := ∀ a : ℝ, 0 < a → bounded a → ∃ v : ℂ,
  Tendsto (fun k => z a k - v * phase k) atTop (𝓝 0)
def H3 : Prop := ∀ a : ℝ, 0 < a → ¬Tendsto (z a) atTop (𝓝 0)

theorem state_pos {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 < (state a k).1 ∧ 0 < (state a k).2 := by
  induction k with
  | zero => exact ⟨ha, ha⟩
  | succ k ih =>
    simp only [state]
    have := ih.1
    have := ih.2
    constructor <;> positivity

/-- One step of the centered recurrence in rational coordinates. -/
theorem centered_step {a : ℝ} (ha : 0 < a) (k : ℕ) :
    let n := idx k
    let v := u a k
    let y := Y a k
    let t := 2*n+y-1/2
    let h := (2*v-y)/t + (v-y/2-3/4)/t^2
    let s := (v+h)/(n+1)
    u a (k+1) = v+h-s ∧ Y a (k+1) = y+s := by
  dsimp only
  let n := idx k
  let A := (state a k).1
  let S := (state a k).2
  let t := 2*n+Y a k-1/2
  let h := (2*u a k-Y a k)/t+(u a k-Y a k/2-3/4)/t^2
  have hn : 0 < n := by dsimp [n,idx]; positivity
  have hA : 0 < A := (state_pos ha k).1
  have hS : 0 < S := (state_pos ha k).2
  have ht : t = A*S/n := by dsimp [t,n,A,S,Y]; ring
  have ht0 : 0 < t := by rw [ht]; positivity
  have hT : t*n=A*S := by rw [ht]; field_simp
  have hAs : A+n/S=A*(1+1/t) := by rw [ht]; field_simp
  have hN : idx (k+1) = n+1 := by simp [n,idx]
  have hnext : (state a (k+1)).1 = A+n/S := rfl
  have hsnext : (state a (k+1)).2 = S+(A+n/S) := rfl
  have hA2 : A^2 = D a k+3*n-3/2 := by dsimp [A,D,n]; ring
  have hd : D a (k+1) = D a k+h := by
    simp only [D, hnext,hN]
    change (A+n/S)^2-3*(n+1)+3/2 = A^2-3*n+3/2+h
    rw [hAs, mul_pow]
    dsimp only [h]
    rw [hA2]
    have hu : D a k = u a k + Y a k := by simp [u]
    rw [hu]
    field_simp
    dsimp only [t]
    ring
  have hy : Y a (k+1) = Y a k + (u a k+h)/(n+1) := by
    have hd' := hd
    simp only [D,hnext,hN] at hd'
    change (A+n/S)^2-3*(n+1)+3/2=A^2-3*n+3/2+h at hd'
    have hlin : (A+n/S)*S=n*(t+1) := by field_simp; nlinarith [hT]
    have hn1 : n+1 ≠ 0 := by positivity
    simp only [Y,hnext,hsnext,hN]
    change (A+n/S)*(S+(A+n/S))/(n+1)-2*(n+1)+1/2 =
      A*S/n-2*n+1/2+(u a k+h)/(n+1)
    have hsq : (A+n/S)^2=A^2+3+h := by linarith [hd']
    rw [mul_add, hlin, ← sq, hsq, ← ht]
    rw [show u a k = A^2-3*n+3/2-(t-2*n+1/2) by dsimp [u,A,n,t,D]; ring]
    field_simp
    ring
  change u a (k+1) = u a k+h-(u a k+h)/(n+1) ∧ _
  exact ⟨by unfold u at *; rw [hd,hy]; ring,hy⟩

private theorem correction_error {a : ℝ} (ha : 0 < a) (hb : bounded a) :
    Tendsto (fun k => correction a k - (Real.sqrt 3/4-D a k/(2*Real.sqrt 3))) atTop (𝓝 0) := by
  obtain ⟨R,hR⟩ := hb
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h2 : 0 < Real.sqrt 2 := by positivity
  have h3 : 0 < Real.sqrt 3 := by positivity
  let C := (3/2 + (1 + Real.sqrt 2)*|R|) / Real.sqrt 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᶠ k in atTop, |correction a k| ≤ C := by
    filter_upwards [hR] with k hk
    have hn : 0 < idx k := by dsimp [idx]; positivity
    have hsn := Real.sq_sqrt hn.le
    have hsn' : 0 < Real.sqrt (idx k) := Real.sqrt_pos.mpr hn
    have hh := (state_pos ha k).1
    have hu : |u a k| ≤ |R| := (Complex.abs_re_le_norm (z a k)).trans (hk.trans (le_abs_self R))
    have hy : |Y a k / Real.sqrt 2| ≤ |R| :=
      (Complex.abs_im_le_norm (z a k)).trans (hk.trans (le_abs_self R))
    rw [abs_div, abs_of_pos h2, div_le_iff₀ h2] at hy
    have hd : |D a k| ≤ (1+Real.sqrt 2)*|R| := calc
      _ = |u a k + Y a k| := by simp [u]
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
    have hid : correction a k * (Real.sqrt 3 + (state a k).1/Real.sqrt (idx k)) =
        3/2 - D a k := by
      change (idx k * Real.sqrt 3 - (state a k).1*Real.sqrt (idx k))*_ = _
      unfold D; field_simp; ring_nf; simp only [hs, hsn]; ring
    have hf : Real.sqrt 3 ≤ Real.sqrt 3 + (state a k).1/Real.sqrt (idx k) := le_add_of_nonneg_right (by positivity)
    apply (le_div_iff₀ h3).mpr
    calc
      |correction a k| * Real.sqrt 3 ≤
          |correction a k| * (Real.sqrt 3 + (state a k).1/Real.sqrt (idx k)) :=
        mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      _ = |3/2 - D a k| := by rw [← hid, abs_mul, abs_of_pos (h3.trans_le hf)]
      _ ≤ |(3:ℝ)/2| + |D a k| := abs_sub _ _
      _ ≤ _ := by norm_num; linarith
  have exact_error k :
      correction a k - (Real.sqrt 3/4-D a k/(2*Real.sqrt 3)) =
        (correction a k)^2 / (2*Real.sqrt 3*idx k) := by
    have hn : 0 < idx k := by dsimp [idx]; positivity
    have hsn := Real.sq_sqrt hn.le
    change (idx k * Real.sqrt 3 - (state a k).1*Real.sqrt (idx k)) - _ =
      (idx k * Real.sqrt 3 - (state a k).1*Real.sqrt (idx k))^2 / _
    unfold D
    field_simp
    ring_nf; simp only [hs, hsn]; ring
  have hnlim : Tendsto idx atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hlim : Tendsto (fun k => (C^2/(2*Real.sqrt 3)) / idx k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hbound] with k hk
  rw [exact_error, Real.norm_eq_abs, abs_of_nonneg (by unfold idx; positivity),
    div_mul_eq_div_div]
  have hn : 0 ≤ idx k := by unfold idx; positivity
  apply div_le_div_of_nonneg_right _ hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hk 2)

theorem combine : H1 → H2 → H3 → (∀ a : ℝ, 0 < a → ∃ w : ℂ, w ≠ 0 ∧
    Tendsto (fun k => correction a k - (Real.sqrt 3 / 4 + (w * phase k).re)) atTop (𝓝 0)) := by
  intro h1 h2 h3 a ha
  obtain ⟨v,hv⟩ := h2 a ha (h1 a ha)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact h3 a ha (by simpa using hv)
  let c : ℂ := ⟨1, -(Real.sqrt 2)⟩
  let w := (((-(1/(2*Real.sqrt 3)) : ℝ) : ℂ))*(c*v)
  refine ⟨w, ?_, ?_⟩
  · have hc : c ≠ 0 := by intro h; exact one_ne_zero (congrArg Complex.re h)
    exact mul_ne_zero (by dsimp; norm_num) (mul_ne_zero hc hv0)
  have h : Tendsto (fun k => (c*(z a k - v*phase k)).re / (2*Real.sqrt 3)) atTop (𝓝 0) := by
    simpa using (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul hv)).div_const (2*Real.sqrt 3)
  convert (correction_error ha (h1 a ha)).sub h using 2 with k
  · have hcz : (c*z a k).re = D a k := by
      simp [c,Complex.mul_re,z,u]; field_simp; ring
    change correction a k - (Real.sqrt 3/4 +
      ((((-(1/(2*Real.sqrt 3)):ℝ):ℂ))*(c*v)*phase k).re) = _
    rw [mul_assoc, mul_assoc, Complex.re_ofReal_mul, mul_sub, Complex.sub_re, hcz]
    ring
  · ring

end OMA.R_mo_429627_R1

namespace MO429627Phase
open OMA.S_mo_429627 OMA.R_mo_429627_R1 Filter Topology

private theorem scalar_error {n R v y : ℝ} (hR : 1 ≤ R) (hn : 2*R+1 ≤ n)
    (hv : |v| ≤ R) (hy : |y| ≤ 2*R) :
    let t := 2*n+y-1/2
    let h := (2*v-y)/t+(v-y/2-3/4)/t^2
    let s := (v+h)/(n+1)
    |h-s+y/(2*n)| ≤ 17*R^2/n^2 ∧ |s-v/n| ≤ 8*R/n^2 := by
  dsimp only
  let t := 2*n+y-1/2
  let h := (2*v-y)/t+(v-y/2-3/4)/t^2
  let s := (v+h)/(n+1)
  have vabs := abs_le.mp hv
  have yabs := abs_le.mp hy
  have hn0 : 0 < n := by linarith
  have hnt : n ≤ t := by dsimp [t]; linarith
  have ht : 0 < t := hn0.trans_le hnt
  have hnum1 : |2*v-y| ≤ 4*R := abs_le.mpr ⟨by linarith,by linarith⟩
  have hnum2 : |v-y/2-3/4| ≤ 3*R := abs_le.mpr ⟨by linarith,by linarith⟩
  have hnum3 : |1/2-y| ≤ 3*R := abs_le.mpr ⟨by linarith,by linarith⟩
  have aux1 : |(2*v-y)/t| ≤ 4*R/n := by
    rw [abs_div,abs_of_pos ht]; gcongr
  have aux2 : |(v-y/2-3/4)/t^2| ≤ 3*R/n^2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos ht)]; gcongr
  have hh : |h| ≤ 7*R/n := calc
    |h| ≤ _ := abs_add_le _ _
    _ ≤ 4*R/n+3*R/n^2 := add_le_add aux1 aux2
    _ ≤ _ := by field_simp; nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ n-1 by linarith)]
  have heq : h-(2*v-y)/(2*n) =
      (2*v-y)*(1/2-y)/(2*n*t)+(v-y/2-3/4)/t^2 := by
    dsimp only [h]; field_simp; dsimp [t]; ring
  have he : |h-(2*v-y)/(2*n)| ≤ 9*R^2/n^2 := by
    rw [heq]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ (4*R)*(3*R)/(2*n*n) + 3*R/n^2 := by
        apply add_le_add _ aux2
        rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 2*n*t)]
        gcongr
      _ ≤ _ := by field_simp; nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ R-1 by linarith)]
  have hs : |s-v/n| ≤ 8*R/n^2 := by
    have hid : s-v/n = (n*h-v)/(n*(n+1)) := by dsimp [s]; field_simp; ring
    rw [hid,abs_div,abs_of_pos (by positivity : 0 < n*(n+1))]
    calc
      |n*h-v|/(n*(n+1)) ≤ (n*(7*R/n)+R)/(n*n) := by
        have hnv : |n*h-v| ≤ n*(7*R/n)+R := by
          refine (abs_sub (n*h) v).trans ?_
          rw [abs_mul, abs_of_pos hn0]
          exact add_le_add (mul_le_mul_of_nonneg_left hh hn0.le) hv
        exact div_le_div₀ (by positivity) hnv (by positivity) (by nlinarith)
      _ = _ := by field_simp; ring
  refine ⟨?_,hs⟩
  change |h-s+y/(2*n)| ≤ _
  have heq' : h-s+y/(2*n) = (h-(2*v-y)/(2*n))-(s-v/n) := by ring
  rw [heq']
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ 9*R^2/n^2+8*R/n^2 := add_le_add he hs
    _ ≤ _ := by
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ R-1 by linarith)]

noncomputable def freq : ℝ := 1 / Real.sqrt 2

private theorem freq_bounds : 0 < freq ∧ freq ≤ 1 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h' : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  exact ⟨by unfold freq; positivity, (div_le_one (by positivity)).mpr h'⟩

private theorem phase_error {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖Complex.exp (Complex.I * ((freq*Real.log (1+t) : ℝ) : ℂ)) -
        (1 + Complex.I * ((freq*t : ℝ) : ℂ))‖ ≤ 2*t^2 := by
  let d := Real.log (1+t)
  have hd0 : 0 ≤ d := Real.log_nonneg (by linarith)
  have hd1 : d ≤ t := by simpa [d] using Real.log_le_sub_one_of_pos (by linarith : 0 < 1+t)
  have hd2 : |d-t| ≤ t^2 := by
    rw [abs_of_nonpos (by linarith)]
    have h := Real.le_log_one_add_of_nonneg ht.le
    change 2*t/(t+2) ≤ d at h
    rw [div_le_iff₀ (by linarith)] at h
    nlinarith [mul_le_mul_of_nonneg_right hd1 ht.le, sq_nonneg t]
  let x : ℂ := Complex.I*((freq*d:ℝ):ℂ)
  let y : ℂ := Complex.I*((freq*t:ℝ):ℂ)
  have hx : ‖x‖ ≤ t := by
    simp only [x,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos freq_bounds.1, abs_of_nonneg hd0]
    exact (mul_le_of_le_one_left hd0 freq_bounds.2).trans hd1
  have hxy : ‖x-y‖ ≤ t^2 := by
    have id' : x-y=Complex.I*((freq*(d-t):ℝ):ℂ) := by dsimp [x,y]; push_cast; ring
    rw [id', norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_pos freq_bounds.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) freq_bounds.2).trans hd2
  change ‖Complex.exp x-(1+y)‖ ≤ _
  calc
    _ = ‖(Complex.exp x-1-x)+(x-y)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ t^2+t^2 := add_le_add ((Complex.norm_exp_sub_one_sub_id_le (hx.trans ht1)).trans
      (pow_le_pow_left₀ (norm_nonneg _) hx 2)) hxy
    _ = _ := by ring

private theorem phase_norm (k : ℕ) : ‖phase k‖ = 1 := by
  rw [phase,mul_comm,Complex.norm_exp_ofReal_mul_I]

private theorem phase_step (k : ℕ) : phase (k+1) =
    Complex.exp (Complex.I*((freq*Real.log (1+1/idx k):ℝ):ℂ))*phase k := by
  have hn : 0 < idx k := by dsimp [idx]; positivity
  have hN : idx (k+1) = (1+1/idx k)*idx k := by simp [idx]; field_simp
  change Complex.exp (Complex.I*((Real.log (idx (k+1))/Real.sqrt 2:ℝ):ℂ)) = _
  rw [hN, Real.log_mul (by positivity) hn.ne', phase, ← Complex.exp_add]
  congr 1
  dsimp only [phase,idx,freq]
  push_cast
  ring

private theorem euler_error {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 1 ≤ R)
    {k : ℕ} (hk : 2*R+1 ≤ idx k) (hz : ‖z a k‖ ≤ R) :
    ‖z a (k+1) - (1+Complex.I*((freq*(1/idx k):ℝ):ℂ))*z a k‖ ≤ 25*R^2/(idx k)^2 := by
  let n := idx k
  let v := u a k
  let y := Y a k
  let t := 2*n+y-1/2
  let h := (2*v-y)/t+(v-y/2-3/4)/t^2
  let s := (v+h)/(n+1)
  have hn : 0 < n := by dsimp [n,idx]; positivity
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hv : |v| ≤ R := (Complex.abs_re_le_norm (z a k)).trans hz
  have hy : |y| ≤ 2*R := by
    have hp : |y/Real.sqrt 2| ≤ R := (Complex.abs_im_le_norm (z a k)).trans hz
    rw [abs_div,abs_of_pos hs,div_le_iff₀ hs] at hp
    nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ 2-Real.sqrt 2 by nlinarith)]
  obtain ⟨hu',hy'⟩ := centered_step ha k
  change u a (k+1) = v+h-s at hu'
  change Y a (k+1) = y+s at hy'
  obtain ⟨he1,he2⟩ := scalar_error hR hk hv hy
  change |h-s+y/(2*n)| ≤ _ at he1
  change |s-v/n| ≤ _ at he2
  let b := z a (k+1) - (1+Complex.I*((freq*(1/n):ℝ):ℂ))*z a k
  have bre : b.re = h-s+y/(2*n) := by
    simp only [b,z,Complex.sub_re,Complex.mul_re,Complex.add_re,Complex.add_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,
      Complex.one_im,Complex.mul_im,hu',freq]
    dsimp only [v,y,n] at *
    field_simp; ring_nf; simp only [hs2]; ring
  have bim : b.im = (s-v/n)/Real.sqrt 2 := by
    simp only [b,z,Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.add_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,
      Complex.one_im,hy',freq]
    dsimp only [v,y,n] at *
    field_simp; ring
  calc
    ‖b‖ ≤ _ := Complex.norm_le_abs_re_add_abs_im b
    _ ≤ 17*R^2/n^2+8*R/n^2 := by
      rw [bre,bim,abs_div,abs_of_pos hs]
      exact add_le_add he1 ((div_le_self (abs_nonneg _) hs1).trans he2)
    _ ≤ _ := by dsimp only [n] at *; field_simp; nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ R-1 by linarith)]

noncomputable def demod (a : ℝ) (k : ℕ) := z a k / phase k

private theorem step_error {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 1 ≤ R)
    {k : ℕ} (hk : 2*R+1 ≤ idx k) (hz : ‖z a k‖ ≤ R) :
    dist (demod a k) (demod a (k+1)) ≤ 27*R^2/(idx k)^2 := by
  let n := idx k
  let rot := Complex.exp (Complex.I*((freq*Real.log (1+1/n):ℝ):ℂ))
  let lin : ℂ := 1+Complex.I*((freq*(1/n):ℝ):ℂ)
  have hn : 0 < n := by dsimp [n,idx]; positivity
  have hn1 : 1 ≤ n := by dsimp [n] at *; linarith
  have he : ‖rot-lin‖ ≤ 2*(1/n)^2 :=
    phase_error (by positivity) ((div_le_one hn).mpr hn1)
  have heu : ‖z a (k+1)-lin*z a k‖ ≤ 25*R^2/n^2 := euler_error ha hR hk hz
  have hph : phase (k+1)=rot*phase k := phase_step k
  have hph0 : phase k ≠ 0 := Complex.exp_ne_zero _
  have hrot : rot ≠ 0 := Complex.exp_ne_zero _
  have hid : demod a (k+1)-demod a k=(z a (k+1)-rot*z a k)/phase (k+1) := by
    dsimp only [demod]; rw [hph]; field_simp
  rw [dist_comm,dist_eq_norm,hid,norm_div,phase_norm,div_one]
  calc
    _ = ‖(z a (k+1)-lin*z a k) - (rot-lin)*z a k‖ := by congr 1; ring
    _ ≤ _ := norm_sub_le _ _
    _ ≤ 25*R^2/n^2 + 2*(1/n)^2*R := by
      rw [norm_mul]; gcongr
    _ ≤ _ := by dsimp only [n] at *; field_simp; nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ R-1 by linarith)]

end MO429627Phase

open OMA.S_mo_429627 OMA.R_mo_429627_R1 MO429627Phase Filter Topology in
private theorem phase_conclusion : OMA.R_mo_429627_R1.H2 := by
  intro a ha hb
  obtain ⟨R',hb⟩ := hb
  let R := max 1 R'
  have hR : 1 ≤ R := le_max_left _ _
  have hi : Tendsto idx atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  have hstep : ∀ᶠ k in atTop, dist (demod a k) (demod a (k+1)) ≤ 27*R^2/(idx k)^2 := by
    filter_upwards [hb,hi.eventually_ge_atTop (2*R+1)] with k hb hk
    exact step_error ha hR hk (hb.trans (le_max_right _ _))
  have hs : Summable (fun k => 27*R^2/(idx k)^2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2))
    simpa [idx,div_eq_mul_inv] using this.mul_left (27*R^2)
  have hc : CauchySeq (demod a) := by
    apply cauchySeq_of_summable_dist
    apply hs.of_norm_bounded_eventually
    simpa [Nat.cofinite_eq_atTop,Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hstep
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  have h := (hv.sub_const v).norm
  simp only [sub_self, norm_zero] at h
  convert h using 2 with k
  have hp : phase k ≠ 0 := Complex.exp_ne_zero _
  have id' : z a k-v*phase k=(demod a k-v)*phase k := by dsimp [demod]; field_simp
  rw [id', norm_mul,phase_norm,mul_one]

namespace MO429627Nonzero
open OMA.S_mo_429627 OMA.R_mo_429627_R1 Filter Topology

private noncomputable def rate (k : ℕ) := 1 / idx k
private noncomputable def P (a : ℝ) (k : ℕ) := u a k - rate k/8
private noncomputable def Q (a : ℝ) (k : ℕ) := Y a k + rate k/8
private noncomputable def remZ (a : ℝ) (k : ℕ) : ℂ := ⟨P a k, Q a k / Real.sqrt 2⟩

private noncomputable def alpha (v y r : ℝ) :=
  let d := 2+(y-1/2)*r
  (2*v-y)*(1/2-y)/(2*d)+(v-y/2-3/4)/d^2

private noncomputable def beta (v y r : ℝ) :=
  let d := 2+(y-1/2)*r
  ((2*v-y)/d+(v-y/2-3/4)*r/d^2-v)/(1+r)

private theorem expansion {n v y : ℝ} (hn : 0 < n) (ht : 0 < 2*n+y-1/2) :
    let r := 1/n
    let t := 2*n+y-1/2
    let h := (2*v-y)/t+(v-y/2-3/4)/t^2
    let s := (v+h)/(n+1)
    let p := v-r/8
    let q := y+r/8
    n^2*((v+h-s-1/(n+1)/8) - (p-q/(2*n))) =
      alpha v y r - beta v y r + 1/(8*(1+r))+1/16 ∧
    n^2*((y+s+1/(n+1)/8) - (q+p/n)) =
      beta v y r + r/(8*(1+r)) := by
  dsimp only
  let t := 2*n+y-1/2
  let h := (2*v-y)/t+(v-y/2-3/4)/t^2
  let s := (v+h)/(n+1)
  have hn1 : n+1 ≠ 0 := by positivity
  have hr : 1+1/n ≠ 0 := by positivity
  have ht0 : t ≠ 0 := ht.ne'
  have hd : 2+(y-1/2)*(1/n) = t/n := by dsimp only [t]; field_simp; ring
  have hal : n^2*(h-(2*v-y)/(2*n))=alpha v y (1/n) := by
    dsimp only [alpha,h]; rw [hd]; field_simp; dsimp only [t]; ring
  have hbe : n^2*(s-v/n)=beta v y (1/n) := by
    dsimp only [beta,s,h]; rw [hd]; field_simp; ring
  change n^2*((v+h-s-1/(n+1)/8)-_) = _ ∧ n^2*((y+s+1/(n+1)/8)-_) = _
  rw [← hal, ← hbe]
  constructor <;> field_simp <;> ring

private theorem rate_tendsto : Tendsto rate atTop (𝓝 0) := by
  have hn : Tendsto idx atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
  exact tendsto_const_nhds.div_atTop hn

private theorem errors_vanish {a : ℝ} (ha : 0 < a) (hh : Tendsto (z a) atTop (𝓝 0)) :
    let eu := fun k => (idx k)^2*(P a (k+1) - (P a k - Q a k/(2*idx k)))
    let ey := fun k => (idx k)^2*(Q a (k+1) - (Q a k + P a k/idx k))
    Tendsto eu atTop (𝓝 0) ∧ Tendsto ey atTop (𝓝 0) := by
  dsimp only
  have hv : Tendsto (u a) atTop (𝓝 0) := by
    simpa [z, Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hh
  have hy : Tendsto (Y a) atTop (𝓝 0) := by
    have ht := (Complex.continuous_im.continuousAt.tendsto.comp hh).mul_const (Real.sqrt 2)
    simpa [z, Function.comp_def, Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)] using ht
  have hd : Tendsto (fun k => 2+(Y a k-1/2)*rate k) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add ((hy.sub_const (1/2)).mul rate_tendsto)
  have hal : Tendsto (fun k => alpha (u a k) (Y a k) (rate k)) atTop (𝓝 (-(3/16))) := by
    unfold alpha; convert (((hv.const_mul 2).sub hy).mul ((tendsto_const_nhds (x := (1/2:ℝ))).sub hy)).div
      (hd.const_mul 2) (by norm_num) |>.add
      (((hv.sub (hy.div_const 2)).sub_const (3/4)).div (hd.pow 2) (by norm_num)) using 1 <;> norm_num
  have hbe : Tendsto (fun k => beta (u a k) (Y a k) (rate k)) atTop (𝓝 0) := by
    unfold beta
    convert (((((hv.const_mul 2).sub hy).div hd (by norm_num)).add
      ((((hv.sub (hy.div_const 2)).sub_const (3/4)).mul rate_tendsto).div
        (hd.pow 2) (by norm_num))).sub hv).div ((tendsto_const_nhds (x := (1:ℝ))).add rate_tendsto)
          (by norm_num) using 1 <;> norm_num <;> rfl
  have hx k := expansion (v := u a k) (y := Y a k) (n := idx k)
    (show 0 < idx k by dsimp [idx]; positivity)
    (show 0 < 2*idx k+Y a k-1/2 by
      obtain ⟨hp,hs⟩ := state_pos ha k
      unfold Y
      ring_nf
      have hn : 0 < idx k := by dsimp [idx]; positivity
      positivity)
  have hid (k : ℕ) : idx (k+1) = idx k+1 := by simp [idx]
  constructor
  · have main : Tendsto (fun k => alpha (u a k) (Y a k) (rate k) -
        beta (u a k) (Y a k) (rate k) + 1/(8*(1+rate k))+1/16) atTop (𝓝 0) := by
      convert (((hal.sub hbe).add ((tendsto_const_nhds (x := (1:ℝ))).div
        (((tendsto_const_nhds (x := (1:ℝ))).add rate_tendsto).const_mul 8) (by norm_num))).add_const (1/16)) using 1 <;> norm_num
    apply main.congr
    intro k
    obtain ⟨hu,hy⟩ := centered_step ha k
    unfold P Q rate
    rw [hu,hid]
    exact (hx k).1.symm
  · have main : Tendsto (fun k => beta (u a k) (Y a k) (rate k) +
        rate k/(8*(1+rate k))) atTop (𝓝 0) := by
      convert hbe.add (rate_tendsto.div (((tendsto_const_nhds (x := (1:ℝ))).add rate_tendsto).const_mul 8)
        (by norm_num)) using 1 <;> norm_num
    apply main.congr
    intro k
    obtain ⟨hu,hy⟩ := centered_step ha k
    unfold P Q rate
    rw [hy,hid]
    exact (hx k).2.symm

private theorem radius_step (a : ℝ) (k : ℕ) :
    let n := idx k
    let p := P a k
    let q := Q a k
    ‖remZ a k‖ ≤ ‖remZ a (k+1)‖ +
      |P a (k+1)-(p-q/(2*n))| + |Q a (k+1)-(q+p/n)| := by
  dsimp only
  let n := idx k
  let l : ℂ := 1+Complex.I*((1/(n*Real.sqrt 2):ℝ):ℂ)
  have hn : 0 < n := by dsimp [n,idx]; positivity
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs : 0 < Real.sqrt 2 := by positivity
  have h1 : 1 ≤ Real.sqrt 2 := by nlinarith
  have hl : 1 ≤ ‖l‖ := by simpa [l,Complex.add_re,Complex.mul_re] using Complex.abs_re_le_norm l
  have hr : (l * remZ a k).re = P a k-Q a k/(2*n) := by
    simp [l,remZ,Complex.mul_re]
    field_simp
  have hi : (l * remZ a k).im = (Q a k+P a k/n)/Real.sqrt 2 := by
    simp [l,remZ,Complex.mul_im]
    field_simp <;> ring_nf <;> simp only [h2] <;> ring
  have herr := Complex.norm_le_abs_re_add_abs_im (remZ a (k+1)-l*remZ a k)
  rw [Complex.sub_re, Complex.sub_im,hr,hi] at herr
  change ‖_‖ ≤ |P a (k+1)-_| + |Q a (k+1)/Real.sqrt 2-_| at herr
  rw [← sub_div,abs_div,abs_of_pos hs] at herr
  have he := norm_sub_le (remZ a (k+1)) (remZ a (k+1)-l*remZ a k)
  rw [sub_sub_cancel, norm_mul] at he
  have hl' := mul_le_mul_of_nonneg_right hl (norm_nonneg (remZ a k))
  have hab := div_le_self (abs_nonneg (Q a (k+1)-(Q a k+P a k/n))) h1
  change ‖remZ a k‖ ≤ ‖remZ a (k+1)‖ + |P a (k+1)-(P a k-Q a k/(2*n))| +
    |Q a (k+1)-(Q a k+P a k/n)|
  linarith

private theorem bound_backward {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (he : ∀ᶠ k in atTop, f k ≤ f (k+1)+(1/256)/(idx k)^2) :
    ∀ᶠ k in atTop, f k ≤ (1/128)*rate k := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  have hmono (i : ℕ) (hi : N ≤ i) :
      f i-(1/128)*rate i ≤ f (i+1)-(1/128)*rate (i+1) := by
    have hn : 1 ≤ idx i := by dsimp [idx]; exact le_add_of_nonneg_left (by positivity)
    have he' := hN i hi
    have hle : (1/256)/(idx i)^2 ≤ (1/128)*(rate i-rate (i+1)) := by
      rw [rate,rate,show idx (i+1)=idx i+1 by simp [idx]]
      have hn0 : 0 < idx i := by linarith
      field_simp; nlinarith
    linarith
  filter_upwards [eventually_ge_atTop N] with i hi
  have hgo : ∀ j ≥ i, f i-(1/128)*rate i ≤ f j-(1/128)*rate j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact ih.trans (hmono k (hi.trans hk))
  have hlim : Tendsto (fun j => f j-(1/128)*rate j) atTop (𝓝 0) := by
    simpa only [mul_zero,sub_zero] using hf.sub (rate_tendsto.const_mul (1/128:ℝ))
  have h0 := ge_of_tendsto hlim (eventually_atTop.2 ⟨i,hgo⟩)
  linarith

private def tube (a : ℝ) (k : ℕ) : Prop :=
  (1/16 ≤ idx k*u a k ∧ idx k*u a k ≤ 3/16) ∧
  (-(7/32) ≤ idx k*Y a k ∧ idx k*Y a k ≤ -(1/32))

private theorem tube_eventual {a : ℝ} (ha : 0 < a) (hh : Tendsto (z a) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, tube a k := by
  obtain ⟨heu,hey⟩ := errors_vanish ha hh
  have hleu := heu.abs.eventually_lt_const (show |(0:ℝ)| < 1/1024 by norm_num)
  have hley := hey.abs.eventually_lt_const (show |(0:ℝ)| < 1/1024 by norm_num)
  have hr0 : Tendsto (remZ a) atTop (𝓝 0) := by
    have hI : remZ a = fun k => z a k -
        ((rate k : ℝ):ℂ)*(⟨1/8, -1/(8*Real.sqrt 2)⟩ : ℂ) := by
      funext k; apply Complex.ext
      · simp [remZ,P,z,Complex.mul_re]; ring
      · simp [remZ,Q,z,Complex.mul_im]; ring
    rw [hI]
    simpa using hh.sub ((Complex.continuous_ofReal.continuousAt.tendsto.comp rate_tendsto).mul_const
      (⟨1/8,-1/(8*Real.sqrt 2)⟩ : ℂ))
  have hrad := bound_backward (by simpa using hr0.norm)
    (f := fun k => ‖remZ a k‖) (by
      filter_upwards [hleu,hley] with k hu hy
      have hn : 0 < idx k := by dsimp [idx]; positivity
      rw [abs_mul,abs_of_nonneg (sq_nonneg _)] at hu hy
      have hs := radius_step a k
      dsimp only at hs
      have hx (x : ℝ) (h : (idx k)^2*|x| < 1/1024) :
          |x| ≤ (1/1024)/(idx k)^2 :=
        (le_div_iff₀ (sq_pos_of_pos hn)).mpr (by linarith)
      have ht : (1/1024)/(idx k)^2+(1/1024)/(idx k)^2 ≤ (1/256)/(idx k)^2 := by
        field_simp; norm_num
      linarith [hx _ hu,hx _ hy])
  filter_upwards [hrad] with k hk
  have hn : 0 < idx k := by dsimp [idx]; positivity
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs' : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hp : |P a k| ≤ (1/128)*rate k := (Complex.abs_re_le_norm (remZ a k)).trans hk
  have hq : |Q a k/Real.sqrt 2| ≤ (1/128)*rate k := (Complex.abs_im_le_norm (remZ a k)).trans hk
  rw [abs_div,abs_of_pos hs,div_le_iff₀ hs] at hq
  have hq' : |Q a k| ≤ ((1/128)*rate k)*2 :=
    hq.trans (mul_le_mul_of_nonneg_left hs' (by dsimp [rate]; positivity))
  obtain ⟨hp1,hp2⟩ := abs_le.mp hp
  obtain ⟨hq1,hq2⟩ := abs_le.mp hq'
  dsimp only [P,Q,rate] at hp1 hp2 hq1 hq2
  field_simp at hp1 hp2 hq1 hq2
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

set_option maxHeartbeats 4000000 in
private theorem box_lo (x p q : ℝ) (hx : 0 ≤ x)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    let n := x+1
    let M := 32*n*(n+1)
    let B := n*(-7+6*q)-2*(1+2*p)
    let T := (2*n-1/2)*M+B
    let E := T+M
    let A := (3*n+3/2)*32*(n+1)+2*(1+2*p)-7+6*q
    let N := n*A*T^2 - (M*(3*n-3/2)+B)*E^2
    0 ≤ N - 2*(n+1)*E^2 := by
  have hpc : 0 ≤ 1-p := by linarith
  have hqc : 0 ≤ 1-q := by linarith
  let certificate := (67136*(1-p)^3*(1-q)^2 + 173440*(1-p)^3*q*(1-q) + 108608*(1-p)^3*q^2 + 235848*p*(1-p)^2*(1-q)^2 + 594480*p*(1-p)^2*q*(1-q) + 365832*p*(1-p)^2*q^2 + 265744*p^2*(1-p)*(1-q)^2 + 659168*p^2*(1-p)*q*(1-q) + 400912*p^2*(1-p)*q^2 + 97160*p^3*(1-q)^2 + 238384*p^3*q*(1-q) + 143816*p^3*q^2) + (266208*(1-p)^3*(1-q)^2 + 746304*(1-p)^3*q*(1-q) + 488160*(1-p)^3*q^2 + 1081300*p*(1-p)^2*(1-q)^2 + 2834552*p*(1-p)^2*q*(1-q) + 1778164*p*(1-p)^2*q^2 + 1345768*p^2*(1-p)*(1-q)^2 + 3393200*p^2*(1-p)*q*(1-q) + 2073064*p^2*(1-p)*q^2 + 530740*p^3*(1-q)^2 + 1305080*p^3*q*(1-q) + 783124*p^3*q^2)*x^1 + (421920*(1-p)^3*(1-q)^2 + 1310400*(1-p)^3*q*(1-q) + 898848*(1-p)^3*q^2 + 2151520*p*(1-p)^2*(1-q)^2 + 5761952*p*(1-p)^2*q*(1-q) + 3642112*p*(1-p)^2*q^2 + 3013952*p^2*(1-p)*(1-q)^2 + 7545856*p^2*(1-p)*q*(1-q) + 4564160*p^2*(1-p)*q^2 + 1284352*p^3*(1-q)^2 + 3094304*p^3*q*(1-q) + 1820896*p^3*q^2)*x^2 + (337952*(1-p)^3*(1-q)^2 + 1197760*(1-p)^3*q*(1-q) + 865568*(1-p)^3*q^2 + 2415140*p*(1-p)^2*(1-q)^2 + 6447736*p*(1-p)^2*q*(1-q) + 4050020*p*(1-p)^2*q^2 + 3804648*p^2*(1-p)*(1-q)^2 + 9278640*p^2*(1-p)*q*(1-q) + 5491560*p^2*(1-p)*q^2 + 1727460*p^3*(1-q)^2 + 4028664*p^3*q*(1-q) + 2307108*p^3*q^2)*x^3 + (141728*(1-p)^3*(1-q)^2 + 599488*(1-p)^3*q*(1-q) + 458912*(1-p)^3*q^2 + 1653344*p*(1-p)^2*(1-q)^2 + 4275520*p*(1-p)^2*q*(1-q) + 2625632*p*(1-p)^2*q^2 + 2879456*p^2*(1-p)*(1-q)^2 + 6748480*p^2*(1-p)*q*(1-q) + 3872480*p^2*(1-p)*q^2 + 1367840*p^3*(1-q)^2 + 3072448*p^3*q*(1-q) + 1705760*p^3*q^2)*x^4 + (28672*(1-p)^3*(1-q)^2 + 155648*(1-p)^3*q*(1-q) + 126976*(1-p)^3*q^2 + 689664*p*(1-p)^2*(1-q)^2 + 1677312*p*(1-p)^2*q*(1-q) + 987648*p*(1-p)^2*q^2 + 1293312*p^2*(1-p)*(1-q)^2 + 2887680*p^2*(1-p)*q*(1-q) + 1594368*p^2*(1-p)*q^2 + 632320*p^3*(1-q)^2 + 1366016*p^3*q*(1-q) + 733696*p^3*q^2)*x^5 + (2048*(1-p)^3*(1-q)^2 + 16384*(1-p)^3*q*(1-q) + 14336*(1-p)^3*q^2 + 161792*p*(1-p)^2*(1-q)^2 + 360448*p*(1-p)^2*q*(1-q) + 198656*p*(1-p)^2*q^2 + 317440*p^2*(1-p)*(1-q)^2 + 671744*p^2*(1-p)*q*(1-q) + 354304*p^2*(1-p)*q^2 + 157696*p^3*(1-q)^2 + 327680*p^3*q*(1-q) + 169984*p^3*q^2)*x^6 + (16384*p*(1-p)^2*(1-q)^2 + 32768*p*(1-p)^2*q*(1-q) + 16384*p*(1-p)^2*q^2 + 32768*p^2*(1-p)*(1-q)^2 + 65536*p^2*(1-p)*q*(1-q) + 32768*p^2*(1-p)*q^2 + 16384*p^3*(1-q)^2 + 32768*p^3*q*(1-q) + 16384*p^3*q^2)*x^7
  have h : 0 ≤ certificate := by dsimp only [certificate]; positivity
  convert h using 1
  dsimp only [certificate]
  ring

set_option maxHeartbeats 4000000 in
private theorem box_hi (x p q : ℝ) (hx : 0 ≤ x)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    let n := x+1
    let M := 32*n*(n+1)
    let B := n*(-7+6*q)-2*(1+2*p)
    let T := (2*n-1/2)*M+B
    let E := T+M
    let A := (3*n+3/2)*32*(n+1)+2*(1+2*p)-7+6*q
    let N := n*A*T^2 - (M*(3*n-3/2)+B)*E^2
    0 ≤ 6*(n+1)*E^2 - N := by
  have hpc : 0 ≤ 1-p := by linarith
  have hqc : 0 ≤ 1-q := by linarith
  let certificate := (115272*(1-p)^3*(1-q)^2 + 205872*(1-p)^3*q*(1-q) + 88584*(1-p)^3*q^2 + 301712*p*(1-p)^2*(1-q)^2 + 523744*p*(1-p)^2*q*(1-q) + 215696*p*(1-p)^2*q^2 + 262280*p^2*(1-p)*(1-q)^2 + 439600*p^2*(1-p)*q*(1-q) + 170696*p^2*(1-p)*q^2 + 75712*p^3*(1-q)^2 + 121472*p^3*q*(1-q) + 43456*p^3*q^2) + (697172*(1-p)^3*(1-q)^2 + 1236856*(1-p)^3*q*(1-q) + 532340*(1-p)^3*q^2 + 1780904*p*(1-p)^2*(1-q)^2 + 3058480*p*(1-p)^2*q*(1-q) + 1254824*p*(1-p)^2*q^2 + 1488564*p^2*(1-p)*(1-q)^2 + 2443512*p^2*(1-p)*q*(1-q) + 931476*p^2*(1-p)*q^2 + 404768*p^3*(1-q)^2 + 621760*p^3*q*(1-q) + 208928*p^3*q^2)*x^1 + (1713888*(1-p)^3*(1-q)^2 + 3046560*(1-p)^3*q*(1-q) + 1322880*(1-p)^3*q^2 + 4226944*p*(1-p)^2*(1-q)^2 + 7250816*p*(1-p)^2*q*(1-q) + 2993920*p*(1-p)^2*q^2 + 3335552*p^2*(1-p)*(1-q)^2 + 5408800*p^2*(1-p)*q*(1-q) + 2042720*p^2*(1-p)*q^2 + 822496*p^3*(1-q)^2 + 1204544*p^3*q*(1-q) + 371680*p^3*q^2)*x^2 + (2237604*(1-p)^3*(1-q)^2 + 4015992*(1-p)^3*q*(1-q) + 1772772*(1-p)^3*q^2 + 5298728*p*(1-p)^2*(1-q)^2 + 9167920*p*(1-p)^2*q*(1-q) + 3852200*p*(1-p)^2*q^2 + 3896420*p^2*(1-p)*(1-q)^2 + 6311416*p^2*(1-p)*q*(1-q) + 2397860*p^2*(1-p)*q^2 + 835296*p^3*(1-q)^2 + 1159488*p^3*q*(1-q) + 318432*p^3*q^2)*x^3 + (1682656*(1-p)^3*(1-q)^2 + 3071552*(1-p)^3*q*(1-q) + 1387744*(1-p)^3*q^2 + 3817760*p*(1-p)^2*(1-q)^2 + 6733504*p*(1-p)^2*q*(1-q) + 2912288*p*(1-p)^2*q^2 + 2589600*p^2*(1-p)*(1-q)^2 + 4256448*p^2*(1-p)*q*(1-q) + 1663392*p^2*(1-p)*q^2 + 454496*p^3*(1-q)^2 + 594496*p^3*q*(1-q) + 138848*p^3*q^2)*x^4 + (730624*(1-p)^3*(1-q)^2 + 1366016*(1-p)^3*q*(1-q) + 635392*(1-p)^3*q^2 + 1588224*p*(1-p)^2*(1-q)^2 + 2887680*p*(1-p)^2*q*(1-q) + 1299456*p*(1-p)^2*q^2 + 984576*p^2*(1-p)*(1-q)^2 + 1677312*p^2*(1-p)*q*(1-q) + 692736*p^2*(1-p)*q^2 + 126976*p^3*(1-q)^2 + 155648*p^3*q*(1-q) + 28672*p^3*q^2)*x^5 + (169984*(1-p)^3*(1-q)^2 + 327680*(1-p)^3*q*(1-q) + 157696*(1-p)^3*q^2 + 354304*p*(1-p)^2*(1-q)^2 + 671744*p*(1-p)^2*q*(1-q) + 317440*p*(1-p)^2*q^2 + 198656*p^2*(1-p)*(1-q)^2 + 360448*p^2*(1-p)*q*(1-q) + 161792*p^2*(1-p)*q^2 + 14336*p^3*(1-q)^2 + 16384*p^3*q*(1-q) + 2048*p^3*q^2)*x^6 + (16384*(1-p)^3*(1-q)^2 + 32768*(1-p)^3*q*(1-q) + 16384*(1-p)^3*q^2 + 32768*p*(1-p)^2*(1-q)^2 + 65536*p*(1-p)^2*q*(1-q) + 32768*p*(1-p)^2*q^2 + 16384*p^2*(1-p)*(1-q)^2 + 32768*p^2*(1-p)*q*(1-q) + 16384*p^2*(1-p)*q^2)*x^7
  have h : 0 ≤ certificate := by dsimp only [certificate]; positivity
  convert h using 1
  dsimp only [certificate]
  ring

private theorem inverse_step {a : ℝ} (ha : 0 < a) (k : ℕ) :
    let n := idx k
    let x := u a (k+1)
    let w := Y a (k+1)
    let y := Y a k
    let t := 2*n+y-1/2
    y = w-x/n ∧ u a k = (x+w+3*n+3/2)*(t/(t+1))^2-3*n+3/2-y := by
  dsimp only
  let n := idx k
  let A := (state a k).1
  let S := (state a k).2
  let t := 2*n+Y a k-1/2
  have hn : 0 < n := by dsimp [n,idx]; positivity
  have hA : 0 < A := (state_pos ha k).1
  have hS : 0 < S := (state_pos ha k).2
  have ht : t=A*S/n := by dsimp [t,Y,n,A,S]; ring
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨hu1,hy1⟩ := centered_step ha k
  constructor
  · rw [hu1,hy1]
    change _ = _ - _/n
    dsimp only [n] at *
    have hpos : 0 < idx k+1 := by positivity
    field_simp; ring
  · have hi : (state a (k+1)).1 = A+n/S := rfl
    have ht1 : t+1 ≠ 0 := by positivity
    have hprev : A = (A+n/S)*(t/(t+1)) := by
      rw [← mul_div_assoc]; apply (eq_div_iff ht1).mpr
      rw [ht]; field_simp
    have hsq : A^2=(state a (k+1)).1^2*(t/(t+1))^2 := by
      rw [hi,← mul_pow]; exact congrArg (·^2) hprev
    change u a k = _*(t/(t+1))^2-3*n+3/2-Y a k
    have hn1 : idx (k+1) = n+1 := by simp [n,idx]
    rw [show u a (k+1)+Y a (k+1)+3*n+3/2 = (state a (k+1)).1^2 by
      dsimp only [u,D]; rw [hn1]; ring, ← hsq]
    dsimp [u,D,A,n]

set_option maxHeartbeats 1000000 in
private theorem backward_box {n x w y v : ℝ} (hn : 1 ≤ n)
    (hx : 1/16 ≤ (n+1)*x ∧ (n+1)*x ≤ 3/16)
    (hw : -(7/32) ≤ (n+1)*w ∧ (n+1)*w ≤ -(1/32))
    (hy : y=w-x/n)
    (hv : v=(x+w+3*n+3/2)*((2*n+y-1/2)/(2*n+y-1/2+1))^2-3*n+3/2-y) :
    (1/16 ≤ n*v ∧ n*v ≤ 3/16) ∧ (-(7/32) ≤ n*y ∧ n*y ≤ -(1/32)) := by
  let p := (16*((n+1)*x)-1)/2
  let q := (32*((n+1)*w)+7)/6
  have hp : 0 ≤ p := by dsimp [p]; linarith [hx.1]
  have hp1 : p ≤ 1 := by dsimp [p]; linarith [hx.2]
  have hq : 0 ≤ q := by dsimp [q]; linarith [hw.1]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [hw.2]
  let M := 32*n*(n+1)
  let B := n*(-7+6*q)-2*(1+2*p)
  let T := (2*n-1/2)*M+B
  let E := T+M
  let A := (3*n+3/2)*32*(n+1)+2*(1+2*p)-7+6*q
  let N := n*A*T^2-(M*(3*n-3/2)+B)*E^2
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n+1 := by linarith
  have hy' : y*M=B := by rw [hy]; dsimp [M,B,p,q]; field_simp; ring
  have ht : (2*n+y-1/2)*M=T := by dsimp only [T]; linarith [hy',show
      (2*n+y-1/2)*M=(2*n-1/2)*M+y*M by ring]
  have heat : (2*n+y-1/2+1)*M=E := by dsimp only [E]; linarith [ht,show
      (2*n+y-1/2+1)*M=(2*n+y-1/2)*M+M by ring]
  have ha' : (x+w+3*n+3/2)*(32*(n+1))=A := by dsimp [A,p,q]; ring
  have hys : (n+1)*(n*y)=n*((n+1)*w)-(n+1)*x := by rw [hy]; field_simp
  have hylo : -(7/32) ≤ n*y := by
    nlinarith [mul_le_mul_of_nonneg_left hw.1 hn0.le,hx.2,hys]
  have hyhi : n*y ≤ -(1/32) := by
    nlinarith [mul_le_mul_of_nonneg_left hw.2 hn0.le,hx.1,hys]
  have ht0 : 0 < 2*n+y-1/2+1 := by
    by_contra! hn'
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hn0.le hn',mul_nonneg hn0.le (sub_nonneg.mpr hn)]
  have hm : 0 < M := by dsimp [M]; positivity
  have he : 0 < E := by rw [← heat]; positivity
  have hrat : (2*n+y-1/2)/(2*n+y-1/2+1) = T/E := by
    rw [← ht,← heat]; field_simp
  have heq : n*v*(32*(n+1)*E^2)=N := by
    rw [hv,hrat]; dsimp only [N]
    calc
      _ = n*((x+w+3*n+3/2)*(32*(n+1)))*T^2 -
          ((32*n*(n+1))*(3*n-3/2) + y*(32*n*(n+1)))*E^2 := by field_simp; ring
      _ = _ := by rw [ha']; dsimp only [M] at hy' ⊢; rw [hy']
  have lo := box_lo (n-1) p q (by linarith) hp hp1 hq hq1
  have hi := box_hi (n-1) p q (by linarith) hp hp1 hq hq1
  dsimp only at lo hi
  simp only [sub_add_cancel] at lo hi
  change 0 ≤ N-2*(n+1)*E^2 at lo
  change 0 ≤ 6*(n+1)*E^2-N at hi
  have hpos : 0 < 32*(n+1)*E^2 := by positivity
  refine ⟨⟨?_,?_⟩,hylo,hyhi⟩
  · apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [heq,lo]
  · apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [heq,hi]

end MO429627Nonzero

open OMA.S_mo_429627 OMA.R_mo_429627_R1 MO429627Nonzero Filter Topology in
private theorem nonzero_conclusion : OMA.R_mo_429627_R1.H3 := by
  intro a ha hh
  obtain ⟨N,hN⟩ := eventually_atTop.1 (tube_eventual ha hh)
  have hback (k : ℕ) (h : tube a (k+1)) : tube a k := by
    have hn : 1 ≤ idx k := by dsimp [idx]; exact le_add_of_nonneg_left (by positivity)
    obtain ⟨hy,hu⟩ := inverse_step ha k
    obtain ⟨h1,h2⟩ := h
    rw [show idx (k+1)=idx k+1 by simp [idx]] at h1 h2
    exact backward_box hn h1 h2 hy hu
  have hall : ∀ k, tube a k → tube a 0 := by
    intro k; induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (hback k h)
  have hzero := (hall N (hN N le_rfl)).1.1
  norm_num [idx,u,D,Y,state] at hzero
  nlinarith

namespace MO429627Leading
open OMA.S_mo_429627 OMA.R_mo_429627_R1 Filter Topology

private theorem npos (k : ℕ) : 0 < idx k := by dsimp [idx]; positivity
private theorem next_idx (k : ℕ) : idx (k+1)=idx k+1 := by simp [idx]
private theorem idx_inf : Tendsto idx atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))

private theorem eventual_upper {f : ℕ → ℝ} (hd : ∀ᶠ k in atTop, f (k+1) ≤ f k) :
    ∃ B, ∀ᶠ k in atTop, f k ≤ B := by
  obtain ⟨m,hm⟩ := eventually_atTop.1 hd
  refine ⟨f m,eventually_atTop.2 ⟨m,?_⟩⟩
  intro k hk; induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (hm k hk).trans ih

private theorem affine_upper {f : ℕ → ℝ}
    (hd : ∀ᶠ k in atTop, f (k+2)-2*f (k+1)+f k ≤ 0) :
    ∃ A B : ℝ, ∀ᶠ k in atTop, f k ≤ A+B*idx k := by
  obtain ⟨B,hB⟩ := eventual_upper (f := fun k => f (k+1)-f k)
    (hd.mono fun k h => by linarith)
  obtain ⟨A,hA⟩ := eventual_upper (f := fun k => f k-B*idx k)
    (hB.mono fun k h => by rw [next_idx]; linarith)
  exact ⟨A,B,hA.mono fun k h => by linarith⟩

private theorem cubic_upper {f : ℕ → ℝ} {c b : ℝ} (hcb : c < b)
    (hd : ∀ᶠ k in atTop, f (k+2)-2*f (k+1)+f k ≤ 6*c*(idx k+1)) :
    ∀ᶠ k in atTop, f k ≤ b*(idx k)^3 := by
  obtain ⟨A,B,hAB⟩ := affine_upper (f := fun k => f k-c*(idx k)^3) (by
    filter_upwards [hd] with k hk
    try dsimp only
    rw [show idx (k+2)=idx k+1+1 by rw [next_idx (k+1),next_idx],next_idx]
    linarith)
  have hlim : Tendsto (fun k => A/(idx k)^3+B/(idx k)^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := A)).div_atTop (tendsto_pow_atTop (α:=ℝ) (by decide : 3 ≠ 0) |>.comp idx_inf) |>.add
      ((tendsto_const_nhds (x := B)).div_atTop (tendsto_pow_atTop (α:=ℝ) (by decide : 2 ≠ 0) |>.comp idx_inf))
  filter_upwards [hAB,hlim.eventually_lt_const (show 0 < b-c by linarith)] with k hk h
  have hn := npos k
  have hsmall : A+B*idx k < (b-c)*(idx k)^3 := by
    apply (div_lt_iff₀ (pow_pos hn 3)).mp
    convert h using 1; field_simp
  linarith

private noncomputable def aTerm (a : ℝ) (k : ℕ) := (state a k).1
private noncomputable def total (a : ℝ) (k : ℕ) := (state a k).2

private theorem diff2 {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (total a (k+2))^2-2*(total a (k+1))^2+(total a k)^2 =
      2*(idx k+1)+(aTerm a (k+1))^2+(aTerm a (k+2))^2 := by
  let p := aTerm a (k+1)
  let q := aTerm a (k+2)
  let s := total a (k+1)
  have hs : 0 < s := (state_pos ha (k+1)).2
  have hq : q=p+(idx k+1)/s := by dsimp only [p,q,s,aTerm,total,state]; simp [idx]
  have hw : total a (k+2)=s+q := rfl
  have hv : total a k=s-p := by dsimp only [s,p,total,aTerm,state]; ring
  change _-2*s^2+_ = _ + p^2+q^2
  rw [hw,hv,hq]; field_simp; ring

private theorem cubic_pair {a : ℝ} (ha : 0 < a) {c : ℝ} {sg : ℝ} (_hsg : sg=1 ∨ sg= -1)
    (hb : ∀ᶠ k in atTop, sg*(aTerm a k)^2 ≤ c*idx k)
    {b : ℝ} (hc : (sg+c)/3 < b) :
    ∀ᶠ k in atTop, sg*(total a k)^2 ≤ b*(idx k)^3 := by
  let m := ((sg+c)/3+b)/2
  apply cubic_upper (c := m) (by dsimp [m]; linarith)
  have hc' : 0 < 6*m-2*(sg+c) := by dsimp [m]; linarith
  have hlarge : ∀ᶠ k in atTop, c ≤ (6*m-2*(sg+c))*(idx k+1) := by
    filter_upwards [idx_inf.eventually_ge_atTop (c/(6*m-2*(sg+c)))] with k hk
    have h := (div_le_iff₀ hc').mp hk
    linarith
  have h1 := (tendsto_add_atTop_nat 1).eventually hb
  have h2 := (tendsto_add_atTop_nat 2).eventually hb
  filter_upwards [h1,h2,hlarge] with k h1 h2 hlarge
  try dsimp only
  change sg*(aTerm a (k+1))^2 ≤ c*idx (k+1) at h1
  change sg*(aTerm a (k+2))^2 ≤ c*idx (k+2) at h2
  rw [next_idx] at h1
  rw [next_idx (k+1),next_idx] at h2
  have h := congrArg (sg*·) (diff2 ha k)
  linarith

private theorem sqrt_inf : Tendsto (fun k => Real.sqrt (idx k)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp idx_inf

private theorem root_upper {f : ℕ → ℝ} {c b : ℝ} (hc : c < b)
    (hd : ∀ᶠ k in atTop, f (k+1)-f k ≤ c*(Real.sqrt (idx (k+1))-Real.sqrt (idx k))) :
    ∀ᶠ k in atTop, f k ≤ b*Real.sqrt (idx k) := by
  obtain ⟨A,hA⟩ := eventual_upper (f := fun k => f k-c*Real.sqrt (idx k))
    (hd.mono fun k h => by linarith)
  filter_upwards [hA,sqrt_inf.eventually_ge_atTop (A/(b-c))] with k hk h
  have h' := (div_le_iff₀ (show 0 < b-c by linarith)).mp h
  linarith

private noncomputable def shape (k : ℕ) := (Real.sqrt (1+1/idx k)+1)^2
private noncomputable def slope (a : ℝ) (k : ℕ) :=
  (idx k/total a k)*(Real.sqrt (idx (k+1))+Real.sqrt (idx k))
private noncomputable def density (a : ℝ) (k : ℕ) := (total a k)^2/(idx k)^3

private theorem shape_limit : Tendsto shape atTop (𝓝 4) := by
  have h : Tendsto (fun k => 1/idx k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop idx_inf
  have h' := (Real.continuous_sqrt.continuousAt.tendsto.comp (h.const_add 1)).add_const 1 |>.pow 2
  unfold shape; convert h' using 1 <;> norm_num [Function.comp_def]

private theorem slope_info {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < slope a k ∧
    (slope a k)^2 * density a k = shape k ∧
    aTerm a (k+1)-aTerm a k =
      slope a k*(Real.sqrt (idx (k+1))-Real.sqrt (idx k)) := by
  have hn := npos k
  have hn' := npos (k+1)
  have hs : 0 < total a k := (state_pos ha k).2
  have h1 := Real.sq_sqrt hn.le
  have h2 := Real.sq_sqrt hn'.le
  have hid := next_idx k
  have hprod : Real.sqrt (1+1/idx k) = Real.sqrt (idx (k+1))/Real.sqrt (idx k) := by
    rw [← Real.sqrt_div hn'.le]
    congr 1; rw [next_idx]; field_simp
  have hd : aTerm a (k+1)-aTerm a k=idx k/total a k := by dsimp [aTerm,total,state,idx]; ring
  refine ⟨by unfold slope; positivity, ?_, ?_⟩
  · unfold slope density shape
    rw [hprod]
    have hsr : Real.sqrt (idx k) ≠ 0 := by positivity
    field_simp
    ring_nf
    simp only [h1]
  · rw [hd]; unfold slope
    have h : (Real.sqrt (idx (k+1))+Real.sqrt (idx k))*(Real.sqrt (idx (k+1))-Real.sqrt (idx k))=1 := by
      nlinarith
    rw [mul_assoc,h,mul_one]

private theorem upper_root {a l c b : ℝ} (ha : 0 < a) (hl : 0 < l) (hc : 0 < c)
    (hb : c < b) (hgap : 4 < c^2*l)
    (hd : ∀ᶠ k in atTop, l ≤ density a k) :
    ∀ᶠ k in atTop, aTerm a k ≤ b*Real.sqrt (idx k) := by
  apply root_upper hb
  filter_upwards [hd,shape_limit.eventually_lt_const hgap] with k hk h
  obtain ⟨hs,he,hdiff⟩ := slope_info ha k
  have hslt : slope a k ≤ c := by
    by_contra! h'
    have ineq := mul_le_mul (pow_le_pow_left₀ hc.le h'.le 2) hk hl.le (sq_nonneg _)
    linarith
  rw [hdiff]
  apply mul_le_mul_of_nonneg_right hslt
  exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by rw [next_idx]; linarith))

private theorem lower_root {a l c b : ℝ} (ha : 0 < a) (_hl : 0 < l) (_hc : 0 < c)
    (hb : b < c) (hgap : c^2*l < 4)
    (hd : ∀ᶠ k in atTop, density a k ≤ l) :
    ∀ᶠ k in atTop, b*Real.sqrt (idx k) ≤ aTerm a k := by
  have he : ∀ᶠ k in atTop, -aTerm a (k+1)-(-aTerm a k) ≤
      -c*(Real.sqrt (idx (k+1))-Real.sqrt (idx k)) := by
    filter_upwards [hd,shape_limit.eventually_const_lt hgap] with k hk h
    obtain ⟨hs,he,hdiff⟩ := slope_info ha k
    have hd0 : 0 ≤ density a k := by dsimp [density]; have := npos k; positivity
    have hslt : c ≤ slope a k := by
      by_contra! h'
      have ineq := mul_le_mul (pow_le_pow_left₀ hs.le h'.le 2) hk hd0 (sq_nonneg _)
      linarith
    have hdiff0 : 0 ≤ Real.sqrt (idx (k+1))-Real.sqrt (idx k) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by rw [next_idx]; linarith))
    linarith [mul_le_mul_of_nonneg_right hslt hdiff0]
  exact (root_upper (f:=fun k => -aTerm a k) (b := -b) (by linarith) he).mono
    fun k h => by linarith

private def bracket (a l r : ℝ) : Prop := ∀ᶠ k in atTop,
  l*Real.sqrt (idx k) ≤ aTerm a k ∧ aTerm a k ≤ r*Real.sqrt (idx k)

private theorem upper_density {a r d : ℝ} (ha : 0 < a) (_hr : 0 ≤ r)
    (h : ∀ᶠ k in atTop, aTerm a k ≤ r*Real.sqrt (idx k)) (hd : (1+r^2)/3 < d) :
    ∀ᶠ k in atTop, density a k ≤ d := by
  have hb : ∀ᶠ k in atTop, 1*(aTerm a k)^2 ≤ r^2*idx k := by
    filter_upwards [h] with k hk
    have ht : 0 ≤ aTerm a k := (state_pos ha k).1.le
    simpa [mul_pow, Real.sq_sqrt (npos k).le] using pow_le_pow_left₀ ht hk 2
  filter_upwards [cubic_pair ha (Or.inl rfl) hb hd] with k hk
  exact (div_le_iff₀ (pow_pos (npos k) 3)).mpr (by simpa using hk)

private theorem lower_density {a l d : ℝ} (ha : 0 < a) (hl : 0 ≤ l)
    (h : ∀ᶠ k in atTop, l*Real.sqrt (idx k) ≤ aTerm a k) (hd : d < (1+l^2)/3) :
    ∀ᶠ k in atTop, d ≤ density a k := by
  have hb : ∀ᶠ k in atTop, (-1)*(aTerm a k)^2 ≤ (-l^2)*idx k := by
    filter_upwards [h] with k hk
    have he := pow_le_pow_left₀ (mul_nonneg hl (Real.sqrt_nonneg _)) hk 2
    rw [mul_pow, Real.sq_sqrt (npos k).le] at he
    linarith
  filter_upwards [cubic_pair (a:=a) (c := -l^2) (b := -d) ha (Or.inr rfl) hb (by linarith)] with k hk
  exact (le_div_iff₀ (pow_pos (npos k) 3)).mpr (by linarith)

private theorem update {a l u L U c d p q : ℝ} (ha : 0 < a) (hb : bracket a l u)
    (hl : 0 ≤ l) (hu : 0 ≤ u) (hc : 0 < c) (hd : 0 < d)
    (hp : 0 < p) (hq : 0 < q) (hL : L < c) (hU : d < U)
    (hps : p < (1+l^2)/3) (hqs : (1+u^2)/3 < q)
    (hcq : c^2*q < 4) (hdp : 4 < d^2*p) : bracket a L U :=
  (lower_root ha hq hc hL hcq (upper_density ha hu (hb.mono fun _ h => h.2) hqs)).and
    (upper_root ha hp hd hU hdp (lower_density ha hl (hb.mono fun _ h => h.1) hps))

set_option maxHeartbeats 3200000 in
private theorem narrow {a : ℝ} (ha : 0 < a) : bracket a (173205/100000) (173206/100000) := by
  have h0 : ∀ᶠ k in atTop, (0:ℝ)*Real.sqrt (idx k) ≤ aTerm a k := Eventually.of_forall fun k => by
    simpa [aTerm] using (state_pos ha k).1.le
  have hb : bracket a 0 5 :=
    h0.and (upper_root ha (l:=3/10) (c:=4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (lower_density ha (by norm_num) h0 (by norm_num)))

  have hb : bracket a (3396831/5000000) (346410171/100000000) := update (p:=(8333333/25000000)) (q:=(866666667/100000000)) (c:=(67936621/100000000)) (d:=(34641017/10000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (96076887/100000000) (28654017/10000000) := update (p:=(24358973/50000000)) (q:=(108333339/25000000)) (c:=(12009611/12500000)) (d:=(286540169/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (57071381/50000000) (62449983/25000000) := update (p:=(64102559/100000000)) (q:=(76754391/25000000)) (c:=(114142763/100000000)) (d:=(249799931/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (25748463/20000000) (114137183/50000000) := update (p:=(76761899/100000000)) (q:=(120666677/50000000)) (c:=(32185579/25000000)) (d:=(45654873/20000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (69499663/50000000) (13281203/6250000) := update (p:=(11072743/12500000)) (q:=(207030621/100000000)) (c:=(138999327/100000000)) (d:=(212499247/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (29500169/20000000) (202303143/100000000) := update (p:=(97736041/100000000)) (q:=(91926551/50000000)) (c:=(73750423/50000000)) (d:=(101151571/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (30700711/20000000) (9719509/5000000) := update (p:=(26463749/25000000)) (q:=(84877603/50000000)) (c:=(38375889/25000000)) (d:=(194390179/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (158464969/100000000) (189085417/100000000) := update (p:=(111877803/100000000)) (q:=(159291807/100000000)) (c:=(15846497/10000000)) (d:=(23635677/12500000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (161949431/100000000) (92435359/50000000) := update (p:=(117037153/100000000)) (q:=(19063873/12500000)) (c:=(20243679/12500000)) (d:=(184870717/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (32962611/20000000) (181999729/100000000) := update (p:=(60379363/50000000)) (q:=(5890291/4000000)) (c:=(643801/390625)) (d:=(11374983/6250000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (83406827/50000000) (179693863/100000000) := update (p:=(123877809/100000000)) (q:=(71873169/50000000)) (c:=(33362731/20000000)) (d:=(89846931/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (42112631/25000000) (178111047/100000000) := update (p:=(31522329/25000000)) (q:=(70483141/50000000)) (c:=(6738021/4000000)) (d:=(89055523/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (21198739/12500000) (88416469/50000000) := update (p:=(25583719/20000000)) (q:=(34769621/25000000)) (c:=(169589913/100000000)) (d:=(176832937/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (170519469/100000000) (43988041/25000000) := update (p:=(129202459/100000000)) (q:=(68783147/50000000)) (c:=(17051947/10000000)) (d:=(175952163/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (171165043/100000000) (175238949/100000000) := update (p:=(16282037/12500000)) (q:=(136530547/100000000)) (c:=(42791261/25000000)) (d:=(43809737/25000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (171690813/100000000) (34949287/20000000) := update (p:=(32747893/25000000)) (q:=(135695631/100000000)) (c:=(85845407/50000000)) (d:=(87373217/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86027733/50000000) (34869403/20000000) := update (p:=(131592449/100000000)) (q:=(4222533/3125000)) (c:=(172055467/100000000)) (d:=(87173507/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86176073/50000000) (174070883/100000000) := update (p:=(33002569/25000000)) (q:=(134656273/100000000)) (c:=(172352147/100000000)) (d:=(87035441/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (690231/400000) (86923379/50000000) := update (p:=(132350873/100000000)) (q:=(5373423/4000000)) (c:=(172557751/100000000)) (d:=(173846757/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (172724933/100000000) (173691719/100000000) := update (p:=(26517451/20000000)) (q:=(134075651/100000000)) (c:=(86362467/50000000)) (d:=(86845859/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (172840739/100000000) (8678291/5000000) := update (p:=(132779673/100000000)) (q:=(26779209/20000000)) (c:=(8642037/5000000)) (d:=(173565819/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (43233719/25000000) (1734787/1000000) := update (p:=(132913069/100000000)) (q:=(133750313/100000000)) (c:=(172934877/100000000)) (d:=(173478699/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86500033/50000000) (34681587/20000000) := update (p:=(13302157/10000000)) (q:=(33412383/25000000)) (c:=(173000067/100000000)) (d:=(86703967/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (21631631/12500000) (173358959/100000000) := update (p:=(133096741/100000000)) (q:=(133567707/100000000)) (c:=(173053049/100000000)) (d:=(86679479/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173089733/100000000) (173319171/100000000) := update (p:=(133157857/100000000)) (q:=(16688887/12500000)) (c:=(86544867/50000000)) (d:=(17331917/10000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86559773/50000000) (173291631/100000000) := update (p:=(16650023/12500000)) (q:=(133465117/100000000)) (c:=(173119547/100000000)) (d:=(17329163/10000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86570093/50000000) (34653851/20000000) := update (p:=(133234589/100000000)) (q:=(66716649/50000000)) (c:=(173140187/100000000)) (d:=(86634627/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86578479/50000000) (173253767/100000000) := update (p:=(33314603/25000000)) (q:=(2668149/2000000)) (c:=(173156959/100000000)) (d:=(86626883/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (17316857/10000000) (173241183/100000000) := update (p:=(33319443/25000000)) (q:=(3334739/2500000)) (c:=(173168571/100000000)) (d:=(86620591/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (34635601/20000000) (173232471/100000000) := update (p:=(133291177/100000000)) (q:=(5335001/4000000)) (c:=(86589003/50000000)) (d:=(17323247/10000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173184537/100000000) (173225393/100000000) := update (p:=(13330207/10000000)) (q:=(33341241/25000000)) (c:=(86592269/50000000)) (d:=(10826587/6250000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (34637969/20000000) (173220493/100000000) := update (p:=(133309611/100000000)) (q:=(13335679/10000000)) (c:=(86594923/50000000)) (d:=(43305123/25000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173193519/100000000) (676627/390625) := update (p:=(6665787/5000000)) (q:=(133351131/100000000)) (c:=(2164919/1250000)) (d:=(173216511/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (34639301/20000000) (43303439/25000000) := update (p:=(66659991/50000000)) (q:=(66673267/50000000)) (c:=(86598253/50000000)) (d:=(34642751/20000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (43299643/25000000) (43302879/25000000) := update (p:=(13332343/10000000)) (q:=(133343351/100000000)) (c:=(173198573/100000000)) (d:=(34642303/20000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173200251/100000000) (86604983/50000000) := update (p:=(16665727/12500000)) (q:=(26668153/20000000)) (c:=(43300063/25000000)) (d:=(34641993/20000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86600707/50000000) (173208707/100000000) := update (p:=(26665551/20000000)) (q:=(5333559/4000000)) (c:=(34640283/20000000)) (d:=(86604353/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86601179/50000000) (86603917/50000000) := update (p:=(66664549/50000000)) (q:=(133337521/100000000)) (c:=(173202359/100000000)) (d:=(173207833/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173203013/100000000) (86603563/50000000) := update (p:=(33332547/25000000)) (q:=(133336513/100000000)) (c:=(86601507/50000000)) (d:=(1385657/800000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (21650443/12500000) (34641327/20000000) := update (p:=(520824/390625)) (q:=(26667139/20000000)) (c:=(34640709/20000000)) (d:=(86603317/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (21650489/12500000) (173206237/100000000) := update (p:=(133331557/100000000)) (q:=(133335129/100000000)) (c:=(173203913/100000000)) (d:=(43301559/25000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173204211/100000000) (173205961/100000000) := update (p:=(66665991/50000000)) (q:=(133334669/100000000)) (c:=(43301053/25000000)) (d:=(4330149/2500000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86602209/50000000) (21650717/12500000) := update (p:=(16666541/12500000)) (q:=(2666687/2000000)) (c:=(173204419/100000000)) (d:=(34641147/20000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173204587/100000000) (173205581/100000000) := update (p:=(133332567/100000000)) (q:=(13333409/10000000)) (c:=(43301147/25000000)) (d:=(8660279/5000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173204703/100000000) (86602727/50000000) := update (p:=(66666381/50000000)) (q:=(133333911/100000000)) (c:=(5412647/3125000)) (d:=(173205453/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86602399/50000000) (173205367/100000000) := update (p:=(4166653/3125000)) (q:=(26666753/20000000)) (c:=(173204799/100000000)) (d:=(86602683/50000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (173204863/100000000) (173205297/100000000) := update (p:=(26666601/20000000)) (q:=(4166677/3125000)) (c:=(1353163/781250)) (d:=(10825331/6250000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (34640983/20000000) (676583/390625) := update (p:=(3333327/2500000)) (q:=(8333349/6250000)) (c:=(43301229/25000000)) (d:=(173205247/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (21650619/12500000) (173205209/100000000) := update (p:=(6666657/5000000)) (q:=(133333527/100000000)) (c:=(173204953/100000000)) (d:=(21650651/12500000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86602491/50000000) (173205181/100000000) := update (p:=(133333183/100000000)) (q:=(66666741/50000000)) (c:=(173204983/100000000)) (d:=(8660259/5000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb : bracket a (86602501/50000000) (86602579/50000000) := update (p:=(66666609/50000000)) (q:=(2666669/2000000)) (c:=(173205003/100000000)) (d:=(173205157/100000000)) ha hb  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hb] with k hk
  have hs := Real.sqrt_nonneg (idx k)
  constructor
  · exact (mul_le_mul_of_nonneg_right (by norm_num) hs).trans hk.1
  · exact hk.2.trans (mul_le_mul_of_nonneg_right (by norm_num) hs)

private theorem relatively_small {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k in atTop, 500*‖z a k‖ ≤ idx k := by
  have hb := narrow ha
  have hl := lower_density ha (l := 173205/100000) (d := 133332/100000) (by norm_num)
    (hb.mono fun _ h => h.1) (by norm_num)
  have hu := upper_density ha (r := 173206/100000) (d := 133335/100000) (by norm_num)
    (hb.mono fun _ h => h.2) (by norm_num)
  filter_upwards [hb,hl,hu,idx_inf.eventually_ge_atTop 100000] with k hb hl hu hnBig
  let n := idx k
  let A := aTerm a k
  let S := total a k
  let X := A*S/n^2
  have hn : 0 < n := npos k
  have hA : 0 < A := (state_pos ha k).1
  have hS : 0 < S := (state_pos ha k).2
  have hL : (173205/100000:ℝ)^2 ≤ A^2/n := by
    apply (le_div_iff₀ hn).mpr
    have := pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hb.1 2
    simpa [mul_pow,Real.sq_sqrt (npos k).le] using this
  have hU : A^2/n ≤ (173206/100000:ℝ)^2 := by
    apply (div_le_iff₀ hn).mpr
    have := pow_le_pow_left₀ hA.le hb.2 2
    simpa [mul_pow,Real.sq_sqrt (npos k).le] using this
  change 133332/100000 ≤ S^2/n^3 at hl
  change S^2/n^3 ≤ 133335/100000 at hu
  have hx : X^2=(A^2/n)*(S^2/n^3) := by dsimp [X]; ring
  have hx0 : 0 < X := by dsimp [X]; positivity
  have hxl : 19999/10000 ≤ X := by
    have h := mul_le_mul hL hl (by norm_num) (by positivity)
    rw [← hx] at h
    by_contra! hbad
    have := pow_le_pow_left₀ hx0.le hbad.le 2
    norm_num at h this; linarith
  have hxu : X ≤ 20001/10000 := by
    have h := mul_le_mul hU hu (by positivity) (by norm_num)
    rw [← hx] at h
    by_contra! hbad
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20001/10000) hbad.le 2
    norm_num at h this; linarith
  have hDn : D a k/n = A^2/n-3+(3/2)/n := by dsimp [D,A,aTerm,n]; field_simp
  have hYn : Y a k/n = X-2+(1/2)/n := by dsimp [Y,X,A,S,aTerm,total,n]; field_simp
  have hinv : 1/n ≤ (1/100000:ℝ) := by rw [div_le_div_iff₀ hn (by norm_num)]; linarith
  have hdinv : (3/2)/n ≤ 3/200000 := by apply (div_le_iff₀ hn).mpr; change 100000 ≤ n at hnBig; linarith
  have hyinv : (1/2)/n ≤ 1/200000 := by apply (div_le_iff₀ hn).mpr; change 100000 ≤ n at hnBig; linarith
  have hd : |D a k/n| ≤ 1/10000 := abs_le.mpr ⟨by linarith [div_nonneg (by norm_num : 0 ≤ (3:ℝ)/2) hn.le],by linarith⟩
  have hy : |Y a k/n| ≤ 2/10000 := abs_le.mpr ⟨by linarith [div_nonneg (by norm_num : 0 ≤ (1:ℝ)/2) hn.le],by linarith⟩
  rw [abs_div,abs_of_pos hn, div_le_iff₀ hn] at hd hy
  have hs : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
  have hab := Complex.norm_le_abs_re_add_abs_im (z a k)
  change ‖z a k‖ ≤ |D a k-Y a k| + |Y a k/Real.sqrt 2| at hab
  rw [abs_div,abs_of_pos (by positivity : 0 < Real.sqrt 2)] at hab
  change 500*‖z a k‖ ≤ n
  linarith [abs_sub (D a k) (Y a k), div_le_self (abs_nonneg (Y a k)) hs]

end MO429627Leading

open OMA.S_mo_429627 OMA.R_mo_429627_R1 MO429627Phase MO429627Leading Filter Topology in
private theorem bounded_conclusion : OMA.R_mo_429627_R1.H1 := by
  intro a ha
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((relatively_small ha).and
    (idx_inf.eventually_ge_atTop 1000))
  let R := 2*(‖z a N‖+1)
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg (z a N)]
  have hn0 := npos N
  have hNlarge : 108*R ≤ idx N := by dsimp [R]; linarith [(hN N le_rfl).1,(hN N le_rfl).2]
  have hmono {i j : ℕ} (h : i ≤ j) : idx i ≤ idx j := by
    dsimp [idx]; exact_mod_cast Nat.add_le_add_right h 1
  have hcap (k : ℕ) : ‖z a N‖+54*R^2*(1/idx N-1/idx k) ≤ R := by
    have h1 : 54*R^2/idx N ≤ R/2 := (div_le_iff₀ hn0).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left hNlarge (show 0 ≤ R by linarith)])
    have h2 : 0 ≤ 54*R^2/idx k := by have := npos k; positivity
    have h3 : ‖z a N‖ ≤ R/2 := by dsimp [R]; linarith
    rw [mul_sub,mul_one_div,mul_one_div]
    linarith only [h1,h2,h3]
  have hiter : ∀ k ≥ N, ‖z a k‖ ≤ ‖z a N‖+54*R^2*(1/idx N-1/idx k) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have h := step_error ha hR (k := k) (by linarith [hmono hk]) (ih.trans (hcap k))
      have hd (j : ℕ) : ‖demod a j‖ = ‖z a j‖ := by rw [demod,norm_div,phase_norm,div_one]
      have hdist := norm_sub_norm_le (demod a (k+1)) (demod a k)
      rw [hd,hd,← dist_eq_norm,dist_comm] at hdist
      have hn := npos k
      have hkn : 1 ≤ idx k := by linarith [hmono hk]
      have htail : 27*R^2/(idx k)^2 ≤ 54*R^2*(1/idx k-1/idx (k+1)) := by
        rw [next_idx]
        have hnp : 0 < idx k+1 := by positivity
        field_simp
        nlinarith only [hkn]
      linarith
  exact ⟨R,eventually_atTop.2 ⟨N,fun k hk => (hiter k hk).trans (hcap k)⟩⟩

theorem OMA.solution : type_of% @OMA.S_mo_429627.main :=
  OMA.R_mo_429627_R1.combine bounded_conclusion phase_conclusion nonzero_conclusion
