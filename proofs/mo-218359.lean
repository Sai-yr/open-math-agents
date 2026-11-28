import OMAStatements.S_mo_218359

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

theorem inside {n : ℕ} {i : ℤ} (hi : i ∈ sites n) : 0 < i ∧ i < (n:ℤ) := mem_Ioo.mp hi

theorem wpos {n : ℕ} {i : ℤ} (hi : i ∈ sites n) : 0 < weight n i := by
  obtain ⟨l,h⟩ := inside hi
  unfold weight
  have : (i:ℝ) < n := by exact_mod_cast h
  have : (0:ℝ) < i := by exact_mod_cast l
  positivity

theorem wtwo {n : ℕ} (hn : 3 ≤ n) {i : ℤ} (hi : i ∈ sites n) : 2 ≤ weight n i := by
  obtain ⟨l,h⟩ := inside hi
  have h₁ : (1:ℝ) ≤ i := by exact_mod_cast (show (1:ℤ) ≤ i by omega)
  have h₂ : (1:ℝ) ≤ (n:ℝ)-i := by exact_mod_cast (show (1:ℤ) ≤ (n:ℤ)-i by omega)
  have h₃ : (3:ℝ) ≤ n := by exact_mod_cast hn
  unfold weight
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

theorem wclosed {n : ℕ} {i : ℤ} (lo : 0 ≤ i) (hi : i ≤ (n:ℤ)) : 0 ≤ weight n i := by
  unfold weight
  exact mul_nonneg (by exact_mod_cast lo) (sub_nonneg.mpr (by exact_mod_cast hi))

theorem harmonic (n : ℕ) (i : ℤ) :
    weight n (i-1)+weight n (i+1)=2*(weight n i-1) := by unfold weight; push_cast; ring

def spike (i : ℤ) (v : ℝ) (j : ℤ) : ℝ := if j=i then v else 0

theorem spike_sum {s : Finset ℤ} {i : ℤ} (hi : i ∈ s) (v : ℝ) :
    (∑ j ∈ s, spike i v j)=v := by simp [spike,hi]

theorem wspike_sum {n : ℕ} {i : ℤ} (lo : 0 ≤ i) (hi : i ≤ (n:ℤ)) (v : ℝ) :
    (∑ j ∈ sites n, spike i (weight n i*v) j)=weight n i*v := by
  by_cases mem : i ∈ sites n
  · exact spike_sum mem _
  · have alt : i=0 ∨ i=(n:ℤ) := by
      change ¬i ∈ Ioo (0:ℤ) n at mem; simp only [mem_Ioo] at mem; omega
    rcases alt with rfl|rfl <;> simp [spike,weight]

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

private def energy (n : ℕ) (u : State) : ℝ := ∑ i ∈ sites n, weight n i*max (gap u i) 0

private theorem energy_nonneg (n : ℕ) (u : State) : 0 ≤ energy n u :=
  sum_nonneg fun _i hi => mul_nonneg (wpos hi).le (le_max_right ..)

private theorem energy_le {n : ℕ} {u : State} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ sites n, gap u i ≤ b) : energy n u ≤ totalWeight n*b := by
  unfold energy totalWeight; rw [sum_mul]
  exact sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (max_le (h j hj) hb) (wpos hj).le

private theorem energy_step {n : ℕ} {u : State} {i : ℤ} (hi : legal n u i) :
    energy n (step u i) ≤ energy n u-gap u i := by
  let g := gap u i
  have gp : 0 < g := lt_trans zero_lt_one hi.2
  obtain ⟨lo,up⟩ := inside hi.1
  have term (j : ℤ) (hj : j ∈ sites n) :
      weight n j*max (gap (step u i) j) 0 ≤ weight n j*max (gap u j) 0
      +spike (i-1) (weight n (i-1)*(g/2)) j+spike (i+1) (weight n (i+1)*(g/2)) j
      -spike i (weight n i*g) j := by
    have hinge (k : ℤ) : max (gap u k+g/2) 0 ≤ max (gap u k) 0+g/2 := by
      apply max_le <;> linarith [le_max_left (gap u k) 0,le_max_right (gap u k) 0]
    by_cases a : j=i-1
    · subst j
      have eq : gap (step u i) (i-1)=gap u (i-1)+g/2 := by
        simp [gap,step,g,show i-1-1 ≠ i-1 by omega,show i-1-1 ≠ i by omega]; ring
      simp only [eq,spike,if_true,if_neg (show i-1 ≠ i+1 by omega),if_neg (show i-1 ≠ i by omega),add_zero,sub_zero]
      rw [←mul_add]; exact mul_le_mul_of_nonneg_left (hinge _) (wpos hj).le
    by_cases b : j=i+1
    · subst j
      have eq : gap (step u i) (i+1)=gap u (i+1)+g/2 := by
        simp [gap,step,g,show i ≠ i-1 by omega,show i+1 ≠ i-1 by omega]; ring
      simp only [eq,spike,if_true,if_neg a,if_neg (show i+1 ≠ i by omega),add_zero,sub_zero]
      rw [←mul_add]; exact mul_le_mul_of_nonneg_left (hinge _) (wpos hj).le
    by_cases c : j=i
    · subst j
      have eq : gap (step u i) i=0 := by simp [gap,step,show i ≠ i-1 by omega]; ring
      simp [eq,spike,a,b,max_eq_left gp.le,g]
    · have eq : gap (step u i) j=gap u j := by
        simp [gap,step,a,c,show j-1 ≠ i-1 by omega,show j-1 ≠ i by omega]
      simp [eq,spike,a,b,c]
  have total := sum_le_sum term
  simp only [sum_sub_distrib,sum_add_distrib] at total
  rw [wspike_sum (by omega : 0 ≤ i-1) (by omega : i-1 ≤ (n:ℤ)),
      wspike_sum (by omega : 0 ≤ i+1) (by omega : i+1 ≤ (n:ℤ)),spike_sum hi.1] at total
  change energy n (step u i) ≤ energy n u+weight n (i-1)*(g/2)+weight n (i+1)*(g/2)-weight n i*g at total
  change energy n (step u i) ≤ energy n u-g
  nlinarith only [total,congrArg (fun x : ℝ => x*g) (harmonic n i)]

private def clock (D E : ℝ) := 2*D*(Real.log (D+E)-Real.log D)

private theorem clock_drop {D E E' g : ℝ} (d : 0 < D) (_e : 0 ≤ E) (e' : 0 ≤ E')
    (drop : E' ≤ E-g) (active : 1 ≤ g) (big : E ≤ D*g) :
    1+clock D E' ≤ clock D E := by
  have e₁ : 0 < D+E := by linarith
  have e₂ : 0 < D+E' := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos e₂ e₁)
  rw [Real.log_div e₂.ne' e₁.ne'] at h
  have v : Real.log (D+E')-Real.log (D+E)+1 ≤ (D+E')/(D+E) := by linarith
  have v' := (le_div_iff₀ e₁).mp v
  have scaled := mul_le_mul_of_nonneg_left v' (show 0 ≤ 2*D by positivity)
  have gd := mul_le_mul_of_nonneg_left active d.le
  have z : (1+clock D E'-clock D E)*(D+E) ≤ 0 := by
    unfold clock
    nlinarith only [scaled,gd,big,mul_le_mul_of_nonneg_left drop (show 0 ≤ 2*D by positivity)]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_left z e₁)

theorem chooseGreedy {n : ℕ} {u : State} (hs : ¬sorted n u) : ∃ i, greedy n u i := by
  classical
  change ¬∀ i ∈ sites n, gap u i ≤ 1 at hs
  push Not at hs
  obtain ⟨a,ha,active⟩ := hs
  obtain ⟨m,hm,largest⟩ := (sites n).exists_max_image (gap u) ⟨a,ha⟩
  let ties := (sites n).filter (fun j => gap u j=gap u m)
  have mem : m ∈ ties := mem_filter.mpr ⟨hm,rfl⟩
  let i := ties.min' ⟨m,mem⟩
  obtain ⟨hi,eq⟩ := mem_filter.mp (min'_mem ties ⟨m,mem⟩)
  refine ⟨i,⟨hi,by dsimp only [i]; rw [eq]; exact active.trans_le (largest _ ha)⟩,?_⟩
  intro j hj
  exact ⟨(largest _ hj).trans_eq eq.symm,fun h => min'_le _ _ (mem_filter.mpr ⟨hj,h.trans eq⟩)⟩

theorem upper (n : ℕ) (hn : 3 ≤ n) (b : ℝ) (hb : 1 ≤ b) (u : State)
    (bound : ∀ i ∈ sites n, gap u i ≤ b) :
    ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧
      (l.length:ℝ) ≤ 2*totalWeight n*Real.log (1+b) := by
  let D := totalWeight n
  have d : 0 < D := sum_pos' (fun i hi => (wpos hi).le)
    ⟨1,mem_Ioo.mpr ⟨by norm_num,by exact_mod_cast (show 1 < n by omega)⟩,
    wpos (n:=n) (i:=1) (mem_Ioo.mpr ⟨by norm_num,by exact_mod_cast (show 1 < n by omega)⟩)⟩
  have pos (v : State) : 0 ≤ clock D (energy n v) := by
    apply mul_nonneg (by positivity)
    exact sub_nonneg.mpr (Real.log_le_log d (by linarith [energy_nonneg n v]))
  have inductionBound (k : ℕ) : ∀ v, clock D (energy n v) ≤ k →
      ∃ l : List ℤ, follows (greedy n) v l ∧ sorted n (run v l) ∧ (l.length:ℝ) ≤ clock D (energy n v) := by
    induction k with
    | zero =>
      intro v hv
      by_cases s : sorted n v
      · exact ⟨[],trivial,s,by simpa using pos v⟩
      · obtain ⟨i,hi⟩ := chooseGreedy s
        have h := clock_drop d (energy_nonneg n v) (energy_nonneg n _) (energy_step hi.1) hi.1.2.le
          (energy_le (by linarith [hi.1.2]) (fun j hj => (hi.2 j hj).1))
        norm_num at hv; linarith [pos (step v i)]
    | succ k ih =>
      intro v hv
      by_cases s : sorted n v
      · exact ⟨[],trivial,s,by simpa using pos v⟩
      · obtain ⟨i,hi⟩ := chooseGreedy s
        have h := clock_drop d (energy_nonneg n v) (energy_nonneg n _) (energy_step hi.1) hi.1.2.le
          (energy_le (by linarith [hi.1.2]) (fun j hj => (hi.2 j hj).1))
        obtain ⟨l,follow,stop,cost⟩ := ih (step v i) (by push_cast at hv; linarith)
        exact ⟨i::l,⟨hi,follow⟩,stop,by simp; linarith⟩
  obtain ⟨l,h,s,c⟩ := inductionBound ⌈clock D (energy n u)⌉₊ u (Nat.le_ceil _)
  refine ⟨l,h,s,c.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [←Real.log_div (by linarith [energy_nonneg n u] : D+energy n u ≠ 0) d.ne']
  apply Real.log_le_log (div_pos (by linarith [energy_nonneg n u]) d)
  apply (div_le_iff₀ d).mpr
  have bound' : energy n u ≤ D*b := energy_le (by linarith) bound
  linarith

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

private def square (u : State) (i : ℤ) := (u i-(i:ℝ))^2
private def sqtotal (n : ℕ) (u : State) := ∑ k ∈ Ico (0:ℤ) n, square u k
private theorem sqpos (n : ℕ) (u : State) : 0 ≤ sqtotal n u := sum_nonneg fun _ _ => sq_nonneg _

private theorem sqdrop {n : ℕ} {i : ℤ} (hi : i ∈ sites n) (u : State) :
    sqtotal n (step u i)-sqtotal n u = -(gap u i)^2/2 := by
  obtain ⟨lo,up⟩ := inside hi
  let d (k : ℤ) := square (step u i) k-square u k
  have term (k : ℤ) : d k=spike (i-1) (d (i-1)) k + spike i (d i) k := by
    by_cases l : k=i-1
    · subst k; simp [spike,show i-1 ≠ i by omega]
    by_cases r : k=i
    · subst k; simp [spike,l]
    · simp [spike,l,r,d,square,step]
  have eq := sum_congr (s₁:=Ico (0:ℤ) (n:ℤ)) rfl (fun k _ => term k)
  rw [sum_add_distrib,spike_sum (mem_Ico.mpr ⟨by omega,by omega⟩ : i-1 ∈ Ico (0:ℤ) (n:ℤ)),
      spike_sum (mem_Ico.mpr ⟨by omega,up⟩ : i ∈ Ico (0:ℤ) (n:ℤ))] at eq
  simp only [d,sum_sub_distrib] at eq
  unfold sqtotal; rw [eq]
  simp [square,step,gap,show i ≠ i-1 by omega]
  ring

theorem legal_prefix (n : ℕ) (l : List ℤ) :
    ∀ u : State, follows (legal n) u l →
      (l.length:ℝ) + 2*sqtotal n (run u l) ≤ 2*sqtotal n u := by
  induction l with
  | nil => simp [run]
  | cons i l ih =>
    intro u path
    obtain ⟨hi,rest⟩ := path
    have d := sqdrop hi.1 u
    have g := hi.2
    have cost := ih (step u i) rest
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,run]
    nlinarith only [d,cost,sq_le_sq' (by linarith : -(gap u i) ≤ 1) g.le]

private theorem two_stage (n : ℕ) (hn : 3 ≤ n) (h : ℝ) (hh : 1 ≤ h) (u : State) :
    ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧
      (l.length:ℝ) ≤ 2*sqtotal n u/h^2+2*totalWeight n*Real.log (1+h) := by
  let Q (v : State) := 2*sqtotal n v/h^2
  let B := 2*totalWeight n*Real.log (1+h)
  have qp (v : State) : 0 ≤ Q v := div_nonneg (mul_nonneg (by norm_num) (sqpos n v)) (sq_nonneg _)
  have inductionBound (k : ℕ) : ∀ v, Q v ≤ k →
      ∃ l : List ℤ, follows (greedy n) v l ∧ sorted n (run v l) ∧ (l.length:ℝ) ≤ Q v+B := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hq
      by_cases good : ∀ j ∈ sites n, gap v j ≤ h
      · obtain ⟨l,path,stop,c⟩ := upper n hn h hh v good
        exact ⟨l,path,stop,c.trans (le_add_of_nonneg_left (qp v))⟩
      push Not at good
      obtain ⟨j,hj,large⟩ := good
      have unsorted : ¬sorted n v := fun s => (not_lt_of_ge ((s j hj).trans hh)) large
      obtain ⟨i,act⟩ := chooseGreedy unsorted
      have b := large.le.trans (act.2 j hj).1
      have hp : 0<h^2 := pow_pos (by linarith : 0<h) 2
      have drop : Q (step v i)+1 ≤ Q v := by
        dsimp only [Q]; apply (le_div_iff₀ hp).mpr
        rw [add_mul,div_mul_cancel₀ _ hp.ne',one_mul]
        nlinarith only [sqdrop act.1.1 v,sq_le_sq' (by linarith : -gap v i ≤ h) b]
      obtain ⟨l,path,stop,c⟩ := ih (k-1) (by
        have : (1:ℝ) ≤ k := by linarith [qp (step v i)]
        have hnat : 1 ≤ k := by exact_mod_cast this
        omega) (step v i) (by
        have : 1 ≤ k := by exact_mod_cast (show (1:ℝ) ≤ k by linarith [qp (step v i)])
        rw [Nat.cast_sub this,Nat.cast_one]; linarith)
      exact ⟨i::l,⟨act,path⟩,stop,by simp; linarith⟩
  exact inductionBound ⌈Q u⌉₊ u (Nat.le_ceil _)

/-- Put s=S/n for the uniform-amplitude model A, and s=S for model B. -/
theorem uniform (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : 0 ≤ s) (u : State)
    (bound : ∀ j ∈ Ico (0:ℤ) (n:ℤ), |u j| ≤ (n:ℝ)*s) :
    ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧
      (l.length:ℝ) ≤ 2*(n:ℝ)^3+2*totalWeight n*Real.log (2+s) := by
  let h := 1+s
  have hh : 1 ≤ h := by dsimp [h]; linarith
  obtain ⟨l,path,stop,c⟩ := two_stage n hn h hh u
  have e : sqtotal n u ≤ (n:ℝ)*((n:ℝ)*h)^2 := by
    unfold sqtotal
    calc _ ≤ ∑ _j ∈ Ico (0:ℤ) (n:ℤ), ((n:ℝ)*h)^2 := by
           apply sum_le_sum; intro j hj
           obtain ⟨lo,hi⟩ := mem_Ico.mp hj
           obtain ⟨p,q⟩ := abs_le.mp (bound j hj)
           have lo' : (0:ℝ) ≤ j := by exact_mod_cast lo
           have hi' : (j:ℝ) < n := by exact_mod_cast hi
           unfold square; apply sq_le_sq' <;> dsimp [h] <;> nlinarith only [p,q,lo',hi',Nat.cast_nonneg (α:=ℝ) n]
         _ = _ := by simp
  have bound' : 2*sqtotal n u/h^2 ≤ 2*(n:ℝ)^3 := by
    apply (div_le_iff₀ (pow_pos (by linarith : 0<h) 2)).mpr
    nlinarith only [e]
  have hi : 1+h=2+s := by dsimp [h]; ring
  rw [hi] at c
  exact ⟨l,path,stop,by linarith⟩
end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

def decode (n : ℕ) (c : ℝ) (x : State) : State := fun k =>
  c+(k:ℝ)+(weight n (k+1)*x (k+1)-weight n k*x k)/2

def half (n : ℕ) (x : State) (i : ℤ) : ℝ :=
  (weight n (i-1)*x (i-1)+weight n (i+1)*x (i+1))/(2*weight n i)

def fire (n : ℕ) (x : State) (i : ℤ) : State := Function.update x i (half n x i)

theorem gap_decode (n : ℕ) (c : ℝ) (x : State) (i : ℤ) :
    gap (decode n c x) i = weight n i*x i -
      (weight n (i-1)*x (i-1)+weight n (i+1)*x (i+1))/2 := by
  simp [gap,decode]; ring

theorem half_id {n : ℕ} {i : ℤ} (hi : i ∈ sites n) (x : State) :
    weight n i*half n x i =
      (weight n (i-1)*x (i-1)+weight n (i+1)*x (i+1))/2 := by
  unfold half; field_simp [(wpos hi).ne']

theorem step_decode {n : ℕ} {i : ℤ} (hi : i ∈ sites n) (c : ℝ) (x : State) :
    step (decode n c x) i = decode n c (fire n x i) := by
  funext k
  by_cases left : k=i-1
  · subst k
    simp [step,decode,fire,Function.update,show i-1 ≠ i by omega,half_id hi]
    ring
  by_cases right : k=i
  · subst k
    simp [step,decode,fire,Function.update,left,show i+1 ≠ i by omega,half_id hi]
    ring
  · simp [step,decode,fire,Function.update,left,right,show k+1 ≠ i by omega]

theorem half_pos {n : ℕ} (hn : 3 ≤ n) {i : ℤ} (hi : i ∈ sites n)
    {x : State} (xp : ∀ k, 0 < x k) : 0 < half n x i := by
  obtain ⟨l,h⟩ := inside hi
  have a := wclosed (n:=n) (i:=i-1) (by omega) (by omega)
  have b := wclosed (n:=n) (i:=i+1) (by omega) (by omega)
  have both := harmonic n i
  have w := wtwo hn hi
  unfold half
  apply div_pos _ (mul_pos (by norm_num) (wpos hi))
  rcases eq_or_lt_of_le a with z|pos
  · have : 0 < weight n (i+1) := by linarith
    rw [←z,zero_mul,zero_add]; exact mul_pos this (xp _)
  · exact add_pos_of_pos_of_nonneg (mul_pos pos (xp _)) (mul_nonneg b (xp _).le)

theorem after_pos {n : ℕ} (hn : 3 ≤ n) {i : ℤ} (hi : i ∈ sites n)
    {x : State} (xp : ∀ k, 0 < x k) : ∀ k, 0 < fire n x i k := by
  intro k; by_cases eq : k=i
  · subst k; simpa [fire] using half_pos hn hi xp
  · simpa [fire,eq] using xp k

def logs (R : ℝ) (x : State) : State := fun k => Real.log R-Real.log (x k)

private theorem avg_log {a b x y : ℝ} (a₀ : 0 ≤ a) (b₀ : 0 ≤ b)
    (_ab : 0 < a+b) (xp : 0 < x) (yp : 0 < y) {m : ℝ} (mp : 0 < m)
    (mean : (a+b)*m=a*x+b*y) :
    a*Real.log x+b*Real.log y ≤ (a+b)*Real.log m := by
  have tangent (z : ℝ) (zp : 0 < z) : (Real.log z-Real.log m+1)*m ≤ z := by
    apply (le_div_iff₀ mp).mp
    have v := Real.log_le_sub_one_of_pos (div_pos zp mp)
    rw [Real.log_div zp.ne' mp.ne'] at v
    linarith
  have eq := mul_le_mul_of_nonneg_left (tangent x xp) a₀
  have eq' := mul_le_mul_of_nonneg_left (tangent y yp) b₀
  apply (le_of_mul_le_mul_right (a:=m) _ mp)
  nlinarith only [eq,eq',mean]

/-- Logarithmic decay at a site is controlled by its two neighbors. Boundary
weights are zero, so the same inequality covers both endpoint sites. -/
theorem log_local {n : ℕ} (hn : 3 ≤ n) {i : ℤ} (hi : i ∈ sites n)
    (R : ℝ) {x : State} (xp : ∀ k, 0 < x k) :
    let w := weight n i
    let a := weight n (i-1)
    let b := weight n (i+1)
    let f := logs R x
    let z := logs R (fire n x i) i
    2*(w-1)*z ≤ 2+a*f (i-1)+b*f (i+1) := by
  intro w a b f z
  have w₂ : 2 ≤ w := wtwo hn hi
  have w₁ : 0 < w-1 := by linarith
  have wp : 0 < w := by linarith
  obtain ⟨l,h⟩ := inside hi
  have a₀ : 0 ≤ a := wclosed (by omega) (by omega)
  have b₀ : 0 ≤ b := wclosed (by omega) (by omega)
  have ab : a+b=2*(w-1) := harmonic n i
  have pp := half_pos hn hi xp
  let m := half n x i*w/(w-1)
  have mp : 0 < m := div_pos (mul_pos pp wp) w₁
  have id : (a+b)*m = a*x (i-1)+b*x (i+1) := by
    rw [ab]
    dsimp only [m]; field_simp [w₁.ne']
    have v := half_id hi x
    change w*half n x i=_ at v
    change _=a*x (i-1)+b*x (i+1) at *
    nlinarith
  have lg := avg_log a₀ b₀ (by rw [ab]; positivity) (xp _) (xp _) mp id
  have lt := Real.log_le_sub_one_of_pos (div_pos wp w₁)
  have lt' : Real.log (w/(w-1))*(w-1) ≤ 1 := by
    have q : (Real.log (w/(w-1))+1)*(w-1) ≤ w := (le_div_iff₀ w₁).mp (by linarith)
    linarith
  have ml : Real.log m=Real.log (half n x i)+Real.log (w/(w-1)) := by
    rw [←Real.log_mul pp.ne' (div_pos wp w₁).ne']; congr 1; dsimp [m]; ring
  rw [ml,ab] at lg
  dsimp [z,f,logs,fire]
  rw [Function.update_self]
  nlinarith only [lg,lt',congrArg (fun v : ℝ => v*Real.log R) ab]

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

def edge (n : ℕ) (f : State) (j : ℤ) : ℝ :=
  weight n j*weight n (j+1)/4*(f (j+1)-f j)^2
def dirichlet (n : ℕ) (f : State) : ℝ := ∑ j ∈ Ico (0:ℤ) (n:ℤ), edge n f j
def progress (n : ℕ) (f : State) : ℝ := (∑ j ∈ sites n, weight n j*f j)+dirichlet n f

theorem dirichlet_nonneg (n : ℕ) (f : State) : 0 ≤ dirichlet n f := by
  apply sum_nonneg; intro j hj
  obtain ⟨l,h⟩ := mem_Ico.mp hj
  have ap := wclosed (n:=n) (i:=j) l (by omega)
  have bp := wclosed (n:=n) (i:=j+1) (by omega) (by omega)
  unfold edge; positivity

private theorem progress_update {n : ℕ} {i : ℤ} (hi : i ∈ sites n) (f : State) (z : ℝ) :
    let δ := z-f i
    let a := weight n (i-1)
    let w := weight n i
    let b := weight n (i+1)
    progress n (Function.update f i z)-progress n f =
      w*δ+w/4*(a*(2*(f i-f (i-1))*δ+δ^2)+b*(2*(f i-f (i+1))*δ+δ^2)) := by
  intro δ a w b
  let u := Function.update f i z
  have dj (k : ℤ) : weight n k * u k-weight n k*f k=spike i (w*δ) k := by
    by_cases eq : k=i
    · subst k; simp [u,δ,w,spike]; ring
    · simp [u,spike,eq]
  let v₁ := w*a/4*(2*(f i-f (i-1))*δ+δ^2)
  let v₂ := w*b/4*(2*(f i-f (i+1))*δ+δ^2)
  have dk (k : ℤ) : edge n u k-edge n f k=spike (i-1) v₁ k+spike i v₂ k := by
    by_cases eq : k=i-1
    · subst k; simp [edge,u,v₁,w,a,δ,spike,show i-1 ≠ i by omega]; ring
    by_cases eq' : k=i
    · subst k; simp [edge,u,v₂,w,b,δ,spike,eq,show i+1 ≠ i by omega]; ring
    · simp [edge,u,spike,eq,eq',show k+1 ≠ i by omega]
  obtain ⟨l,h⟩ := inside hi
  have di : i∈Ico (0:ℤ) n := mem_Ico.mpr ⟨by omega,h⟩
  have dm : i-1∈Ico (0:ℤ) n := mem_Ico.mpr ⟨by omega,by omega⟩
  have H₁ := sum_congr (s₁:=sites n) rfl (fun k _ => dj k)
  rw [sum_sub_distrib,spike_sum hi] at H₁
  have H₂ := sum_congr (s₁:=Ico (0:ℤ) (n:ℤ)) rfl (fun k _ => dk k)
  rw [sum_sub_distrib,sum_add_distrib,spike_sum dm,spike_sum di] at H₂
  change dirichlet n u-dirichlet n f=v₁+v₂ at H₂
  change progress n u-progress n f=_
  unfold progress
  dsimp only [v₁,v₂] at H₂
  linarith only [H₁,H₂]

theorem progress_step {n : ℕ} (hn : 3 ≤ n) {c R : ℝ} {x : State}
    (xp : ∀ k, 0 < x k) {i : ℤ} (hi : legal n (decode n c x) i) :
    progress n (logs R (fire n x i)) ≤ progress n (logs R x)+4 := by
  let w := weight n i
  let a := weight n (i-1)
  let b := weight n (i+1)
  let f := logs R x
  let z := logs R (fire n x i) i
  let δ := z-f i
  have up : logs R (fire n x i)=Function.update f i z := by
    funext k; by_cases eq : k=i
    · subst k; simp [z]
    · simp [f,logs,fire,Function.update,eq]
  have wp : 0 < w := wpos hi.1
  have w₂ : 2 ≤ w := wtwo hn hi.1
  have hp := half_id hi.1 x
  have change' := hi.2
  rw [gap_decode] at change'
  have hfi : half n x i ≤ x i := (le_of_mul_le_mul_left (a:=w) (by dsimp [w]; linarith) wp)
  have dd : 0 ≤ δ := by
    dsimp [δ,z,f,logs,fire]; simp only [Function.update_self]
    linarith [Real.log_le_log (half_pos hn hi.1 xp) hfi]
  have diff := progress_update hi.1 f z
  have drift : 2*(w-1)*z ≤ 2+a*f (i-1)+b*f (i+1) := log_local hn hi.1 R xp
  have harm : a+b=2*(w-1) := harmonic n i
  have H : a*(f i-f (i-1))+b*(f i-f (i+1)) ≤ 2-2*(w-1)*δ := by
    dsimp only [δ]; nlinarith only [drift,congrArg (fun y : ℝ => y*f i) harm]
  have ml := mul_le_mul_of_nonneg_right H (mul_nonneg wp.le dd)
  have dd₂ := congrArg (fun y : ℝ => w*y*δ^2) harm
  have loc : progress n (Function.update f i z)-progress n f ≤ 2*w*δ-w*(w-1)/2*δ^2 := by
    change _=w*δ+w/4*(a*(2*(f i-f (i-1))*δ+δ^2)+b*(2*(f i-f (i+1))*δ+δ^2)) at diff
    nlinarith only [diff,ml,dd₂]
  have coerc : w/4 ≤ (w-1)/2 := by linarith
  have s := mul_le_mul_of_nonneg_right coerc (mul_nonneg wp.le (sq_nonneg δ))
  rw [up]
  change progress n (Function.update f i z) ≤ progress n f+4
  nlinarith only [loc,s,sq_nonneg (w*δ-4)]

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

private theorem terminal {n : ℕ} (hn : 3 ≤ n) {c R : ℝ} {x : State}
    (xp : ∀ k, 0 < x k) (stop : sorted n (decode n c x)) :
    totalWeight n*Real.log R ≤ progress n (logs R x) := by
  have mem : (1:ℤ) ∈ sites n := mem_Ioo.mpr ⟨by norm_num, by exact_mod_cast (show 1<n by omega)⟩
  obtain ⟨m,hm,big⟩ := (sites n).exists_max_image x ⟨1,mem⟩
  obtain ⟨l,h⟩ := inside hm
  have weighted (k : ℤ) (lo : 0 ≤ k) (up : k ≤ (n:ℤ)) : weight n k*x k ≤ weight n k*x m := by
    by_cases hi : k ∈ sites n
    · exact mul_le_mul_of_nonneg_left (big _ hi) (wpos hi).le
    · have alt : k=0 ∨ k=(n:ℤ) := by change ¬k∈Ioo (0:ℤ) n at hi; simp only [mem_Ioo] at hi; omega
      rcases alt with rfl|rfl <;> simp [weight]
  have sm := stop m hm
  rw [gap_decode] at sm
  have mx : x m ≤ 1 := by
    nlinarith only [sm,weighted (m-1) (by omega) (by omega),weighted (m+1) (by omega) (by omega),
      congrArg (fun v : ℝ => v*x m) (harmonic n m)]
  unfold totalWeight progress
  rw [sum_mul]
  apply le_trans _ (le_add_of_nonneg_right (dirichlet_nonneg ..))
  apply sum_le_sum; intro k hk
  apply mul_le_mul_of_nonneg_left _ (wpos hk).le
  have := Real.log_nonpos (xp k).le ((big k hk).trans mx)
  dsimp [logs]; linarith

private theorem path_cost {n : ℕ} (hn : 3 ≤ n) (c R : ℝ) (l : List ℤ) :
    ∀ x : State, (∀ k, 0 < x k) → follows (legal n) (decode n c x) l →
    sorted n (run (decode n c x) l) →
    totalWeight n*Real.log R ≤ progress n (logs R x)+4*l.length := by
  induction l with
  | nil =>
    intro x xp _ stop
    simpa using terminal (R:=R) hn xp stop
  | cons i l ih =>
    intro x xp path stop
    obtain ⟨act,follow⟩ := path
    change sorted n (run (step (decode n c x) i) l) at stop
    rw [step_decode act.1] at follow stop
    have h := ih (fire n x i) (after_pos hn act.1 xp) follow stop
    have q := progress_step (R:=R) hn xp act
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

theorem lower (n : ℕ) (hn : 3 ≤ n) (r : ℕ) (l : List ℤ) :
    let u : State := fun k => -(r:ℝ)*(k:ℝ)
    follows (legal n) u l → sorted n (run u l) →
    totalWeight n*Real.log (1+(r:ℝ)) ≤ 4*l.length := by
  intro u path stop
  let R : ℝ := 1+r
  let c : ℝ := -R*((n:ℝ)-1)/2
  let x : State := fun _ => R
  have init : decode n c x = u := by
    funext k; dsimp [decode,c,x,R,weight,u]; push_cast; ring
  rw [←init] at path stop
  have p := path_cost hn c R l x (fun _ => by dsimp [x,R]; positivity) path stop
  have z : logs R x = fun _ => 0 := by funext k; simp [logs,x]
  rw [z] at p
  simpa [dirichlet,progress,edge] using p

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

theorem counter :
    ∃ u : State, ∃ g l : List ℤ, (∀ k, ∃ z : ℤ, u k=z) ∧ follows (greedy 4) u g ∧ sorted 4 (run u g) ∧
      follows (legal 4) u l ∧ sorted 4 (run u l) ∧ l.length < g.length := by
  let u : State := fun i => if i=0 then 1 else if i=1 then 3 else if i=2 then 1 else 0
  refine ⟨u,[2,3,2,1],[3,2,3],?_,?_⟩
  · intro k; dsimp [u]; split_ifs
    · exact ⟨1,by norm_num⟩
    · exact ⟨3,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  have s4 : sites 4={1,2,3} := by ext i; simp [sites]; omega
  norm_num [follows,run,greedy,legal,sorted,gap,step,u,s4,Finset.forall_mem_insert]

theorem small_n (n : ℕ) (hn : n ≤ 2) (u : State) :
    ∃ l : List ℤ, follows (greedy n) u l ∧ sorted n (run u l) ∧ l.length ≤ 1 := by
  by_cases done : sorted n u
  · exact ⟨[],trivial,done,by simp⟩
  have site (i : ℤ) (hi : i ∈ sites n) : i=1 := by obtain ⟨_,_⟩ := inside hi; omega
  change ¬∀ i ∈ sites n, gap u i ≤ 1 at done
  push Not at done
  obtain ⟨i,hi,active⟩ := done
  have chosen : greedy n u i := by
    refine ⟨⟨hi,active⟩,?_⟩; intro j hj
    rw [(site _ hj).trans (site _ hi).symm]; simp
  refine ⟨[i],⟨chosen,trivial⟩,?_,by simp⟩
  intro j hj; rw [(site _ hj).trans (site _ hi).symm]
  simp [run,gap,step,show i ≠ i-1 by omega]; linarith

theorem weight_formula (n : ℕ) :
    6*totalWeight n = (n:ℝ)*(n-1)*(n+1) := by
  suffices h : 2*(∑ i ∈ sites n, (i:ℝ))=(n:ℝ)*(n-1) ∧
      6*totalWeight n=(n:ℝ)*(n-1)*(n+1) from h.2
  induction n with
  | zero => simp [totalWeight,sites]
  | succ n ih =>
    by_cases z : n=0
    · subst n
      have h : sites 1=∅ := by ext i; simp [sites]; omega
      norm_num [h,totalWeight]
    have mem : (n:ℤ) ∉ sites n := by simp [sites]
    have insert : sites (n+1)=insert (n:ℤ) (sites n) := by ext i; simp [sites]; omega
    have sumw : (∑ i ∈ sites n, weight (n+1) i)=totalWeight n+∑ i ∈ sites n, (i:ℝ) := by
      unfold totalWeight; rw [←sum_add_distrib]
      apply sum_congr rfl; intro i _; unfold weight; push_cast; ring
    have node : weight (n+1) (n:ℤ)=(n:ℝ) := by simp [weight]
    change _ ∧ 6*(∑ i ∈ sites (n+1), weight (n+1) i)=_
    rw [insert,sum_insert mem,sum_insert mem,sumw,node]
    push_cast
    constructor <;> nlinarith only [ih.1,ih.2]

end
end Averaging

namespace Averaging
open OMA.S_mo_218359 Finset
noncomputable section

private def slope (r : ℕ) : State := fun k => -(r:ℝ)*(k:ℝ)

private theorem integral_slope (r : ℕ) (k : ℤ) : ∃ z : ℤ, slope r k=z := by
  exact ⟨-(r:ℤ)*k,by dsimp [slope]; push_cast; rfl⟩

private theorem hard (n : ℕ) (hn : 3 ≤ n) (r : ℕ) (l : List ℤ)
    (path : follows (legal n) (slope r) l) (stop : sorted n (run (slope r) l)) :
    totalWeight n*Real.log (1+(r:ℝ))/4 ≤ l.length := by linarith [lower n hn r l path stop]

theorem models (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : 0 ≤ s) :
    complexityBounds n (uniformInput n s)
      (totalWeight n*Real.log (1+(⌊s/n⌋₊:ℝ))/4) (2*(n:ℝ)^3+2*totalWeight n*Real.log (2+s/n)) ∧
    complexityBounds n (growingInput n s)
      (totalWeight n*Real.log (1+(⌊s⌋₊:ℝ))/4) (2*(n:ℝ)^3+2*totalWeight n*Real.log (2+s)) := by
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hnrm : (n:ℝ)*(s/n)=s := by field_simp
  have absval (r : ℕ) {k : ℤ} (kp : 0 ≤ k) : |slope r k|=(r:ℝ)*(k:ℝ) := by
    dsimp [slope]; rw [neg_mul,abs_neg,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast kp))]
  constructor
  · constructor
    · intro u hu; apply uniform n hn _ (div_nonneg hs np.le)
      intro k hk; rw [hnrm]; exact hu k hk
    · let r := ⌊s/n⌋₊
      refine ⟨slope r,?_,integral_slope r,hard n hn r⟩
      intro k hk
      obtain ⟨lo,hi⟩ := mem_Ico.mp hk
      rw [absval r lo,←hnrm,mul_comm (n:ℝ)]
      exact mul_le_mul (Nat.floor_le (div_nonneg hs np.le)) (by exact_mod_cast hi.le)
        (by exact_mod_cast lo) (div_nonneg hs np.le)
  · constructor
    · intro u hu; apply uniform n hn _ hs
      intro k hk
      have count : k+1 ≤ (n:ℤ) := (mem_Ico.mp hk).2
      exact (hu k hk).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast count) hs)
    · let r := ⌊s⌋₊
      refine ⟨slope r,?_,integral_slope r,hard n hn r⟩
      intro k hk; obtain ⟨lo,_⟩ := mem_Ico.mp hk
      rw [absval r lo,mul_comm _ s]
      exact mul_le_mul (Nat.floor_le hs) (by linarith) (by exact_mod_cast lo) hs

theorem greedy_unique {n : ℕ} {u : State} {i j : ℤ} (hi : greedy n u i) (hj : greedy n u j) : i=j := by
  have l := hi.2 j hj.1.1
  have r := hj.2 i hi.1.1
  exact le_antisymm (l.2 (le_antisymm l.1 r.1)) (r.2 (le_antisymm r.1 l.1))

end
end Averaging

namespace Averaging
open OMA.S_mo_218359
noncomputable section

private theorem relax {n : ℕ} {inputs : State → Prop} {L U L' U' : ℝ}
    (known : complexityBounds n inputs L U) (lo : L' ≤ L) (hi : U ≤ U') :
    complexityBounds n inputs L' U' := by
  constructor
  · intro u bound; obtain ⟨l,path,stop,c⟩ := known.1 u bound
    exact ⟨l,path,stop,c.trans hi⟩
  · obtain ⟨u,bound,z,hard⟩ := known.2
    exact ⟨u,bound,z,fun l h s => lo.trans (hard l h s)⟩

private theorem tight {n : ℕ} (hn : 3 ≤ n) {t : ℝ} (ht : 1 ≤ t) {inputs : State → Prop}
    (known : complexityBounds n inputs (totalWeight n*Real.log (1+(⌊t⌋₊:ℝ))/4)
      (2*(n:ℝ)^3+2*totalWeight n*Real.log (2+t))) :
    complexityBounds n inputs ((n:ℝ)^3*Real.log (1+t)/64) (5*(n:ℝ)^3*Real.log (1+t)) := by
  have c : (3:ℝ) ≤ n := by exact_mod_cast hn
  have np : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have p : 0 ≤ (n:ℝ)^3 := by positivity
  have bounds := weight_formula n
  have lo : (n:ℝ)^3/8 ≤ totalWeight n := by
    nlinarith only [bounds,mul_nonneg np (show 0 ≤ ((n:ℝ)-2)*(n+2) by exact mul_nonneg (by linarith) (by linarith))]
  have hi : totalWeight n ≤ (n:ℝ)^3/6 := by nlinarith only [bounds,np]
  let f : ℝ := ⌊t⌋₊
  have fl : 1 ≤ f := by
    dsimp [f]
    have z : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
    exact_mod_cast z
  have upp : t < f+1 := Nat.lt_floor_add_one _
  have logf : Real.log (1+t) ≤ 2*Real.log (1+f) := by
    have z : 1+t ≤ (1+f)^2 := by nlinarith [sq_nonneg f]
    simpa [Real.log_pow] using Real.log_le_log (by linarith : 0<1+t) z
  have logt : Real.log (2+t) ≤ 2*Real.log (1+t) := by
    have z : 2+t ≤ (1+t)^2 := by nlinarith [sq_nonneg t]
    simpa [Real.log_pow] using Real.log_le_log (by linarith : 0<2+t) z
  have half : (1:ℝ)/2 ≤ Real.log (1+t) := by
    have z := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ)⁻¹)
    rw [Real.log_inv] at z
    have q := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2 ≤ 1+t)
    linarith
  apply relax known
  · have lh := mul_le_mul_of_nonneg_left logf p
    have lf : 0 ≤ Real.log (1+f) := Real.log_nonneg (by linarith)
    have ll := mul_le_mul_of_nonneg_right lo lf
    change _ ≤ totalWeight n*Real.log (1+f)/4
    linarith only [lh,ll]
  · have l₂ : 0 ≤ Real.log (2+t) := Real.log_nonneg (by linarith)
    nlinarith only [p,mul_le_mul_of_nonneg_right hi l₂,mul_le_mul_of_nonneg_left logt p,
      mul_le_mul_of_nonneg_left half p]

theorem ratesA (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : (n:ℝ) ≤ s) :
    complexityBounds n (uniformInput n s) ((n:ℝ)^3*Real.log (1+s/n)/64)
      (5*(n:ℝ)^3*Real.log (1+s/n)) := by
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  exact tight hn ((one_le_div np).mpr hs) (models n hn s (np.le.trans hs)).1

theorem ratesB (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : 1 ≤ s) :
    complexityBounds n (growingInput n s) ((n:ℝ)^3*Real.log (1+s)/64)
      (5*(n:ℝ)^3*Real.log (1+s)) :=
  tight hn hs (models n hn s (by linarith)).2
end
end Averaging

theorem OMA.solution : type_of% @OMA.S_mo_218359.main :=
  ⟨Averaging.models, Averaging.weight_formula, Averaging.small_n, Averaging.counter⟩
