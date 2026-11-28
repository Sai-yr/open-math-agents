import OMAStatements.S_mo_476612



namespace UpperSum
open OMA.S_mo_476612 Finset

theorem cost_cont (p : ℕ → ℝ) (t : ℕ) : Continuous (cost p t) := by
  unfold cost
  fun_prop

theorem cost_mono (p : ℕ → ℝ) (t : ℕ) : Monotone (cost p t) := by
  intro x y h
  exact sum_le_sum fun k _ => div_le_div_of_nonneg_right
    (max_le_max_right 0 (by linarith)) (Real.sqrt_nonneg _)

theorem cost_zero {p : ℕ → ℝ} (hp : UnitData p) (t : ℕ) : cost p t 0=0 := by
  apply sum_eq_zero
  intro k _
  rw [max_eq_right (by linarith [(hp k).1]),zero_div]

theorem cap_spec {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0 < C) (t : ℕ) :
    IsGreatest {x ∈ Set.Icc (0:ℝ) 1 | cost p t x ≤ C} (threshold p C t) := by
  let s := {x ∈ Set.Icc (0:ℝ) 1 | cost p t x ≤ C}
  have compact : IsCompact s := isCompact_Icc.inter_right (isClosed_le (cost_cont p t) continuous_const)
  have nonempty : s.Nonempty := ⟨0,⟨le_refl _,zero_le_one⟩,by rw [cost_zero hp]; exact hC.le⟩
  obtain ⟨x,hx⟩ := compact.exists_isGreatest nonempty
  change IsGreatest s (sSup s)
  rwa [hx.csSup_eq]

theorem level_fits {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0 < C)
    (t : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (budget : cost p t x ≤ C) :
    x ≤ threshold p C t := (cap_spec hp hC t).2 ⟨hx,budget⟩

end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset

private theorem strict_cost {p : ℕ → ℝ} {t : ℕ} {x y : ℝ} (xy : x < y) (pos : 0 < cost p t x) :
    cost p t x < cost p t y := by
  have hits : ∃ k ∈ range (t+1), p k < x := by
    by_contra! h
    have z : cost p t x=0 := sum_eq_zero fun k hk => by
      rw [max_eq_right (sub_nonpos.mpr (h k hk)),zero_div]
    linarith
  obtain ⟨k,hk,hit⟩ := hits
  apply sum_lt_sum (fun j _ => div_le_div_of_nonneg_right (max_le_max_right _ (by linarith))
    (Real.sqrt_nonneg _))
  refine ⟨k,hk,?_⟩
  rw [max_eq_left (sub_nonneg.mpr hit.le),max_eq_left (sub_nonneg.mpr (hit.trans xy).le)]
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

theorem root_spec (p : ℕ → ℝ) (hp : UnitData p) (C : ℝ) (hC : 0 < C) (t : ℕ) :
    ∃ r : ℝ, cost p t r=C ∧ (∀ x, cost p t x=C → x=r) ∧ threshold p C t=min 1 r := by
  have hi : C ≤ cost p t (1+C) := by
    have h := single_le_sum (s:=range (t+1)) (f:=fun k : ℕ =>
      max (1+C-p k) 0 / Real.sqrt (k+1)) (fun k _ => by positivity) (show 0∈range (t+1) by simp)
    simp only [Nat.cast_zero,zero_add,Real.sqrt_one,div_one] at h
    exact (show C ≤ max (1+C-p 0) 0 from le_trans (by linarith [(hp 0).2]) (le_max_left ..)).trans h
  obtain ⟨r,hr,eq⟩ := intermediate_value_Icc (show 0 ≤ 1+C by linarith)
    (cost_cont p t).continuousOn (show C ∈ Set.Icc (cost p t 0) (cost p t (1+C)) from ⟨by rw [cost_zero hp]; exact hC.le,hi⟩)
  refine ⟨r,eq,?_,?_⟩
  · intro x hit
    rcases lt_trichotomy x r with h|h|h
    · linarith [strict_cost h (hit ▸ hC : 0 < cost p t x)]
    · exact h
    · linarith [strict_cost h (eq ▸ hC : 0 < cost p t r)]
  · have cap := cap_spec hp hC t
    rcases le_total r 1 with r1|r1
    · rw [min_eq_right r1]
      apply le_antisymm _ (level_fits hp hC t ⟨hr.1,r1⟩ eq.le)
      by_contra! h
      have above := strict_cost h (eq ▸ hC : 0 < cost p t r)
      linarith [cap.1.2]
    · rw [min_eq_left r1]
      exact le_antisymm cap.1.1.2 (level_fits hp hC t ⟨zero_le_one,le_rfl⟩
        ((cost_mono p t r1).trans eq.le))
end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset

/-- Use prefix size n instead of last index; the empty prefix has level 1. -/
private noncomputable def level (p : ℕ → ℝ) (C : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => threshold p C n

private noncomputable def energy (p : ℕ → ℝ) (n : ℕ) (x : ℝ) :=
  ∑ k ∈ range n, max (x-p k) 0 ^ 2 / Real.sqrt (k+1)

private theorem properties {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0<C) (n : ℕ) :
    level p C n ∈ Set.Icc (0:ℝ) 1 ∧
    (∑ k ∈ range n, max (level p C n-p k) 0 / Real.sqrt (k+1)) ≤ C := by
  cases n with
  | zero => simp [level,hC.le]
  | succ n => exact (cap_spec hp hC n).1

private theorem down {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0<C) (n : ℕ) :
    level p C (n+1) ≤ level p C n := by
  cases n with
  | zero => exact (properties hp hC 1).1.2
  | succ i =>
    apply level_fits hp hC i (properties hp hC (i+2)).1
    have h := (properties hp hC (i+2)).2
    rw [sum_range_succ] at h
    have pos : 0 ≤ max (level p C (i+2)-p (i+1)) 0 / Real.sqrt (((i+1:ℕ):ℝ)+1) :=
      div_nonneg (le_max_right ..) (Real.sqrt_nonneg _)
    exact (le_add_of_nonneg_right pos).trans h

private theorem energy_drop {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0<C)
    (n : ℕ) {x : ℝ} (hx : x ≤ level p C n) :
    energy p n (level p C n)-energy p n x ≤ 2*C*(level p C n-x) := by
  let y := level p C n
  have yn : 0 ≤ y-x := sub_nonneg.mpr hx
  have point (k : ℕ) : max (y-p k) 0^2-max (x-p k) 0^2 ≤
      (2*(y-x))*max (y-p k) 0 := by
    by_cases ll : p k ≤ x
    · rw [max_eq_left (sub_nonneg.mpr ll),max_eq_left (sub_nonneg.mpr (ll.trans hx))]
      nlinarith [sq_nonneg (y-x)]
    · rw [max_eq_right (by linarith : x-p k ≤ 0)]
      by_cases rr : p k ≤ y
      · rw [max_eq_left (sub_nonneg.mpr rr)]
        nlinarith [mul_nonneg (sub_nonneg.mpr rr) (show 0 ≤ (y-x)*2-(y-p k) by linarith)]
      · simp [max_eq_right (le_of_not_ge (by simpa using rr) : y-p k ≤ 0)]
  change energy p n y - energy p n x ≤ _
  unfold energy
  rw [←sum_sub_distrib]
  calc _ ≤ ∑ k ∈ range n, (2*(y-x))*(max (y-p k) 0/Real.sqrt (k+1)) := by
         apply sum_le_sum; intro k _
         rw [←sub_div,←mul_div_assoc]
         exact div_le_div_of_nonneg_right (point k) (Real.sqrt_nonneg _)
       _ = (2*(y-x))*(∑ k ∈ range n, max (y-p k) 0/Real.sqrt (k+1)) := (mul_sum ..).symm
       _ ≤ _ := by
         have h := mul_le_mul_of_nonneg_left (properties hp hC n).2 (show 0 ≤ 2*(y-x) by positivity)
         dsimp [y] at *
         linarith only [h]

theorem square_budget {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0<C) (T : ℕ) :
    ∑ k ∈ range T, max (threshold p C k-p k) 0 ^ 2 / Real.sqrt (k+1) ≤ 2*C := by
  have telescopes (n : ℕ) :
      (∑ k ∈ range n, max (threshold p C k-p k) 0 ^ 2/Real.sqrt (k+1)) +
        2*C*level p C n-energy p n (level p C n) ≤ 2*C := by
    induction n with
    | zero => simp [level,energy]
    | succ n ih =>
      rw [sum_range_succ]
      have dif := energy_drop hp hC n (down hp hC n)
      have eq : energy p (n+1) (level p C (n+1)) = energy p n (level p C (n+1)) +
          max (threshold p C n-p n) 0^2/Real.sqrt (n+1) := by
        unfold energy; rw [sum_range_succ]; rfl
      rw [eq]
      linarith only [ih,dif]
  let y := level p C T
  have yp := (properties hp hC T).1.1
  have small : energy p T y ≤ y*C := by
    unfold energy
    calc _ ≤ ∑ k ∈ range T, y*(max (y-p k) 0/Real.sqrt (k+1)) := by
           apply sum_le_sum; intro k _
           rw [←mul_div_assoc,pow_two]
           apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
           exact mul_le_mul_of_nonneg_right (max_le (sub_le_self _ (hp k).1) yp) (le_max_right ..)
         _ = y*(∑ k ∈ range T, max (y-p k) 0/Real.sqrt (k+1)) := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (properties hp hC T).2 yp
  dsimp [y] at *
  nlinarith only [telescopes T,small,mul_nonneg hC.le yp]

theorem energy_upper {p : ℕ → ℝ} (hp : UnitData p) {C : ℝ} (hC : 0<C) (T : ℕ) :
    excess p C T ≤ Real.sqrt (2*C*(∑ k ∈ range T, Real.sqrt (k+1))) := by
  cases T with
  | zero => simp [excess]
  | succ t =>
    let f (k : ℕ) := max (threshold p C k-p k) 0
    let s := range (t+1)
    have total : 0 < ∑ k ∈ s, Real.sqrt ((k:ℝ)+1) := by
      exact sum_pos' (fun _ _ => Real.sqrt_nonneg _) ⟨0,by simp [s],by norm_num⟩
    have cs := sq_sum_div_le_sum_sq_div s f (g:=fun k : ℕ => Real.sqrt ((k:ℝ)+1))
      (fun k _ => by positivity)
    have sq := (div_le_iff₀ total).mp (cs.trans (square_budget hp hC (t+1)))
    calc excess p C (t+1) ≤ ∑ k ∈ s, f k := sum_le_sum fun k _ => le_max_left .. 
         _ ≤ _ := Real.le_sqrt_of_sq_le sq
end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset

private def index (m k : ℕ) : ℕ := if k < m^4 then 0 else (k-m^4)/m^3+1
private noncomputable def stair (m k : ℕ) : ℝ := max 0 (1-(index m k:ℝ)/m)

private theorem index_mono (m : ℕ) : Monotone (index m) := by
  intro i j h
  unfold index
  split_ifs with hi hj hj
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le_sub_right h _)) 1

private theorem stair_properties (m : ℕ) : UnitData (stair m) ∧ Antitone (stair m) := by
  constructor
  · intro k
    exact ⟨le_max_left ..,max_le (by norm_num) (sub_le_self _ (by positivity))⟩
  · intro i j h
    apply max_le_max_left
    have ij : (index m i:ℝ) ≤ index m j := by exact_mod_cast index_mono m h
    exact sub_le_sub_left (div_le_div_of_nonneg_right ij (Nat.cast_nonneg _)) _

/-- A block of length m³, at indices at least m⁴, costs at most 1 if the
positive deviation is at most 1/m. Earlier summands vanish. -/
private theorem block_budget {p : ℕ → ℝ} {m t a : ℕ} (hm : 0 < m)
    (first : m^4 ≤ a) (length : t+1 ≤ a+m^3) {x : ℝ}
    (before : ∀ i, i<a → x ≤ p i)
    (during : ∀ i ∈ Ico a (t+1), x-p i ≤ (1:ℝ)/m) : cost p t x ≤ 1 := by
  let f (i : ℕ) := max (x-p i) 0 / Real.sqrt (i+1)
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have shrunk : ∑ i ∈ Ico a (t+1), f i = ∑ i ∈ range (t+1), f i := by
    apply sum_subset (fun i h => mem_range.mpr (mem_Ico.mp h).2)
    intro i hi hni
    have outside : i<a := by have := mem_range.mp hi; by_contra! h; exact hni (mem_Ico.mpr ⟨h,this⟩)
    simp [f,max_eq_right (sub_nonpos.mpr (before i outside))]
  change (∑ i ∈ range (t+1), f i) ≤ 1
  rw [←shrunk]
  calc _ ≤ ∑ _i ∈ Ico a (t+1), (1:ℝ)/(m:ℝ)^3 := by
         apply sum_le_sum
         intro i hi
         have mi : (m:ℝ)^4 ≤ (i:ℝ)+1 := by exact_mod_cast (show m^4 ≤ i+1 by have := (mem_Ico.mp hi).1; omega)
         have rt : (m:ℝ)^2 ≤ Real.sqrt ((i:ℝ)+1) := by
           rw [←Real.sqrt_sq (sq_nonneg (m:ℝ))]
           apply Real.sqrt_le_sqrt
           nlinarith only [mi]
         calc f i ≤ ((1:ℝ)/m)/(m:ℝ)^2 := by
                apply div_le_div₀ (by positivity) (max_le (during i hi) (by positivity)) (by positivity) rt
              _ = _ := by field_simp
       _ ≤ 1 := by
         simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]
         rw [mul_one_div,div_le_one (by positivity : 0 < (m:ℝ)^3)]
         exact_mod_cast (show t+1-a ≤ m^3 by omega)

private theorem row_lower {m t : ℕ} (hm : 0 < m) (ht : m^4 ≤ t) (ht2 : t<2*m^4) :
    (1:ℝ)/m ≤ threshold (stair m) 1 t - stair m t := by
  let L := m^4
  let B := m^3
  let j := (t-L)/B
  let a := L+j*B
  have bp : 0 < B := by dsimp [B]; positivity
  have mp : 0 < (m:ℝ) := by exact_mod_cast hm
  have id : m*B=L := by dsimp [B,L]; ring
  have jm : j < m := (Nat.div_lt_iff_lt_mul bp).mpr (by rw [id]; dsimp [L]; omega)
  have ja : (j:ℝ)+1 ≤ m := by exact_mod_cast (show j+1 ≤ m from jm)
  let x := 1-(j:ℝ)/m
  have xp : x ∈ Set.Icc (0:ℝ) 1 := by
    have : (j:ℝ)/m ≤ 1 := (div_le_one mp).mpr (by linarith)
    dsimp [x]; constructor <;> linarith [show 0 ≤ (j:ℝ)/m by positivity]
  have val : stair m t=1-((j:ℝ)+1)/m := by
    dsimp [stair,index]
    rw [if_neg (by omega : ¬t < m^4)]
    change max 0 (1-((j+1:ℕ):ℝ)/m)=_
    push_cast
    exact max_eq_right (sub_nonneg.mpr ((div_le_one mp).mpr ja))
  have len : t+1 ≤ a+B := by
    have large := Nat.lt_mul_div_succ (t-L) bp
    change t-L < B*(j+1) at large
    rw [mul_add,mul_comm B j,mul_one] at large
    change L ≤ t at ht
    dsimp [a]; omega
  have costBound : cost (stair m) t x ≤ 1 := by
    apply block_budget (a:=a) hm (by dsimp [a,L]; omega) len
    · intro i hi
      have ix : index m i ≤ j := by
        by_cases pre : i<L
        · simp [index,show i < m^4 from pre]
        · have ij : i-L<j*B := by dsimp [a] at hi; omega
          have := (Nat.div_lt_iff_lt_mul bp).mpr ij
          simpa [index,show ¬i < m^4 from pre,B,L] using this
      apply le_trans _ (le_max_right ..)
      exact sub_le_sub_left (div_le_div_of_nonneg_right (by exact_mod_cast ix) mp.le) 1
    · intro i hi
      have it : i ≤ t := by have := (mem_Ico.mp hi).2; omega
      have := (stair_properties m).2 it
      rw [val] at this
      dsimp [x]
      have e : ((j:ℝ)+1)/m=(j:ℝ)/m+1/m := add_div ..
      linarith
  have good := level_fits (stair_properties m).1 (by norm_num : (0:ℝ)<1) t xp costBound
  rw [val]
  dsimp [x] at good
  rw [add_div]
  linarith

theorem lower (m T : ℕ) (hm : 0 < m) (bound : 2*m^4 ≤ T) :
    ∃ p : ℕ → ℝ, UnitData p ∧ Antitone p ∧ (m:ℝ)^3 ≤ excess p 1 T := by
  obtain ⟨unit,anti⟩ := stair_properties m
  refine ⟨stair m,unit,anti,?_⟩
  have nonneg (i : ℕ) : 0 ≤ threshold (stair m) 1 i-stair m i := by
    apply sub_nonneg.mpr
    apply level_fits unit (by norm_num) i (unit i)
    have z : cost (stair m) i (stair m i)=0 := by
      apply sum_eq_zero; intro j hj
      rw [max_eq_right (sub_nonpos.mpr (anti (by have := mem_range.mp hj; omega))),zero_div]
    linarith
  calc (m:ℝ)^3 = ∑ _i ∈ Ico (m^4) (2*m^4), (1:ℝ)/m := by
         simp only [sum_const,Nat.card_Ico,nsmul_eq_mul,show 2*m^4-m^4=m^4 by omega]
         push_cast; field_simp
       _ ≤ ∑ i ∈ Ico (m^4) (2*m^4), (threshold (stair m) 1 i-stair m i) :=
         sum_le_sum fun i hi => row_lower hm (mem_Ico.mp hi).1 (mem_Ico.mp hi).2
       _ ≤ excess (stair m) 1 T := sum_le_sum_of_subset_of_nonneg
         (fun i hi => mem_range.mpr ((mem_Ico.mp hi).2.trans_le bound)) (fun i _ _ => nonneg i)

end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Filter Topology

private theorem exponential_dominates (d N : ℕ) (A : ℝ) :
    ∃ j : ℕ, N ≤ j ∧ 1 ≤ j ∧ A*(j:ℝ)^d < 2^j := by
  have conv : Tendsto (fun j : ℕ => A*((j:ℝ)^d/(2:ℝ)^j)) atTop (𝓝 (A*0)) :=
    tendsto_const_nhds.mul (tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num))
  have small := conv.eventually_lt_const (show A*0<1 by simp)
  obtain ⟨j,all⟩ := ((eventually_ge_atTop N).and ((eventually_ge_atTop 1).and small)).exists
  refine ⟨j,all.1,all.2.1,?_⟩
  have h := all.2.2
  rw [←mul_div_assoc,div_lt_one (by positivity)] at h
  exact h

theorem refute (d : ℕ) (K : ℝ) (N : ℕ) :
    ∃ T : ℕ, N ≤ T ∧ ∃ p : ℕ → ℝ, UnitData p ∧ Antitone p ∧
      K*Real.sqrt T*(1+Real.log T)^d < excess p 1 T := by
  let A := max K 1
  have ap : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right ..)
  obtain ⟨j,jn,jp,jlarge⟩ := exponential_dominates d N (A*2*6^d)
  let m : ℕ := 2^j
  let T : ℕ := 2*m^4
  have mp : 0 < m := by dsimp [m]; positivity
  have mr : 0 < (m:ℝ) := by exact_mod_cast mp
  have jm : j ≤ m := Nat.le_of_lt (Nat.lt_two_pow_self)
  have m4 : m ≤ m^4 := Nat.le_self_pow (by decide) m
  obtain ⟨p,u,anti,lowerBound⟩ := lower m T mp (by rfl)
  refine ⟨T,jn.trans (jm.trans (m4.trans (by dsimp [T]; omega))),p,u,anti,lt_of_lt_of_le ?_ lowerBound⟩
  have eq : (T:ℝ)=2*(m:ℝ)^4 := by dsimp [T]; push_cast; rfl
  have pow_eq : (m:ℝ)=(2:ℝ)^j := by dsimp [m]; push_cast; rfl
  have jr : (1:ℝ) ≤ j := by exact_mod_cast jp
  have logtwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have log_bound : 1+Real.log (T:ℝ) ≤ 6*(j:ℝ) := by
    rw [eq,Real.log_mul (by norm_num) (by positivity),Real.log_pow,pow_eq,Real.log_pow]
    push_cast; nlinarith [mul_le_mul_of_nonneg_left logtwo (by positivity : 0≤(j:ℝ))]
  have Tpos : 0 < T := by dsimp [T]; positivity
  have tpos : 1 ≤ (T:ℝ) := by exact_mod_cast Tpos
  have logpos : 0 ≤ 1+Real.log (T:ℝ) := by linarith [Real.log_nonneg tpos]
  have sqrt_bound : Real.sqrt (T:ℝ) ≤ 2*(m:ℝ)^2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [eq]; nlinarith [sq_nonneg ((m:ℝ)^2)]
  calc K*Real.sqrt (T:ℝ)*(1+Real.log (T:ℝ))^d
         ≤ (A*(2*(m:ℝ)^2))*(6*(j:ℝ))^d := by
            apply mul_le_mul _ (pow_le_pow_left₀ logpos log_bound d) (pow_nonneg logpos d) (by positivity)
            exact mul_le_mul (le_max_left ..) sqrt_bound (Real.sqrt_nonneg _) ap.le
       _ = (A*2*6^d*(j:ℝ)^d)*(m:ℝ)^2 := by rw [mul_pow]; ring
       _ < (m:ℝ)*(m:ℝ)^2 := mul_lt_mul_of_pos_right (jlarge.trans_eq pow_eq.symm) (by positivity)
       _ = _ := by ring
end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset

private theorem scale_data {p : ℕ → ℝ} (h : UnitData p) {c : ℝ} (cp : 0 < c) (c1 : c ≤ 1) :
    UnitData (fun i => c*p i) := fun i => ⟨mul_nonneg cp.le (h i).1,
      (mul_le_mul_of_nonneg_left (h i).2 cp.le).trans (by simpa using c1)⟩

private theorem scale_excess {p : ℕ → ℝ} (h : UnitData p) {C c : ℝ} (cp : 0 < c)
    (c1 : c ≤ 1) (cC : c ≤ C) (T : ℕ) :
    c*excess p 1 T ≤ excess (fun i => c*p i) C T := by
  unfold excess
  rw [mul_sum]
  apply sum_le_sum; intro i _
  let b := threshold p 1 i
  have spec := (cap_spec h (by norm_num : (0:ℝ)<1) i).1
  have scale : cost (fun i => c*p i) i (c*b)=c*cost p i b := by
    unfold cost; rw [mul_sum]; apply sum_congr rfl; intro k _
    rw [←mul_sub,show max (c*(b-p k)) 0=c*max (b-p k) 0 by
      rw [mul_max_of_nonneg _ _ cp.le,mul_zero],mul_div_assoc]
  have eq := level_fits (scale_data h cp c1) (cp.trans_le cC) i
    (x:=c*b) ⟨mul_nonneg cp.le spec.1.1,(mul_le_mul_of_nonneg_left spec.1.2 cp.le).trans (by simpa using c1)⟩
    (scale ▸ (show c*cost p i b ≤ C from (mul_le_mul_of_nonneg_left spec.2 cp.le).trans
      (by simpa using cC)))
  dsimp [b] at eq
  linarith only [eq,mul_sub c (threshold p 1 i) (p i)]

theorem lower_all (C : ℝ) (hC : 0<C) (m T : ℕ) (hm : 0 < m) (bound : 2*m^4 ≤ T) :
    ∃ p : ℕ → ℝ, UnitData p ∧ Antitone p ∧ min C 1*(m:ℝ)^3 ≤ excess p C T := by
  let c := min C 1
  have cp : 0 < c := lt_min hC zero_lt_one
  obtain ⟨p,unit,anti,base⟩ := lower m T hm bound
  exact ⟨fun i => c*p i,scale_data unit cp (min_le_right ..),fun _ _ h => mul_le_mul_of_nonneg_left (anti h) cp.le,
    (mul_le_mul_of_nonneg_left base cp.le).trans (scale_excess unit cp (min_le_right ..) (min_le_left ..) T)⟩

theorem refute_all (C : ℝ) (hC : 0<C) (d : ℕ) (K : ℝ) (N : ℕ) :
    ∃ T : ℕ, N ≤ T ∧ ∃ p : ℕ → ℝ, UnitData p ∧ Antitone p ∧
      K*C*Real.sqrt T*(1+Real.log T)^d < excess p C T := by
  let c := min C 1
  have cp : 0 < c := lt_min hC zero_lt_one
  obtain ⟨T,large,p,unit,anti,hit⟩ := refute d (K*C/c) N
  refine ⟨T,large,fun i => c*p i,scale_data unit cp (min_le_right ..),
    fun _ _ h => mul_le_mul_of_nonneg_left (anti h) cp.le,?_⟩
  have bound := (mul_lt_mul_of_pos_left hit cp).trans_le
    (scale_excess unit cp (min_le_right ..) (min_le_left ..) T)
  have eq : K*C*Real.sqrt T*(1+Real.log T)^d = c*(K*C/c*Real.sqrt T*(1+Real.log T)^d) := by
    field_simp [cp.ne']
  exact eq ▸ bound
end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset

private noncomputable def wt (k : ℕ) : ℝ := Real.sqrt (k+1)
private noncomputable def mass (n : ℕ) : ℝ := ∑ k ∈ range n, wt k
private noncomputable def profile (T k : ℕ) : ℝ := 1-mass (min (k+1) T)/mass T

private theorem wt_pos (k : ℕ) : 0 < wt k := by unfold wt; positivity
private theorem wt_mono : Monotone wt := by
  intro i j h; apply Real.sqrt_le_sqrt; exact_mod_cast Nat.add_le_add_right h 1

private theorem mass_mono : Monotone mass := by
  intro i j h; exact sum_le_sum_of_subset_of_nonneg (range_mono h) (fun k _ _ => (wt_pos k).le)

private theorem mass_nonneg (n : ℕ) : 0 ≤ mass n := sum_nonneg fun k _ => (wt_pos k).le

private theorem mass_pos {n : ℕ} (hn : 0 < n) : 0 < mass n := by
  exact lt_of_lt_of_le (by simpa [mass] using wt_pos 0 : 0 < mass 1) (mass_mono hn)

private theorem mass_increment {a i j : ℕ} (ai : a ≤ i) (ij : i ≤ j) :
    ((j-i:ℕ):ℝ)*wt a ≤ mass j-mass i := by
  unfold mass
  rw [← sum_Ico_eq_sub _ ij]
  calc _ = ∑ _ ∈ Ico i j, wt a := by simp
       _ ≤ _ := sum_le_sum fun k hk => wt_mono (ai.trans (mem_Ico.mp hk).1)

private theorem mass_gap {i j T : ℕ} (ij : i ≤ j) (jT : j ≤ T) :
    mass j-mass i ≤ ((j-i:ℕ):ℝ)*Real.sqrt T := by
  unfold mass
  rw [← sum_Ico_eq_sub _ ij]
  calc _ ≤ ∑ _ ∈ Ico i j, Real.sqrt (T:ℝ) := by
         apply sum_le_sum; intro k hk
         have : k+1 ≤ T := (mem_Ico.mp hk).2.trans_le jT
         apply Real.sqrt_le_sqrt; exact_mod_cast this
       _ = _ := by simp

private theorem profile_prop (T : ℕ) : UnitData (profile T) ∧ Antitone (profile T) := by
  constructor
  · intro i; constructor
    · apply sub_nonneg.mpr
      by_cases h : T=0
      · simp [h,mass]
      · exact (div_le_one (mass_pos (Nat.pos_of_ne_zero h))).mpr (mass_mono (min_le_right ..))
    · exact sub_le_self _ (div_nonneg (mass_nonneg _) (mass_nonneg _))
  · intro i j h
    apply sub_le_sub_left; apply div_le_div_of_nonneg_right _ (mass_nonneg _)
    exact mass_mono (min_le_min_right T (Nat.succ_le_succ h))

private theorem triangle (w : ℕ) :
    (∑ j ∈ range w, ((j:ℝ)+1)) = (w:ℝ)*(w+1)/2 := by
  induction w with
  | zero => norm_num
  | succ w ih => rw [sum_range_succ,ih]; push_cast; ring

private theorem ramp_row {T t w : ℕ} {C : ℝ} (hw : 0 < w) (ws : w ≤ t+1) (tT : t < T)
    (budget : (w:ℝ)*(w+1) ≤ 2*C*mass T) (hC : 0 < C) :
    (w:ℝ)*wt (t+1-w)/mass T ≤ threshold (profile T) C t-profile T t := by
  let a := t+1-w
  let B := mass T
  let x := profile T t + (w:ℝ)*wt a/B
  have ha : a+w=t+1 := by dsimp [a]; omega
  have hB : 0 < B := mass_pos (by omega)
  have val {k : ℕ} (hk : k<T) : profile T k=1-mass (k+1)/B := by
    simp [profile,B,min_eq_left (show k+1 ≤ T from hk)]
  have span := mass_increment (a:=a) (i:=a) (j:=t+1) le_rfl (by omega)
  have len : t+1-a=w := by omega
  rw [len] at span
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg ((profile_prop T).1 t).1 (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (wt_pos a).le) hB.le)
    · dsimp only [x]; rw [val tT]
      have : (w:ℝ)*wt a/B ≤ mass (t+1)/B := div_le_div_of_nonneg_right (by linarith [mass_nonneg a]) hB.le
      linarith
  let f (i : ℕ) := max (x-profile T i) 0 / wt i
  have early {i : ℕ} (hi : i<a) : f i=0 := by
    have before := mass_mono (show i+1 ≤ a by omega)
    have sub : x-profile T i ≤ 0 := by
      dsimp only [x]; rw [val tT,val (by omega)]
      field_simp [hB.ne']; linarith
    simp [f,max_eq_right sub]
  have trim : (∑ k ∈ Ico a (t+1), f k) = ∑ k ∈ range (t+1), f k := by
    apply sum_subset (fun i h => mem_range.mpr (mem_Ico.mp h).2)
    intro i hi hni
    apply early
    have := mem_range.mp hi
    by_contra! h; exact hni (mem_Ico.mpr ⟨h,this⟩)
  have costx : cost (profile T) t x ≤ C := by
    change (∑ i ∈ range (t+1), f i) ≤ C
    rw [← trim,sum_Ico_eq_sum_range,len]
    calc _ ≤ ∑ j ∈ range w, (((j:ℝ)+1)/B) := by
           apply sum_le_sum; intro j hj
           have jw := mem_range.mp hj
           let i := a+j
           have it : i ≤ t := by dsimp [i]; omega
           have gap := mass_increment (a:=a) (i:=i+1) (j:=t+1) (by dsimp [i]; omega) (by omega)
           have count : ((t+1-(i+1):ℕ):ℝ)=(w:ℝ)-((j:ℝ)+1) := by
             rw [show t+1-(i+1)=w-(j+1) by dsimp [i]; omega,Nat.cast_sub (by omega)]; push_cast; rfl
           rw [count] at gap
           have num : x-profile T i ≤ ((j:ℝ)+1)*wt a/B := by
             dsimp only [x]; rw [val tT,val (by omega)]
             field_simp [hB.ne']; linarith
           have cmp : wt a ≤ wt i := wt_mono (by dsimp [i]; omega)
           change max (x-profile T i) 0 / wt i ≤ _
           apply (div_le_iff₀ (wt_pos i)).mpr
           apply max_le
           · calc _ ≤ ((j:ℝ)+1)*wt a/B := num
                  _ = (((j:ℝ)+1)/B)*wt a := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left cmp (by positivity)
           · positivity [wt_pos i]
         _ = (w:ℝ)*(w+1)/2/B := by rw [←sum_div,triangle]
         _ ≤ C := (div_le_iff₀ hB).mpr (by change _ ≤ 2*C*B at budget; linarith)
  have hit := level_fits (profile_prop T).1 hC t hx costx
  change profile T t+(w:ℝ)*wt a/B ≤ _ at hit
  linarith

private theorem profile_gap_nonneg (T : ℕ) {C : ℝ} (hC : 0<C) (i : ℕ) :
    0 ≤ threshold (profile T) C i-profile T i := by
  apply sub_nonneg.mpr
  apply level_fits (profile_prop T).1 hC i ((profile_prop T).1 i)
  calc _ = 0 := by
         apply sum_eq_zero; intro j hj
         rw [max_eq_right (sub_nonpos.mpr ((profile_prop T).2 (by have := mem_range.mp hj; omega))),zero_div]
       _ ≤ _ := hC.le

private theorem profile_bound {T w : ℕ} {C : ℝ} (hw : 0 < w) (wT : w ≤ T)
    (budget : (w:ℝ)*(w+1) ≤ 2*C*mass T) (hC : 0 < C) :
    (w:ℝ)*mass (T+1-w)/mass T ≤ excess (profile T) C T := by
  let a := w-1
  have hlen : T-a = T+1-w := by dsimp [a]; omega
  calc _ = ∑ t ∈ Ico a T, ((w:ℝ)*wt (t+1-w)/mass T) := by
         rw [sum_Ico_eq_sum_range,hlen]
         simp only [show ∀ i, a+i+1-w=i by dsimp [a]; omega]
         rw [←sum_div,←mul_sum]; rfl
       _ ≤ ∑ t ∈ Ico a T, (threshold (profile T) C t-profile T t) := by
         apply sum_le_sum; intro t ht
         apply ramp_row hw _ (mem_Ico.mp ht).2 budget hC
         have := (mem_Ico.mp ht).1; dsimp [a] at this; omega
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun t ht => mem_range.mpr (mem_Ico.mp ht).2)
         (fun t _ _ => profile_gap_nonneg T hC t)

theorem sharp_lower (C : ℝ) (hC : 0 < C) (T : ℕ) :
    ∃ p : ℕ → ℝ, UnitData p ∧ Antitone p ∧
      Real.sqrt (2*C*(∑ k ∈ range T, Real.sqrt (k+1)))-2-2*C*Real.sqrt T ≤ excess p C T := by
  refine ⟨profile T,(profile_prop T).1,(profile_prop T).2,?_⟩
  let B := mass T
  let F := Real.sqrt (2*C*B)
  change F-2-2*C*Real.sqrt T ≤ _
  have Fs : F^2=2*C*B := Real.sq_sqrt (mul_nonneg (by positivity) (mass_nonneg T))
  have low : 0 ≤ excess (profile T) C T := sum_nonneg fun i _ => profile_gap_nonneg T hC i
  by_cases small : F<2
  · linarith [mul_nonneg (show 0 ≤ 2*C by positivity) (Real.sqrt_nonneg (T:ℝ))]
  have Fp : 0<F := by linarith
  by_cases large : (T:ℝ)<F
  · have cap := mass_gap (i:=0) (j:=T) (T:=T) (Nat.zero_le _) le_rfl
    simp only [mass,range_zero,sum_empty,sub_zero,Nat.sub_zero] at cap
    change B ≤ (T:ℝ)*Real.sqrt T at cap
    have h := mul_le_mul_of_nonneg_left (cap.trans (mul_le_mul_of_nonneg_right large.le (Real.sqrt_nonneg _)))
      (show 0≤2*C by positivity)
    have : F ≤ 2*C*Real.sqrt T := (le_of_mul_le_mul_right (a:=F) (by nlinarith only [h,Fs]) Fp)
    linarith
  have fp := Nat.floor_le Fp.le
  have fn := Nat.lt_floor_add_one F
  let w := ⌊F⌋₊-1
  have two : 2 ≤ ⌊F⌋₊ := (Nat.le_floor (by linarith : (2:ℝ) ≤ F))
  have hw : 0<w := by dsimp [w]; omega
  have wc : (w:ℝ)=(⌊F⌋₊:ℝ)-1 := by
    dsimp [w]; rw [Nat.cast_sub (by omega)]; norm_num
  have wF : (w:ℝ) ≤ F := by linarith
  have wT : w ≤ T := by exact_mod_cast (show (w:ℝ) ≤ T by linarith)
  have hB : 0<B := mass_pos (by omega)
  have budget : (w:ℝ)*(w+1) ≤ 2*C*mass T := by
    rw [←Fs]
    simpa [pow_two] using (mul_le_mul wF (show (w:ℝ)+1 ≤ F by linarith)
      (show 0 ≤ (w:ℝ)+1 by positivity) Fp.le)
  have hit := profile_bound hw wT budget hC
  have gap := mass_gap (i:=T+1-w) (j:=T) (T:=T) (by omega) le_rfl
  have wl : ((T-(T+1-w):ℕ):ℝ) ≤ w := by exact_mod_cast (show T-(T+1-w) ≤ w by omega)
  have gap' := gap.trans (mul_le_mul_of_nonneg_right wl (Real.sqrt_nonneg _))
  have sq : (w:ℝ)*(w:ℝ) ≤ 2*C*B := by
    rw [← Fs,pow_two]; exact mul_le_mul wF wF (Nat.cast_nonneg _) Fp.le
  have scaled := mul_le_mul_of_nonneg_right sq (Real.sqrt_nonneg (T:ℝ))
  have weighted := mul_le_mul_of_nonneg_left gap' (Nat.cast_nonneg w : 0 ≤ (w:ℝ))
  have valid : (w:ℝ)-2*C*Real.sqrt T ≤ (w:ℝ)*mass (T+1-w)/B := by
    apply (le_div_iff₀ hB).mpr
    change (w:ℝ)*(B-mass (T+1-w)) ≤ _ at weighted
    nlinarith only [weighted,scaled]
  have short : F-2 ≤ (w:ℝ) := by linarith
  linarith only [valid,hit,short]
end UpperSum

namespace UpperSum
open OMA.S_mo_476612 Finset Filter Topology

noncomputable def worst (C : ℝ) (T : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ p, UnitData p ∧ excess p C T = s}

theorem worst_bounds {C : ℝ} (hC : 0<C) (T : ℕ) :
    let F := Real.sqrt (2*C*(∑ k ∈ range T, Real.sqrt (k+1)))
    F-2-2*C*Real.sqrt T ≤ worst C T ∧ worst C T ≤ F := by
  intro F
  let s := {s : ℝ | ∃ p, UnitData p ∧ excess p C T = s}
  have upper (v : ℝ) (hv : v∈s) : v ≤ F := by
    obtain ⟨p,hp,rfl⟩ := hv; exact energy_upper hp hC T
  obtain ⟨p,hp,_,hit⟩ := sharp_lower C hC T
  have mem : excess p C T ∈ s := ⟨p,hp,rfl⟩
  exact ⟨hit.trans (le_csSup ⟨F,upper⟩ mem),csSup_le ⟨_,mem⟩ upper⟩

private theorem sqrt_sum_bounds (T : ℕ) :
    let H := ∑ k ∈ range T, Real.sqrt (k+1)
    let R := Real.sqrt (T:ℝ)
    2*(T:ℝ)*R ≤ 3*H ∧ 3*H ≤ 2*(T:ℝ)*R+3*R := by
  induction T with
  | zero => simp
  | succ t ih =>
    let a := Real.sqrt (t:ℝ)
    let b := Real.sqrt ((t:ℝ)+1)
    have ap : 0≤a := Real.sqrt_nonneg _
    have bp : 0≤b := Real.sqrt_nonneg _
    have ab : a≤b := Real.sqrt_le_sqrt (by linarith)
    have aa : a^2=(t:ℝ) := Real.sq_sqrt (by positivity)
    have bb : b^2=(t:ℝ)+1 := Real.sq_sqrt (by positivity)
    have id : b^2-a^2=1 := by linarith
    have h₁ : 3*a ≤ 2*((t+1:ℝ)*b-(t:ℝ)*a) := by
      rw [← bb,← aa,← one_mul (3*a),← id]
      nlinarith only [mul_nonneg (sq_nonneg (b-a)) (by linarith : 0≤2*b+a)]
    have h₂ : 2*((t+1:ℝ)*b-(t:ℝ)*a) ≤ 3*b := by
      rw [← bb,← aa,← one_mul (3*b),← id]
      nlinarith only [mul_nonneg (sq_nonneg (b-a)) (by linarith : 0≤b+2*a)]
    dsimp only
    rw [sum_range_succ,Nat.cast_succ]
    change _ ≤ 3*(_+b) ∧ 3*(_+b) ≤ 2*((t:ℝ)+1)*b+3*b
    obtain ⟨ih₁,ih₂⟩ := ih
    change 2*(t:ℝ)*a ≤ _ at ih₁
    change _ ≤ 2*(t:ℝ)*a+3*a at ih₂
    change 2*((t:ℝ)+1)*b ≤ _ ∧ _
    constructor <;> linarith only [ih₁,ih₂,h₁,h₂]

private theorem normalized_bounds {C : ℝ} (hC : 0<C) {T : ℕ} (hT : 1≤T) :
    let A := 2*Real.sqrt (C/3)
    let D := 2+2*C+Real.sqrt (2*C)
    let e := D*(T:ℝ)^(-(1/4:ℝ))
    A-e ≤ worst C T/(T:ℝ)^(3/4:ℝ) ∧ worst C T/(T:ℝ)^(3/4:ℝ) ≤ A+e := by
  let R := Real.sqrt (T:ℝ)
  let Q := (T:ℝ)^(3/4:ℝ)
  let H := ∑ k ∈ range T, Real.sqrt (k+1)
  let F := Real.sqrt (2*C*H)
  let A := 2*Real.sqrt (C/3)
  let D := 2+2*C+Real.sqrt (2*C)
  have tp : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have R1 : 1≤R := by simpa [R] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ T by exact_mod_cast hT)
  have qp : 0<Q := Real.rpow_pos_of_pos tp _
  have qsq : Q^2=(T:ℝ)*R := by
    calc Q^2 = Q^(2:ℝ) := by norm_cast
         _ = (T:ℝ)^((3/4:ℝ)*2) := (Real.rpow_mul tp.le _ _).symm
         _ = (T:ℝ)^((1:ℝ)+1/2) := by norm_num
         _ = (T:ℝ)*R := by rw [Real.rpow_add tp,Real.rpow_one,←Real.sqrt_eq_rpow]
  have eQ : (T:ℝ)^(-(1/4:ℝ))*Q=R := by
    rw [show (T:ℝ)^(-(1/4:ℝ))*Q=(T:ℝ)^(-(1/4:ℝ)+3/4) from (Real.rpow_add tp _ _).symm]
    norm_num [R,Real.sqrt_eq_rpow]
  have rp : 0 ≤ R := by linarith
  have fs : F^2=2*C*H := Real.sq_sqrt (mul_nonneg (by positivity)
    (sum_nonneg fun k _ => Real.sqrt_nonneg _))
  have ap : 0≤A := by dsimp [A]; positivity
  have asq : A^2=4*C/3 := by
    dsimp [A]; rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
  have aq : (A*Q)^2=(4*C/3)*((T:ℝ)*R) := by rw [mul_pow,asq,qsq]
  have hS := sqrt_sum_bounds T
  change 2*(T:ℝ)*R ≤ 3*H ∧ 3*H ≤ 2*(T:ℝ)*R+3*R at hS
  have lower : A*Q ≤ F := by
    have sqle : (A*Q)^2 ≤ F^2 := by rw [aq,fs]; nlinarith only [mul_le_mul_of_nonneg_left hS.1 hC.le]
    exact le_of_sq_le_sq sqle (Real.sqrt_nonneg _)
  let X := Real.sqrt (2*C)
  have xp : 0 ≤ X := Real.sqrt_nonneg _
  have xs : X^2=2*C := Real.sq_sqrt (by positivity)
  have upper : F ≤ A*Q+X*R := by
    have du : 0 ≤ 2*(A*Q)*(X*R) := by positivity
    have ur := mul_le_mul_of_nonneg_left hS.2 hC.le
    have hi : (X*R)^2 ≥ 2*C*R := by
      rw [mul_pow,xs]
      exact mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg rp (sub_nonneg.mpr R1)]) (by positivity)
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [hi,du,aq,fs,ur]
  have ds : 2+2*C ≤ D := by dsimp [D,X] at *; linarith
  have dx : X ≤ D := by dsimp [D,X]; linarith
  have wb := worst_bounds hC T
  change F-2-2*C*R ≤ worst C T ∧ worst C T ≤ F at wb
  change A-D*(T:ℝ)^(-(1/4:ℝ)) ≤ worst C T/Q ∧ worst C T/Q ≤ A+D*(T:ℝ)^(-(1/4:ℝ))
  constructor
  · apply (le_div_iff₀ qp).mpr
    rw [sub_mul,mul_assoc D _ Q,eQ]
    linarith only [wb.1,lower,mul_le_mul_of_nonneg_right ds rp,R1]
  · apply (div_le_iff₀ qp).mpr
    rw [add_mul,mul_assoc D _ Q,eQ]
    linarith only [wb.2,upper,mul_le_mul_of_nonneg_right dx rp]

/-- The leading coefficient of the worst possible discrete excess. -/
theorem worst_limit (C : ℝ) (hC : 0<C) :
    Tendsto (fun T : ℕ => worst C T/(T:ℝ)^(3/4:ℝ)) atTop (𝓝 (2*Real.sqrt (C/3))) := by
  let A := 2*Real.sqrt (C/3)
  let D := 2+2*C+Real.sqrt (2*C)
  have e : Tendsto (fun T : ℕ => D*(T:ℝ)^(-(1/4:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=D)).mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop)
  have lim₁ := (tendsto_const_nhds (x:=A) (f:=atTop)).sub e
  have lim₂ := (tendsto_const_nhds (x:=A) (f:=atTop)).add e
  simp only [sub_zero,add_zero] at lim₁ lim₂
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lim₁ lim₂
  · filter_upwards [eventually_ge_atTop 1] with T hT using (normalized_bounds hC hT).1
  · filter_upwards [eventually_ge_atTop 1] with T hT using (normalized_bounds hC hT).2
end UpperSum


theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_476612.main) := by
  intro conjecture
  obtain ⟨d,K,_,N,bound⟩ := conjecture 1 zero_lt_one
  obtain ⟨T,hT,p,hp,_,hit⟩ := UpperSum.refute_all 1 zero_lt_one d K N
  exact (not_lt_of_ge (bound T hT p hp)) hit
