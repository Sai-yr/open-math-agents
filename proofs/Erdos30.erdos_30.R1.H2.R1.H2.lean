import OMAReductions.R_Erdos30_erdos_30_R1_H2_R1
import Mathlib

/-!
# Distribution of a cyclic Sidon template in the ordinary integer interval

Slide a short window around the cyclic group. Two distinct translates of a
modular Sidon ruler overlap at most once, giving a second moment bound for
the count in the window. Moving a weight by less than the window length only
crosses one of its two jumps on two short bands. Averaging this envelope and
using Cauchy–Schwarz shows that the two weights in the edit inequality have
total score at most three times the modulus times the number of marks.
The explicit threshold is chosen for convenience.
-/

namespace SidonDistribution
open Finset

private theorem sumShift {m : ℕ} [NeZero m] (f : ZMod m → ℤ) (a : ZMod m) :
    ∑ y, f (y-a) = ∑ y, f y := by
  simpa [sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-a)) f

/-- Second moment of a window moving around a circle. The hypothesis is
the uniqueness of each nonzero modular difference. -/
theorem variance {m : ℕ} [NeZero m] (D T : Finset (ZMod m))
    (unique : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ d ∈ D, a-b=c-d → a≠b → a=c)
    (dense : m ≤ D.card^2) :
    let I (z : ZMod m) : ℤ := if z∈D then 1 else 0
    let f (y : ZMod m) := ∑ t ∈ T, I (y-t)
    (∑ y : ZMod m, |(m : ℤ)*f y-D.card*T.card|)^2 ≤
      (m : ℤ)^3*D.card*T.card := by
  classical
  intro I f
  have weights (t : ZMod m) : ∑ y, I (y-t) = D.card := by
    rw [sumShift]; simp [I]
  have mean : ∑ y, f y = (D.card : ℤ)*T.card := by
    dsimp [f]; rw [sum_comm]; simp [weights,mul_comm]
  have pair (s t : ZMod m) : ∑ y, I (y-s)*I (y-t) ≤
      (if s=t then (D.card : ℤ) else 0)+1 := by
    by_cases h : s=t
    · subst t
      simp only [if_true]
      have eq : ∀ y, I (y-s)*I (y-s) = I (y-s) := by
        intro y; dsimp [I]; split <;> norm_num
      simp [eq,weights]
    · rw [if_neg h,zero_add]
      let P (y : ZMod m) : Prop := y-s∈D ∧ y-t∈D
      have eq (y : ZMod m) : I (y-s)*I (y-t) = if P y then 1 else 0 := by
        dsimp [I,P]; split <;> split <;> simp_all
      simp only [eq]
      rw [show (∑ y : ZMod m, if P y then (1 : ℤ) else 0) = ((univ.filter P).card : ℤ) by exact sum_boole P univ]
      exact_mod_cast (show (univ.filter P).card ≤ 1 by
        apply card_le_one.mpr
        intro y hy z hz
        have yy := (mem_filter.mp hy).2
        have zz := (mem_filter.mp hz).2
        have id := unique (y-s) yy.1 (y-t) yy.2 (z-s) zz.1 (z-t) zz.2
          (by abel) (fun e => h (by simpa using e))
        exact sub_left_injective id)
  have bound : ∑ y, (f y)^2 ≤ (T.card : ℤ)*D.card+T.card^2 := by
    calc
      _ = ∑ s ∈ T, ∑ t ∈ T, ∑ y, I (y-s)*I (y-t) := by
        simp only [f,pow_two,sum_mul,mul_sum]
        rw [sum_comm]
        apply sum_congr rfl; intro s _; rw [sum_comm]; simp only [mul_comm]
      _ ≤ ∑ s ∈ T, ∑ t ∈ T, ((if s=t then (D.card : ℤ) else 0)+1) :=
        sum_le_sum (fun s _ => sum_le_sum (fun t _ => pair s t))
      _ = _ := by simp [sum_add_distrib,pow_two,add_comm,mul_comm]
  have centered : ∑ y, ((m : ℤ)*f y-D.card*T.card)^2 ≤ (m : ℤ)^2*D.card*T.card := by
    have eq (y : ZMod m) : ((m : ℤ)*f y-D.card*T.card)^2 =
        (m : ℤ)^2*(f y)^2-(2*m*D.card*T.card)*f y+((D.card : ℤ)*T.card)^2 := by ring
    simp only [eq,sum_add_distrib,sum_sub_distrib,← mul_sum,mean,sum_const,card_univ,
      ZMod.card,nsmul_eq_mul]
    have dm : (m : ℤ) ≤ (D.card : ℤ)^2 := by exact_mod_cast dense
    nlinarith [mul_le_mul_of_nonneg_left bound (sq_nonneg (m : ℤ)),
      mul_le_mul_of_nonneg_right dm (show 0 ≤ (m : ℤ)*T.card^2 by positivity)]
  have cs := sum_mul_sq_le_sq_mul_sq (R := ℤ) (univ : Finset (ZMod m))
    (fun _ => 1) (fun y => |(m : ℤ)*f y-D.card*T.card|)
  simp only [one_mul,one_pow,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one,sq_abs] at cs
  nlinarith [mul_le_mul_of_nonneg_left centered (Nat.cast_nonneg (α := ℤ) m)]

end SidonDistribution

namespace SidonDistribution
open Finset

def p (m x y : ℤ) := if y<x then x-2*y else 2*y-x-m
def g (m y : ℤ) := max 0 (m-4*min y (m-y))

theorem valSum {m : ℕ} [NeZero m] (f : ℕ → ℤ) :
    ∑ y : ZMod m, f y.val = ∑ i ∈ range m, f i := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n+1)

private theorem sums (n : ℕ) :
    2*(∑ i ∈ range n, (i : ℤ))=(n : ℤ)*(n-1) ∧
    6*(∑ i ∈ range n, (i : ℤ)^2)=(n : ℤ)*(n-1)*(2*n-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [sum_range_succ,Nat.cast_succ]; constructor <;> nlinarith [ih.1,ih.2]

private theorem splitRange (x t : ℕ) :
    ∑ i ∈ range (x+t), p (x+t) x i = (x : ℤ)-t := by
  rw [sum_range_add]
  have low : ∑ i ∈ range x, p (x+t) x i = ∑ i ∈ range x, ((x : ℤ)-2*i) := by
    apply sum_congr rfl
    intro i hi; have lt : (i : ℤ)<x := by exact_mod_cast mem_range.mp hi
    simp [p,lt]
  have high : ∑ i ∈ range t, p (x+t) x (↑(x+i) : ℤ) =
      ∑ i ∈ range t, (2*(i : ℤ)-t) := by
    apply sum_congr rfl; intro i _
    rw [Nat.cast_add, p,if_neg (by omega)]; ring
  rw [low,high]
  simp only [sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul]
  nlinarith [(sums x).1,(sums t).1]

theorem pSum {m : ℕ} [NeZero m] (x : ZMod m) :
    ∑ y : ZMod m, p m x.val y.val ≤ m := by
  rw [valSum (fun j => p m x.val j)]
  have hx := ZMod.val_lt x
  have eq : x.val+(m-x.val)=m := by omega
  have alg := splitRange x.val (m-x.val)
  rw [eq] at alg
  have eq' : (x.val : ℤ)+(↑(m-x.val) : ℤ)=m := by exact_mod_cast eq
  rw [eq'] at alg
  omega

theorem gSum {m : ℕ} [NeZero m] :
    3*(∑ y : ZMod m, g m y.val) ≤ (m : ℤ)^2+2 := by
  rw [valSum (fun j => g m j)]
  have pos : (0 : ℤ) < m := by exact_mod_cast NeZero.pos m
  have edge {y : ℕ} (hy : y < m) : (m : ℤ)*g m y ≤ ((m : ℤ)-2*y)^2 := by
    unfold g; cases le_total (y : ℤ) ((m : ℤ)-y) with
    | inl h => rw [min_eq_left h]; rcases le_total (0 : ℤ) (m-4*(y : ℤ)) with z|z
               · rw [max_eq_right z]; nlinarith [sq_nonneg (y : ℤ)]
               · rw [max_eq_left z]; nlinarith [sq_nonneg ((m : ℤ)-2*y)]
    | inr h => rw [min_eq_right h]; rcases le_total (0 : ℤ) (m-4*((m : ℤ)-y)) with z|z
               · rw [max_eq_right z]; nlinarith [sq_nonneg ((m : ℤ)-y)]
               · rw [max_eq_left z]; nlinarith [sq_nonneg ((m : ℤ)-2*y)]
  have s := sum_le_sum (s := range m) (fun i hi => edge (mem_range.mp hi))
  have poly (i : ℕ) : ((m : ℤ)-2*i)^2=(m : ℤ)^2-4*m*i+4*(i : ℤ)^2 := by ring
  simp only [poly,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at s
  apply (mul_le_mul_iff_of_pos_left pos).mp
  nlinarith [(sums m).2,congrArg (fun z : ℤ => (m : ℤ)*z) (sums m).1]

def band (a t y : ℕ) : ℤ := if a≤y ∧ y<a+t then 1 else 0

theorem bandSum {m : ℕ} [NeZero m] (a t : ℕ) :
    ∑ y : ZMod m, band a t y.val ≤ t := by
  rw [valSum (band a t)]
  unfold band
  rw [sum_boole]
  exact_mod_cast (show ((range m).filter (fun y => a≤y ∧ y<a+t)).card ≤ t by
    have h : (range m).filter (fun y => a≤y ∧ y<a+t) ⊆ Ico a (a+t) :=
      fun i hi => mem_Ico.mpr (mem_filter.mp hi).2
    simpa using card_le_card h)

def score (m : ℕ) (x y : ℕ) : ℤ := 16*p m x y+8*g m y

def envelope (m x t y : ℕ) : ℤ :=
  score m x y+64*t+40*m*(band 0 t y+band x t y)

/-- Shifting to the right by less than t only crosses a jump on one of two
short bands. This upper envelope works for every translate of the ruler. -/
theorem shiftBound {m : ℕ} [NeZero m] (x a u : ZMod m) (t : ℕ) (hu : u.val<t) :
    score m x.val a.val ≤ envelope m x.val t (a+u).val := by
  have hx := ZMod.val_lt x
  have ha := ZMod.val_lt a
  have hs := ZMod.val_lt (a+u)
  unfold score envelope score p g band
  by_cases wrap : a.val+u.val < m
  · rw [ZMod.val_add_of_lt wrap]
    push_cast
    split_ifs <;> omega
  · rw [ZMod.val_add_of_le (by omega)]
    push_cast [Nat.cast_sub (by omega : m ≤ a.val+u.val)]
    split_ifs <;> omega

theorem envelopeAbs {m : ℕ} [NeZero m] (x y : ZMod m) {t : ℕ} (ht : t ≤ m) :
    |envelope m x.val t y.val| ≤ 200*(m : ℤ) := by
  have := ZMod.val_lt x; have := ZMod.val_lt y
  unfold envelope score p g band
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

theorem envelopeSum {m : ℕ} [NeZero m] (x : ZMod m) (t : ℕ) :
    3*(∑ y : ZMod m, envelope m x.val t y.val) ≤
      8*(m : ℤ)^2+48*m+16+432*m*t := by
  simp only [envelope,score,sum_add_distrib,← mul_sum,sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  have be := add_le_add (bandSum (m := m) 0 t) (bandSum (m := m) x.val t)
  have mp : (0 : ℤ) ≤ m := Nat.cast_nonneg _
  nlinarith [pSum x,gSum (m := m),mul_le_mul_of_nonneg_left be mp]

end SidonDistribution

namespace SidonDistribution
open Finset

private theorem largeArithmetic {m k t L S : ℤ} (hm : 1000000000000 ≤ m)
    (hk : 1000000000000 ≤ k) (ht : 0<t) (lowerT : m≤8192*t) (upperT : 4096*t ≤ m)
    (hL : 0≤L) (var : L^2 ≤ m^3*k*t) (weighted : 3*m*t*S ≤
      k*t*(8*m^2+48*m+16+432*m*t)+600*m*L) : S ≤ 3*m*k := by
  have pm : 0 < m := by omega
  have pk : 0 < k := by omega
  have mk : 4194304*m ≤ k*t := by
    nlinarith [mul_le_mul_of_nonneg_right hk ht.le]
  have norm : 2048*L ≤ k*m*t := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [mul_le_mul_of_nonneg_right mk (show 0 ≤ m^2*k*t by positivity)]
  have aux : 2*(48*m+16+432*m*t) ≤ m^2 := by
    nlinarith [mul_le_mul_of_nonneg_left upperT pm.le,mul_le_mul_of_nonneg_right hm pm.le]
  apply (mul_le_mul_iff_of_pos_left (show 0 < 3*m*t by positivity)).mp
  nlinarith [mul_le_mul_of_nonneg_right aux (show 0≤k*t by positivity),
    mul_le_mul_of_nonneg_left norm (show 0 ≤ m by omega),mul_nonneg (show 0 ≤ m by omega) hL]

theorem largeProfile {m : ℕ} [NeZero m] (D : Finset (ZMod m)) (x : ZMod m)
    (large : 1000000000000 ≤ D.card) (sidon : IsSidon (D : Set (ZMod m)))
    (covers : ∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b-c=z) :
    16*(∑ d ∈ D, p m x.val d.val) + 8*(∑ d ∈ D, g m d.val) ≤ 3*(m : ℤ)*D.card := by
  classical
  have dm : D.card ≤ m := by simpa using D.card_le_univ
  have md : m ≤ D.card^2 := by
    have incl : (univ : Finset (ZMod m)) ⊆ (D ×ˢ D).image (fun z => z.1-z.2) := by
      intro z _
      by_cases zero : z=0
      · obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<D.card)
        exact mem_image.mpr ⟨(a,a),mem_product.mpr ⟨ha,ha⟩,by simp [zero]⟩
      · obtain ⟨a,ha,b,hb,h⟩ := covers z zero
        exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,h⟩
    simpa [pow_two] using (card_le_card incl).trans card_image_le
  let t := m/4096
  have tp : 0<t := by dsimp [t]; omega
  have tm : t ≤ m := by dsimp [t]; omega
  let T : Finset (ZMod m) := (range t).image Nat.cast
  have tc : T.card=t := by
    rw [show T=(range t).image Nat.cast from rfl,card_image_of_injOn,card_range]
    intro i hi j hj h
    have e := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ((mem_range.mp hi).trans_le tm),
      ZMod.val_natCast_of_lt ((mem_range.mp hj).trans_le tm)] at e
  have inT {u : ZMod m} (hu : u∈T) : u.val<t := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    rwa [ZMod.val_natCast_of_lt ((mem_range.mp hi).trans_le tm),← mem_range]
  let I (y : ZMod m) : ℤ := if y∈D then 1 else 0
  let f (y : ZMod m) := ∑ u ∈ T, I (y-u)
  let F (y : ZMod m) := envelope m x.val t y.val
  let S (a : ZMod m) := score m x.val a.val
  let L := ∑ y : ZMod m, |(m : ℤ)*f y-D.card*t|
  have var := variance D T (fun a ha b hb c hc d hd eq ne => by
    have sum : a+d=c+b := by linear_combination eq
    rcases sidon _ ha _ hc _ hd _ hb sum with h|h
    · exact h.1
    · exact (ne h.1).elim) md
  dsimp only at var
  rw [tc] at var
  have var' : L^2 ≤ (m : ℤ)^3*D.card*t := var
  have sm (u : ZMod m) : ∑ y, I (y-u)*F y = ∑ a ∈ D, F (a+u) := by
    calc
      _ = ∑ a, I a*F (a+u) := by
        simpa using (Equiv.sum_comp (Equiv.addRight u) (fun y => I (y-u)*F y)).symm
      _ = _ := by simp [I,ite_mul]
  have lower : (t : ℤ)*(∑ a ∈ D, S a) ≤ ∑ y, f y*F y := by
    calc
      _ = ∑ u ∈ T, ∑ a ∈ D, S a := by simp [tc]
      _ ≤ ∑ u ∈ T, ∑ a ∈ D, F (a+u) :=
        sum_le_sum (fun u hu => sum_le_sum (fun a _ => shiftBound x a u t (inT hu)))
      _ = _ := by symm; simp only [f,sum_mul]; rw [sum_comm]; simp only [sm]
  have top (y : ZMod m) : (m : ℤ)*(f y*F y) ≤
      (D.card : ℤ)*t*F y+200*m*|(m : ℤ)*f y-D.card*t| := by
    have le := le_abs_self (((m : ℤ)*f y-D.card*t)*F y)
    rw [abs_mul] at le
    nlinarith [mul_le_mul_of_nonneg_left (envelopeAbs x y tm) (abs_nonneg ((m : ℤ)*f y-D.card*t))]
  have upper := sum_le_sum (s := univ) (fun y _ => top y)
  simp only [sum_add_distrib,← mul_sum] at upper
  have nonneg : 0≤L := sum_nonneg (fun _ _ => abs_nonneg _)
  have comb : 3*(m : ℤ)*t*(∑ a ∈ D, S a) ≤
      (D.card : ℤ)*t*(8*m^2+48*m+16+432*m*t)+600*m*L := by
    have h := envelopeSum x t
    change 3*(∑ y, F y) ≤ _ at h
    change (m : ℤ)*(∑ y, f y*F y) ≤ (D.card : ℤ)*t*(∑ y, F y)+200*m*L at upper
    nlinarith [mul_le_mul_of_nonneg_left lower (Nat.cast_nonneg (α := ℤ) m),
      mul_le_mul_of_nonneg_left h (show 0 ≤ (D.card : ℤ)*t by positivity)]
  have result := largeArithmetic (by exact_mod_cast large.trans dm) (by exact_mod_cast large)
    (by exact_mod_cast tp) (by exact_mod_cast (show m≤8192*t by dsimp [t]; omega))
    (by exact_mod_cast (show 4096*t ≤ m by dsimp [t]; omega)) nonneg var' comb
  simpa [S,score,sum_add_distrib,← mul_sum] using result

end SidonDistribution

namespace SidonDistribution
open Finset

/-- Given the finite obstruction from the first step, every new integer mark
costs at least one in sixty-four marks of the original perfect template. -/
theorem deletionDistance (finiteBound : OMA.R_Erdos30_erdos_30_R1_H2_R1.H1)
    {m : ℕ} [NeZero m] (D : Finset (ZMod m)) (klarge : 1000000000000 ≤ D.card)
    (hD : IsSidon (D : Set (ZMod m)))
    (full : ∀ z : ZMod m, z ≠ 0 → ∃ b ∈ D, ∃ c ∈ D, b-c=z)
    (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (x : ZMod m) (hx : x ∉ D) (hxA : x.val ∈ A) :
    D.card ≤ 64*(D.filter (fun d => d.val ∉ A)).card := by
  have h := finiteBound m D A x hD full hA hx hxA
  have inc := largeProfile D x klarge hD full
  have pp (d : ZMod m) : (if d.val<x.val then (x.val : ℤ)-2*d.val else 2*(d.val : ℤ)-x.val-m)
      = p m x.val d.val := by
    unfold p; by_cases lt : d.val<x.val
    · rw [if_pos lt,if_pos (by exact_mod_cast lt)]
    · rw [if_neg lt,if_neg (by exact_mod_cast lt)]
  dsimp only at h
  simp only [pp] at h
  change (m : ℤ)*D.card ≤ 16*m*((D.filter (fun d => d.val∉A)).card : ℤ) +
    4*(∑ d ∈ D, p m x.val d.val) + 2*(∑ d ∈ D, g m d.val) at h
  by_contra! contrary
  have lt : (64 : ℤ)*(D.filter (fun d => d.val∉A)).card < D.card := by exact_mod_cast contrary
  nlinarith [mul_lt_mul_of_pos_left lt (show (0 : ℤ) < m by exact_mod_cast NeZero.pos m)]

end SidonDistribution

theorem OMA.solution : OMA.R_Erdos30_erdos_30_R1_H2_R1.H2 := by
  refine ⟨1000000000000,?_⟩
  intro m _ D x large hD full p g
  have pp (d : ZMod m) : p d = SidonDistribution.p m x.val d.val := by
    dsimp only [p,SidonDistribution.p]; by_cases lt : d.val<x.val
    · rw [if_pos lt,if_pos (by exact_mod_cast lt)]
    · rw [if_neg lt,if_neg (by exact_mod_cast lt)]
  simp only [pp]
  exact SidonDistribution.largeProfile D x large hD full
