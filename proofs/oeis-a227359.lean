import OMAStatements.S_oeis_a227359
/-!
# Simultaneous omissions of the binary digit-sum maps

Inside a dyadic block, the two maps translate their low-word images by
opposite high-digit weights. The block overlap is therefore a correlation
at twice the high weight. Averaging over free high bits gives a binomial
kernel with small variation under translation.

The minus-map sends the four inputs 4a,...,4a+3 to just two successive
values, starting at 4a minus the binary weight of a. On short progressions
of stride two this gives density one half, with an explicit error. Smoothing
the correlation and controlling both block boundaries gives the same
factor one half at arbitrary cutoffs.
-/
namespace A227359Proof
open OMA.S_oeis_a227359 Finset Filter Topology
open scoped Classical

@[local simp] private theorem w_zero : weight 0 = 0 := rfl
@[local simp] private theorem w_even (n : ℕ) : weight (2*n)=weight n := by simp [weight]
@[local simp] private theorem w_odd (n : ℕ) : weight (2*n+1)=weight n+1 := by simp [weight]

private theorem w_split (b k u : ℕ) (hu : u<2^k) : weight (b*2^k+u)=weight b+weight u := by
  induction k generalizing u with
  | zero =>
    have h : u=0 := by simpa using hu
    simp [h]
  | succ k ih =>
    have hhalf : u/2<2^k := by rw [pow_succ] at hu; omega
    have hmod := Nat.mod_two_eq_zero_or_one u
    rcases hmod with h | h
    · have he : u=2*(u/2) := by omega
      have he' : b*2^(k+1)+u = 2*(b*2^k+u/2) := by
        rw [pow_succ]; nlinarith [he]
      rw [he',w_even,ih _ hhalf,he,w_even]
      simp
    · have he : u=2*(u/2)+1 := by omega
      have he' : b*2^(k+1)+u = 2*(b*2^k+u/2)+1 := by
        rw [pow_succ]; nlinarith [he]
      rw [he',w_odd,ih _ hhalf,he,w_odd]
      simp [add_assoc, show (2*(u/2)+1)/2=u/2 by omega]

private theorem w_bound (k u : ℕ) (hu : u<2^k) : weight u ≤ k := by
  induction k generalizing u with
  | zero =>
    have : u=0 := by simpa using hu
    simp [this]
  | succ k ih =>
    have ht : u/2<2^k := by rw [pow_succ] at hu; omega
    have h := ih _ ht
    rcases Nat.mod_two_eq_zero_or_one u with r|r
    · have hh : u=2*(u/2) := by omega
      calc weight u = weight (u/2) := by conv_lhs => rw [hh,w_even]
           _ ≤ k+1 := by omega
    · have hh : u=2*(u/2)+1 := by omega
      calc weight u = weight (u/2)+1 := by conv_lhs => rw [hh,w_odd]
           _ ≤ k+1 := by omega

private theorem w_le (u : ℕ) : weight u ≤ u := w_bound u u Nat.lt_two_pow_self

private theorem preimage_bound (u : ℕ) : u ≤ 2*(u-weight u)+2 := by
  obtain ⟨m,hm|hm⟩ := Nat.even_or_odd' u
  · rw [hm,w_even]; have := w_le m; omega
  · rw [hm,w_odd]; have := w_le m; omega

private theorem w_succ (u : ℕ) : weight (u+1) ≤ weight u+1 := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    rcases Nat.mod_two_eq_zero_or_one u with h|h
    · have hu : u=2*(u/2) := by omega
      conv_lhs => rw [hu,w_odd]
      conv_rhs => rw [hu,w_even]
    · have hu : u=2*(u/2)+1 := by omega
      have hu' : u+1=2*(u/2+1) := by omega
      have hh := ih (u/2) (by omega)
      rw [hu',w_even]
      conv_rhs => rw [hu,w_odd]
      omega

private def z (j : ℕ) := 2*j-weight j

private theorem z_strict : StrictMono z := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := w_succ j
  have := w_le j
  unfold z; omega

private theorem minus_even (j : ℕ) : 2*j-weight (2*j)=z j := by simp [z]
private theorem minus_odd (j : ℕ) : 2*j+1-weight (2*j+1)=z j := by simp [z]


private def bin (r : ℕ) (f : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ range (r+1), (r.choose j : ℝ)*f (s+j)

private theorem central_square (r : ℕ) :
    ((r:ℝ)+1) * (r.centralBinom:ℝ)^2 ≤ 16^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : ((r:ℝ)+1)*(r+1).centralBinom = 2*(2*r+1)*(r.centralBinom:ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ r
    have hx : (r:ℝ)+1>0 := by positivity
    have hy : ((r:ℝ)+2)*(2*(2*r+1))^2 ≤ 16*(r+1)^3 := by
      nlinarith [show (0:ℝ)≤r by positivity]
    push_cast; rw [pow_succ]
    apply (le_of_mul_le_mul_right (a:=((r:ℝ)+1)^2) ?_ (by positivity))
    calc
      _ = (r+2)*(((r:ℝ)+1)*(r+1).centralBinom)^2 := by ring
      _ = (r+2)*(2*(2*(r:ℝ)+1))^2 * (r.centralBinom:ℝ)^2 := by rw [h]; ring
      _ ≤ 16*(r+1)^3 * (r.centralBinom:ℝ)^2 := mul_le_mul_of_nonneg_right hy (by positivity)
      _ = (r+1)^2*(((r:ℝ)+1)*(r.centralBinom:ℝ)^2)*16 := by ring
      _ ≤ _ := by
        rw [show (16:ℝ)^(r+1)=16^r*16 by ring]
        nlinarith [mul_le_mul_of_nonneg_left ih (sq_nonneg ((r:ℝ)+1))]

/-- Sum of consecutive differences with a nonnegative, nondecreasing weight.
The boundary bound uses no regularity of the test function. -/
private theorem forward_bounds (a f : ℕ → ℝ) (N : ℕ) (A : ℝ)
    (hf : ∀ j, 0≤f j ∧ f j≤A) (h0 : 0≤a 0)
    (hm : ∀ j, j<N → a j ≤ a (j+1)) :
    let z := ∑ j ∈ range N, a j*(f (j+1)-f j)
    a N*f N - a N*A ≤ z ∧ z ≤ a N*f N := by
  induction N with
  | zero =>
    simp only [sum_range_zero]
    constructor
    · nlinarith [(mul_le_mul_of_nonneg_left (hf 0).2 h0)]
    · positivity [h0,(hf 0).1]
  | succ N ih =>
    have H := ih (fun j hj=>hm j (by omega))
    have inc := sub_nonneg.mpr (hm N (by omega))
    simp only [sum_range_succ] at *
    obtain ⟨l,u⟩ := H
    constructor
    · nlinarith [mul_nonneg inc (sub_nonneg.mpr (hf (N+1)).2)]
    · nlinarith [mul_nonneg inc (hf (N+1)).1]


private theorem half_bound (r : ℕ) (f : ℕ → ℝ) (A : ℝ) (hf : ∀ i, 0≤f i ∧ f i≤A) :
    |∑ j ∈ range r, ((2*r).choose j : ℝ)*(f (j+1)-f j)| ≤ (r.centralBinom:ℝ)*A := by
  let a : ℕ → ℝ := fun j=> (2*r).choose j
  have hm : ∀j, j<r → a j ≤ a (j+1) := by
    intro j hj
    dsimp [a]
    exact_mod_cast Nat.choose_le_succ_of_lt_half_left (n:=2*r) (r:=j) (by omega)
  have h := forward_bounds a f r A hf (by simp [a]) hm
  have hp : 0≤a r := by dsimp [a]; positivity
  have h0 := mul_nonneg hp (hf r).1
  have h1 := mul_le_mul_of_nonneg_left (hf r).2 hp
  change |∑ j ∈ range r, a j*(f (j+1)-f j)| ≤ a r*A
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

private theorem bin_shift_one (r : ℕ) (f : ℕ → ℝ) (s : ℕ) (A : ℝ)
    (hf : ∀ i, 0≤f i ∧ f i≤A) :
    |bin (2*r) f (s+1)-bin (2*r) f s| ≤ 3*(r.centralBinom:ℝ)*A := by
  let d : ℕ → ℝ := fun i => ((2*r).choose i:ℝ)*(f (s+i+1)-f (s+i))
  let g : ℕ → ℝ := fun i => f (s+(2*r+1-i))
  let v : ℕ → ℝ := fun i => ((2*r).choose i:ℝ)*(g (i+1)-g i)
  have hl := half_bound r (fun j=>f (s+j)) A (fun j=>hf _)
  have hr := half_bound r g A (fun j=>hf _)
  have hl' : |∑i ∈ range r, d i| ≤ (r.centralBinom:ℝ)*A := by
    simpa [d,add_assoc] using hl
  have hr' : |∑i ∈ range r, v i| ≤ (r.centralBinom:ℝ)*A := hr
  have hm : |d r| ≤ (r.centralBinom:ℝ)*A := by
    dsimp [d]; rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((2*r).choose r:ℝ))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact abs_le.mpr ⟨by linarith [(hf (s+r+1)).1,(hf (s+r)).2],
      by linarith [(hf (s+r+1)).2,(hf (s+r)).1]⟩
  have reflect : ∑ i ∈ range r, d (r+(i+1)) = -(∑ i ∈ range r, v i) := by
    rw [←sum_range_reflect (fun i=>d (r+(i+1))) r,←sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have id1 : r+(r-1-i+1)=2*r-i := by omega
    dsimp [d,v,g]
    rw [id1,Nat.choose_symm (by omega : i≤2*r)]
    rw [show s+(2*r-i)+1=s+(2*r+1-i) by omega,
      show 2*r+1-(i+1)=2*r-i by omega]
    ring
  have total : bin (2*r) f (s+1)-bin (2*r) f s =
      (∑i ∈ range r, d i) + d r - (∑i ∈ range r, v i) := by
    unfold bin; rw [←sum_sub_distrib]
    calc
      _ = ∑i ∈ range (2*r+1), d i := by
        apply sum_congr rfl; intro i _
        dsimp [d]; rw [show s+1+i=s+i+1 by omega]; ring
      _ = _ := by
        rw [show 2*r+1=r+(r+1) by omega,sum_range_add,sum_range_succ' (fun j=>d (r+j)),reflect]
        simp; ring
  rw [total]
  have h1 := abs_add_le (∑ i ∈ range r,d i) (d r)
  have h2 := abs_sub ((∑ i ∈ range r,d i)+d r) (∑ i ∈ range r,v i)
  linarith

private theorem bin_shift (r : ℕ) (f : ℕ → ℝ) (s t : ℕ) (A : ℝ)
    (hf : ∀ i, 0≤f i ∧ f i≤A) :
    |bin (2*r) f (s+t)-bin (2*r) f s| ≤ t*(3*(r.centralBinom:ℝ)*A) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := bin_shift_one r f (s+t) A hf
    have h2 := abs_sub_le (bin (2*r) f (s+t+1)) (bin (2*r) f (s+t)) (bin (2*r) f s)
    push_cast; rw [show s+(t+1)=s+t+1 by omega]; linarith


private theorem bin_zero (f : ℕ → ℝ) (s : ℕ) : bin 0 f s=f s := by simp [bin]

private theorem bin_succ (r : ℕ) (f : ℕ → ℝ) (s : ℕ) :
    bin (r+1) f s = bin r f s + bin r f (s+1) := by
  unfold bin
  rw [sum_range_succ' (fun i=>((r+1).choose i:ℝ)*f (s+i)),
    sum_range_succ' (fun i=>(r.choose i:ℝ)*f (s+i))]
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,add_zero,Nat.choose_succ_succ,
    Nat.cast_add,add_mul,sum_add_distrib]
  rw [sum_range_succ (fun i=>(r.choose (i+1):ℝ)*f (s+(i+1)))]
  have eq : ∑ i ∈ range (r+1), (r.choose i:ℝ)*f (s+(i+1)) =
      ∑ i ∈ range (r+1), (r.choose i:ℝ)*f (s+1+i) := by
    apply sum_congr rfl; intro i _; rw [show s+(i+1)=s+1+i by omega]
  rw [eq]; simp; ring

private theorem weights_sum (r : ℕ) (f : ℕ → ℝ) (s : ℕ) :
    ∑ u ∈ range (2^r), f (s+weight u) = bin r f s := by
  induction r generalizing s with
  | zero => simp [bin]
  | succ r ih =>
    rw [pow_succ, Nat.mul_two,sum_range_add,bin_succ,ih]
    congr 1
    rw [←ih]
    apply sum_congr rfl; intro i hi
    have h := w_split 1 r i (mem_range.mp hi)
    simp only [one_mul,show weight 1=1 by rfl] at h
    rw [h]; congr 1; omega

private theorem sum_by_blocks (q M : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ range (q*M), f n =
      ∑ b ∈ range q, ∑ u ∈ range M, f (b*M+u) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.add_mul,one_mul,sum_range_add,ih,sum_range_succ]

private theorem sum_bin_weights (r : ℕ) :
    ∑ j ∈ range (r+1), (r.choose j:ℝ) = (2:ℝ)^r := by
  exact_mod_cast Nat.sum_range_choose r


private noncomputable def mark (p : Prop) : ℝ := if p then 1 else 0

private theorem mark_mem (p : Prop) : 0 ≤ mark p ∧ mark p≤1 := by unfold mark; split_ifs <;> norm_num

private noncomputable def plusL (k x : ℕ) := mark (¬∃u<2^k, u+weight u=x)
private noncomputable def minusL (k x : ℕ) := mark (¬∃u<2^k, u-weight u=x)

private noncomputable def actual (joint : Bool) (x : ℕ) :=
  if joint then mark (missed x) else mark (self x)

private noncomputable def low (joint : Bool) (k h x : ℕ) :=
  if joint then plusL k x * minusL k (x+2*h) else plusL k x

private theorem prod_unit {a b : ℝ} (ha : 0≤a ∧ a≤1) (hb : 0≤b ∧ b≤1) :
    0≤a*b ∧ a*b≤1 := ⟨mul_nonneg ha.1 hb.1,by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hb.2)]⟩

private theorem actual_mem (j : Bool) (x : ℕ) : 0≤actual j x ∧ actual j x≤1 := by
  cases j <;> exact mark_mem _

private theorem low_mem (j : Bool) (k h x : ℕ) : 0≤low j k h x ∧ low j k h x≤1 := by
  cases j
  · exact mark_mem _
  · exact prod_unit (mark_mem _) (mark_mem _)

private theorem shift_sum {f : ℕ → ℝ} (hf : ∀x,0≤f x ∧ f x≤1) (N h : ℕ) :
    |(∑ x ∈ range N, f (h+x))-(∑ x ∈ range N, f x)| ≤ h := by
  have main : (∑ x ∈ range h, f x)+(∑ x ∈ range N, f (h+x)) =
      (∑ x ∈ range N, f x)+(∑ x ∈ range h, f (N+x)) := by
    rw [←sum_range_add,←sum_range_add,add_comm h N]
  have bounded (t : ℕ) :
      0≤∑x ∈ range h, f (t+x) ∧ (∑x ∈ range h,f (t+x))≤h := by
    refine ⟨sum_nonneg (fun i _=>(hf _).1),?_⟩
    calc _ ≤ ∑ _x ∈ range h,(1:ℝ) := sum_le_sum (fun i _=>(hf _).2)
         _ = _ := by simp
  have h₁ := bounded 0; simp only [zero_add] at h₁
  have h₂ := bounded N
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem edges {f g : ℕ → ℝ} (N a b : ℕ)
    (hf : ∀x,0≤f x ∧ f x≤1) (hg : ∀x,0≤g x ∧ g x≤1)
    (hfg : ∀x, a≤x → x+b<N → f x=g x) :
    |(∑x ∈ range N,f x)-(∑x ∈ range N,g x)| ≤ (a+b : ℕ) := by
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ range N, |f x-g x| := abs_sum_le_sum_abs .. 
    _ ≤ ∑ x ∈ range N, ((if x<a then 1 else 0) + (if N≤x+b then 1 else 0)) := by
      apply sum_le_sum; intro x hx
      by_cases hl : x<a <;> by_cases hr : N≤x+b <;> simp only [* ,ite_true,ite_false]
      all_goals first | (rw [hfg x (by omega) (by omega)]; simp) |
        (apply abs_le.mpr; constructor <;> linarith [(hf x).1,(hf x).2,(hg x).1,(hg x).2])
    _ ≤ _ := by
      rw [sum_add_distrib,sum_boole,sum_boole]
      have H1 : (range N).filter (fun x=>x<a) ⊆ range a := fun x hx=>mem_range.mpr (mem_filter.mp hx).2
      have H2 : (range N).filter (fun x=>N≤x+b) ⊆ Ico (N-b) N := by
        intro x hx; obtain ⟨hr,hb⟩:=mem_filter.mp hx
        exact mem_Ico.mpr ⟨by omega,mem_range.mp hr⟩
      have hl := card_le_card H1
      have hr := card_le_card H2
      simp only [card_range,Nat.card_Ico] at hl hr
      exact_mod_cast (show _ ≤ a+b by omega)

private theorem interior {D k b x : ℕ} (ht : (b+1)*2^k≤2^D) (lo : D+2≤x)
    (hi : x+weight b+(D+2)<2^k) (joint : Bool) :
    actual joint (b*2^k+weight b+x) = low joint k (weight b) x := by
  let M:=2^k
  let A:=b*M
  let H:=weight b
  let y:=A+H+x
  have hy : y<2^D := by dsimp [y,A,M,H]; rw [Nat.add_mul] at ht; omega
  have mapform (u : ℕ) (hu : A≤u) (hv : u<A+M) :
      weight u=H+weight (u-A) := by
    have e := w_split b k (u-A) (by omega)
    have eq : b*2^k+(u-A)=u := by change A+(u-A)=u; omega
    rw [eq] at e; exact e
  have up : (∃u : ℕ, u+weight u=y) ↔ ∃v<M, v+weight v=x := by
    constructor
    · rintro ⟨u,he⟩
      have wu:=w_bound D u (by omega)
      have hl : A≤u := by dsimp [y] at he; omega
      have hr : u<A+M := by change x+H+(D+2)<M at hi; dsimp [y] at he; omega
      refine ⟨u-A,by omega,?_⟩; rw [mapform _ hl hr] at he; dsimp [y] at he; omega
    · rintro ⟨v,hv,he⟩
      refine ⟨A+v,?_⟩
      have e := w_split b k v hv; change weight (A+v)=H+weight v at e
      rw [e]; dsimp [y]; omega
  have down : (∃u : ℕ, u-weight u=y) ↔ ∃v<M, v-weight v=x+2*H := by
    constructor
    · rintro ⟨u,he⟩
      have ub := preimage_bound u
      have hp : 2^(D+2)=4*2^D := by rw [pow_add]; ring
      have wu := w_bound (D+2) u (by rw [hp]; have := Nat.two_pow_pos D; omega)
      have hl : A≤u := by dsimp [y] at he; omega
      have hr : u<A+M := by change x+H+(D+2)<M at hi; dsimp [y] at he; omega
      have wv := w_le (u-A)
      refine ⟨u-A,by omega,?_⟩; rw [mapform _ hl hr] at he; dsimp [y] at he; omega
    · rintro ⟨v,hv,he⟩
      refine ⟨A+v,?_⟩
      have e := w_split b k v hv; change weight (A+v)=H+weight v at e
      have wm := w_le v
      have wu := w_le (A+v)
      rw [e] at wu ⊢; dsimp [y]; omega
  cases joint
  · change mark (¬ ∃ u, u+weight u=y) = mark (¬∃v<M, v+weight v=x)
    rw [up]
  · change mark ((¬ ∃ u, u+weight u=y) ∧ (¬∃u, u-weight u=y)) =
      mark (¬∃v<M, v+weight v=x) * mark (¬∃v<M, v-weight v=x+2*H)
    rw [up,down]; unfold mark; split_ifs <;> simp_all


private def lowGen (k y : ℕ) : Prop := ∃ u < 2^k, u-weight u = y

private def base (a : ℕ) := 4*a-weight a

private def rep (x a : ℕ) := base a+(x+base a)%2

private theorem base_jump (a : ℕ) : base a+3≤base (a+1) := by
  unfold base; have := w_le a; have := w_succ a; omega

private theorem rep_inc (x : ℕ) : StrictMono (rep x) := by
  apply strictMono_nat_of_lt_succ; intro a
  have := base_jump a
  unfold rep; omega

private theorem low_pairs (k y : ℕ) :
    lowGen (k+2) y ↔ ∃ a<2^k, y=base a ∨ y=base a+1 := by
  have hpow : 2^(k+2)=4*2^k := by rw [pow_add]; ring
  constructor
  · rintro ⟨u,hu,rfl⟩
    rw [hpow] at hu
    let a := u/4
    have ha : a<2^k := by dsimp [a]; omega
    refine ⟨a,ha,?_⟩
    have hdec : u=4*a+u%4 := by dsimp [a]; omega
    have hw : weight u=weight a+weight (u%4) := by
      have h := w_split a 2 (u%4) (by norm_num; omega)
      convert h using 1; congr 1; omega
    rw [hw]
    have wa := w_le a
    unfold base
    rcases (show u%4=0 ∨ u%4=1 ∨ u%4=2 ∨ u%4=3 by omega) with h|h|h|h <;>
      rw [h] <;> simp only [show weight 0=0 by decide, show weight 1=1 by decide,
        show weight 2=1 by decide, show weight 3=2 by decide] <;> omega
  · rintro ⟨a,ha,he|he⟩
    · refine ⟨4*a,by rw [hpow]; omega,?_⟩
      have hw : weight (4*a)=weight a := by
        rw [show 4*a=2*(2*a) by ring,w_even,w_even]
      simpa [hw,base] using he.symm
    · refine ⟨4*a+2,by rw [hpow]; omega,?_⟩
      have hw : weight (4*a+2)=weight a+1 := by
        rw [show 4*a+2=2*(2*a+1) by ring,w_even,w_odd]
      have := w_le a
      rw [hw,he]; unfold base; omega

private theorem gen_iff_rep (k x t : ℕ) :
    lowGen (k+2) (x+2*t) ↔ ∃ a<2^k, rep x a=x+2*t := by
  rw [low_pairs]
  constructor
  · rintro ⟨a,ha,h|h⟩ <;> refine ⟨a,ha,?_⟩ <;> unfold rep <;> omega
  · rintro ⟨a,ha,h⟩
    refine ⟨a,ha,?_⟩
    unfold rep at h; omega

private def repHits (k x L : ℕ) := (range (2^k)).filter (fun a=>x≤rep x a ∧ rep x a<x+2*L)

private theorem hits_eq (k x L : ℕ) :
    ((range L).filter (fun t=>lowGen (k+2) (x+2*t))).card = (repHits k x L).card := by
  symm
  apply card_bij (fun a _=>(rep x a-x)/2)
  · intro a ha
    obtain ⟨ha,h1,h2⟩ := mem_filter.mp ha
    have hp : (rep x a)%2=x%2 := by unfold rep; omega
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),
      (gen_iff_rep _ _ _).mpr ⟨a,mem_range.mp ha,by omega⟩⟩
  · intro a ha b hb h
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    have e1 : rep x a % 2=x%2 := by unfold rep; omega
    have e2 : rep x b % 2=x%2 := by unfold rep; omega
    exact (rep_inc x).injective (by omega)
  · intro t ht
    obtain ⟨ht,h⟩ := mem_filter.mp ht
    obtain ⟨a,ha,he⟩ := (gen_iff_rep _ _ _).mp h
    have ht' := mem_range.mp ht
    exact ⟨a,mem_filter.mpr ⟨mem_range.mpr ha,by omega,by omega⟩,by omega⟩

private theorem local_hit_bounds (k x L : ℕ) (hx : x+2*L≤4*2^k) :
    let C := ((range L).filter (fun t=>lowGen (k+2) (x+2*t))).card
    2*L ≤ 4*C + (k+8) ∧ 4*C ≤ 2*L + (k+8) := by
  rw [hits_eq]; dsimp only
  have lo : Ico ((x+k+3)/4) ((x+2*L)/4) ⊆ repHits k x L := by
    intro a ha
    obtain ⟨ha,hb⟩ := mem_Ico.mp ha
    have hg : a<2^k := by omega
    have hw := w_bound k a hg
    have hw' := w_le a
    apply mem_filter.mpr
    refine ⟨mem_range.mpr hg,?_,?_⟩ <;> unfold rep base <;> omega
  have hi : repHits k x L ⊆ Ico ((x-1)/4) ((x+2*L+k)/4+1) := by
    intro a ha
    obtain ⟨ha,h1,h2⟩ := mem_filter.mp ha
    have hw := w_bound k a (mem_range.mp ha)
    have hw' := w_le a
    unfold rep base at h1 h2
    apply mem_Ico.mpr; omega
  have cl := card_le_card lo
  have cu := card_le_card hi
  rw [Nat.card_Ico] at cl cu
  omega


private noncomputable def block (j : Bool) (k h : ℕ) := ∑ x ∈ range (2^k), low j k h x

private noncomputable def plusBlock (k : ℕ) := ∑ x ∈ range (2^k), plusL k x

private noncomputable def alpha (k : ℕ) := plusBlock k/(2:ℝ)^k

private theorem block_false (k h : ℕ) : block false k h = plusBlock k := rfl

private theorem block_unit (j : Bool) (k h : ℕ) : 0 ≤ block j k h ∧ block j k h ≤ (2:ℝ)^k := by
  constructor
  · exact sum_nonneg (fun i _=>(low_mem j k h i).1)
  · calc _ ≤ ∑ _i ∈ range (2^k), (1:ℝ) := sum_le_sum (fun i _=>(low_mem j k h i).2)
         _ = _ := by simp

private theorem plus_exact (k x : ℕ) (hx : x<2^k) : actual false x=plusL k x := by
  change mark (¬∃u, u+weight u=x) = mark (¬∃u<2^k, u+weight u=x)
  congr 1; apply propext; apply not_congr
  constructor
  · rintro ⟨u,he⟩; exact ⟨u,by omega,he⟩
  · rintro ⟨u,_,he⟩; exact ⟨u,he⟩

private theorem sum_plus_exact (k : ℕ) : ∑ x ∈ range (2^k), actual false x = plusBlock k :=
  sum_congr rfl (fun x hx=>plus_exact k x (mem_range.mp hx))

private theorem block_error (j : Bool) (k b D : ℕ) (hb : (b+1)*2^k≤2^D) :
    |(∑ x ∈ range (2^k), actual j (b*2^k+x))- block j k (weight b)| ≤ 4*(D+2:ℝ) := by
  have hp : 0<2^k := Nat.two_pow_pos _
  have hbd : b<2^D := by nlinarith [show 1≤2^k by omega]
  have hw := w_bound D b hbd
  let f : ℕ → ℝ := fun x=>actual j (b*2^k+x)
  have sh := shift_sum (f:=f) (fun i=>actual_mem j _) (2^k) (weight b)
  have err := edges (f:=fun x=>f (weight b+x)) (g:=low j k (weight b)) (2^k)
    (D+2) (weight b+(D+2)) (fun i=>actual_mem j _) (fun i=>low_mem j k (weight b) _)
    (fun x lo hi=>by simpa [f,Nat.add_assoc] using interior hb lo (by omega) j)
  have tri := abs_sub_le (∑ x ∈ range (2^k), f x) (∑ x ∈ range (2^k), f (weight b+x))
    (block j k (weight b))
  change |(∑ x ∈ range (2^k), f x)-block j k (weight b)| ≤ _
  change |(∑ x ∈ range (2^k),f (weight b+x))-block j k (weight b)| ≤ _ at err
  rw [abs_sub_comm] at sh; push_cast at err
  have hh : (weight b:ℝ)≤D := by exact_mod_cast hw
  linarith

private theorem alpha_step (k : ℕ) :
    |alpha (k+1)-alpha k| ≤ 4*((k:ℝ)+3)/(2:ℝ)^(k+1) := by
  have e := block_error false k 1 (k+1) (by rw [pow_succ]; omega)
  rw [block_false] at e; simp only [one_mul,Nat.cast_add,Nat.cast_one] at e
  have eq : plusBlock (k+1) = plusBlock k + ∑x ∈ range (2^k), actual false (2^k+x) := by
    rw [←sum_plus_exact, pow_succ, Nat.mul_two,sum_range_add,sum_plus_exact]
  have he : alpha (k+1)-alpha k =
      ((∑ x ∈ range (2^k), actual false (2^k+x))-plusBlock k)/(2:ℝ)^(k+1) := by
    unfold alpha; rw [eq,pow_succ]; field_simp; ring
  rw [he,abs_div,abs_of_pos (by positivity : 0<(2:ℝ)^(k+1))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

private theorem alpha_limit : ∃ c : ℝ, Tendsto alpha atTop (𝓝 c) := by
  have h1 : Summable (fun k : ℕ=>(k:ℝ)*(1/2:ℝ)^k) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 (r:=(1/2:ℝ)) (by norm_num))
  have h0 : Summable (fun k : ℕ=>(1/2:ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable (fun k : ℕ=>4*((k:ℝ)+3)/(2:ℝ)^(k+1)) := by
    refine ((h1.add (h0.mul_left 3)).mul_left 2).congr (fun k=>?_ )
    change 2*((k:ℝ)*(1/2:ℝ)^k+3*(1/2:ℝ)^k) = _; rw [pow_succ,div_pow,one_pow]
    field_simp; ring
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_dist_le_of_summable _ _ hsum
  intro k
  rw [dist_comm,Real.dist_eq]; exact alpha_step k


private theorem sum_error {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (C : ℝ)
    (h : ∀ i ∈ S, |f i-g i|≤C) :
    |(∑i ∈ S,f i) - (∑i ∈ S,g i)| ≤ S.card*C := by
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |f i-g i| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _i ∈ S, C := sum_le_sum h
    _ = _ := by simp

private theorem bin_mean_error (r s L : ℕ) (f : ℕ → ℝ) (A cap E : ℝ) (hL : 0<L)
    (hf : ∀i, 0≤f i ∧ f i≤cap)
    (H : ∀ j, j≤2*r → |(∑t ∈ range L, f (s+j+t))-L*A|≤E) :
    |bin (2*r) f s - (2:ℝ)^(2*r)*A| ≤ 3*L*(r.centralBinom:ℝ)*cap + (2:ℝ)^(2*r)*(E/L) := by
  let B := (2:ℝ)^(2*r)
  let U := ∑t ∈ range L, bin (2*r) f (s+t)
  let c := (r.centralBinom:ℝ)
  have non : 0≤3*c*cap := by
    have hc : 0≤c := by dsimp [c]; positivity
    have hcap := (hf 0).1.trans (hf 0).2
    positivity
  have e1 : |L*bin (2*r) f s-U| ≤ L*((L:ℝ)*(3*c*cap)) := by
    have h := sum_error (range L) (fun _=>bin (2*r) f s) (fun t=>bin (2*r) f (s+t))
      (L*(3*c*cap)) (by
        intro i hi
        rw [abs_sub_comm]
        have hh := bin_shift r f s i cap hf
        exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (mem_range.mp hi).le) non))
    simpa [U] using h
  have e2 : |U-B*(L*A)| ≤ B*E := by
    let w := fun j=>(↑((2*r).choose j):ℝ)
    have he : U-B*(L*A) = ∑ j ∈ range (2*r+1),
        w j*((∑ t ∈ range L, f (s+j+t))-L*A) := by
      dsimp [U,bin,B,w]; rw [sum_comm,←sum_bin_weights]
      simp only [mul_sub,mul_sum,sum_sub_distrib,Finset.sum_mul]
      congr 1
      apply sum_congr rfl; intro j _; apply sum_congr rfl; intro t _
      rw [show s+t+j=s+j+t by omega]
    rw [he]
    calc
      _ ≤ ∑j ∈ range (2*r+1), |w j*((∑t ∈ range L,f (s+j+t))-L*A)| := abs_sum_le_sum_abs ..
      _ ≤ ∑j ∈ range (2*r+1), w j*E := by
        apply sum_le_sum; intro j hj
        have hp : 0≤w j := by dsimp [w]; positivity
        rw [abs_mul,abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_left (H j (Nat.le_of_lt_succ (mem_range.mp hj))) hp
      _ = _ := by rw [←Finset.sum_mul]; dsimp [w,B]; rw [sum_bin_weights]
  have h := abs_sub_le (L*bin (2*r) f s) U (B*(L*A))
  have e : L*bin (2*r) f s-B*(L*A) = L*(bin (2*r) f s-B*A) := by ring
  rw [e,abs_mul,abs_of_nonneg (Nat.cast_nonneg L)] at h
  change |bin (2*r) f s-B*A| ≤ 3*L*c*cap+B*(E/L)
  have hpos : 0<(L:ℝ) := by exact_mod_cast hL
  apply le_of_mul_le_mul_left (a:=(L:ℝ)) _ hpos
  calc
    _ ≤ L*((L:ℝ)*(3*c*cap))+B*E := h.trans (add_le_add e1 e2)
    _ = _ := by field_simp


private theorem window (k x L : ℕ) (hx : x+2*L≤4*2^k) :
    |(∑t ∈ range L, minusL (k+2) (x+2*t))-(L:ℝ)/2| ≤ k+8 := by
  have H := local_hit_bounds k x L hx
  let p := fun t=>lowGen (k+2) (x+2*t)
  let a := ((range L).filter p).card
  let b := ((range L).filter (fun t=>¬p t)).card
  have eq : a+b=L := by simpa [a,b] using card_filter_add_card_filter_not (s:=range L) p
  have hl : 2*L ≤ 4*a + (k+8) := H.1
  have hu : 4*a ≤ 2*L + (k+8) := H.2
  have hsum : (∑t ∈ range L, minusL (k+2) (x+2*t))=(b:ℝ) := by
    unfold b
    rw [natCast_card_filter]
    apply sum_congr rfl; intro t _
    by_cases ht : p t <;> simp [minusL,mark,p,lowGen] at ht ⊢
  rw [hsum]
  have e : (a:ℝ)+b=L := by exact_mod_cast eq
  have el : 2*(L:ℝ)≤4*a+(k+8) := by exact_mod_cast hl
  have eu : 4*(a:ℝ)≤2*L+(k+8) := by exact_mod_cast hu
  apply abs_le.mpr; constructor <;> linarith [show (0:ℝ)≤k by positivity]

private theorem window_raw (k x L : ℕ) :
    |(∑t ∈ range L, minusL k (x+2*t))-(L:ℝ)/2| ≤ L := by
  have hp : 0 ≤ ∑t ∈ range L, minusL k (x+2*t) := sum_nonneg (fun i _=>(mark_mem _).1)
  have hu : (∑t ∈ range L, minusL k (x+2*t)) ≤ L := by
    calc _ ≤ ∑ _t ∈ range L, (1:ℝ) := sum_le_sum (fun i _=>(mark_mem _).2)
         _ = _ := by simp
  exact abs_le.mpr ⟨by linarith [show (0:ℝ)≤L by positivity],by linarith [show (0:ℝ)≤L by positivity]⟩

private theorem window_block (k h L : ℕ) :
    |(∑t ∈ range L, block true (k+2) (h+t))-(L:ℝ)*plusBlock (k+2)/2| ≤
      (2:ℝ)^(k+2)*(k+8)+2*(h+L)*(L:ℝ) := by
  let M:=2^(k+2)
  let K:=k+2
  have hM : M=4*2^k := by dsimp [M]; rw [pow_add]; ring
  let w := fun x=> (∑ t ∈ range L, minusL K (x+2*h+2*t))-(L:ℝ)/2
  have he : (∑t ∈ range L, block true K (h+t))-(L:ℝ)*plusBlock K/2 =
      ∑x ∈ range M, plusL K x*w x := by
    unfold block plusBlock; change (∑t ∈ range L, ∑x ∈ range M,
      plusL K x*minusL K (x+2*(h+t))) - _ = _
    rw [sum_comm]
    simp only [w,mul_sub,mul_sum,sum_sub_distrib]
    congr 1
    · apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
      rw [show i+2*(h+j)=i+2*h+2*j by omega]
    · rw [←mul_sum]
      change (L:ℝ)*(∑x ∈ range M,plusL K x)/2 = ∑x ∈ range M,plusL K x*((L:ℝ)/2)
      rw [←sum_mul]; ring
  change |(∑t ∈ range L, block true K (h+t))-(L:ℝ)*plusBlock K/2| ≤ _
  rw [he]
  calc
    _ ≤ ∑x ∈ range M, |plusL K x*w x| := abs_sum_le_sum_abs ..
    _ ≤ ∑x ∈ range M, ((k+8:ℝ) + (if M<x+2*(h+L) then (L:ℝ) else 0)) := by
      apply sum_le_sum; intro x _
      have hw : |w x| ≤ L := window_raw K (x+2*h) L
      have hp : 0≤plusL K x ∧ plusL K x≤1 := mark_mem _
      have le : |plusL K x*w x| ≤ |w x| := by
        rw [abs_mul,abs_of_nonneg hp.1]; nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (abs_nonneg (w x))]
      split_ifs with hx
      · linarith [show (0:ℝ)≤k by positivity]
      · have u := window k (x+2*h) L (by omega)
        change |w x| ≤ _ at u; linarith
    _ ≤ _ := by
      rw [sum_add_distrib,sum_const,sum_ite,sum_const,sum_const_zero,add_zero]
      simp only [card_range,nsmul_eq_mul]
      have sub : (range M).filter (fun x=>M<x+2*(h+L)) ⊆ Ico (M-2*(h+L)) M := by
        intro x hx; obtain ⟨hi,hh⟩ := mem_filter.mp hx
        exact mem_Ico.mpr ⟨by omega,mem_range.mp hi⟩
      have hc := card_le_card sub
      rw [Nat.card_Ico] at hc
      have hle : (((range M).filter (fun x=>M<x+2*(h+L))).card:ℝ) ≤ 2*(h+L) := by
        exact_mod_cast (show _ ≤ 2*(h+L) by omega)
      dsimp [M] at *
      push_cast; gcongr


private def scale (N : ℕ) := Nat.findGreatest (fun s=>2^(4*s^6) ≤ N) N

private theorem scale_tendsto : Tendsto scale atTop atTop := by
  apply tendsto_atTop.mpr; intro n
  filter_upwards [eventually_ge_atTop (max n (2^(4*n^6)))] with N hN
  exact Nat.le_findGreatest (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN)

private theorem base_bounds (N : ℕ) (hn : 0<N) :
    2^(4*(scale N)^6) ≤ N ∧ N < 2^(4*(scale N+1)^6) := by
  refine ⟨Nat.findGreatest_spec (P:=fun t=>2^(4*t^6) ≤ N) (Nat.zero_le N) (by norm_num; omega),?_⟩
  by_cases h : scale N+1 ≤ N
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest (P:=fun t=>2^(4*t^6) ≤ N) (n:=N) (k:=scale N+1) (by change scale N< scale N+1; omega) h)
  · have hm : N<2^N := Nat.lt_two_pow_self
    have he : N ≤ 4*(scale N+1)^6 := by
      have hx : scale N+1 ≤ (scale N+1)^6 := Nat.le_self_pow (by decide) _
      omega
    exact hm.trans_le (Nat.pow_le_pow_right (by decide) he)

private theorem scale_upper (N : ℕ) (hn : 0<N) (hs : 1 ≤ scale N) : N ≤ 2^(256*(scale N)^6) := by
  have h:= (base_bounds N hn).2
  apply h.le.trans
  apply Nat.pow_le_pow_right (by decide)
  have hp := Nat.pow_le_pow_left (show scale N+1 ≤ 2*scale N by omega) 6
  rw [mul_pow] at hp; norm_num at hp; omega

private theorem remainder_scale (N s : ℕ) (hs : 2 ≤ s) (hn : 2^(4*s^6) ≤ N) :
    (2^(2*s^6)*2^(s+2))*2^s ≤ N := by
  rw [←pow_add,←pow_add]
  apply le_trans _ hn; apply Nat.pow_le_pow_right (by decide)
  have hh : s+1 ≤ s^6 := by
    have H : s^2 ≤ s^6 := Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith
  omega

private theorem central_at_scale (s : ℕ) :
    (s:ℝ)^3*((s^6).centralBinom:ℝ) ≤ 2^(2*s^6) := by
  have h := central_square (s^6)
  push_cast at h
  have h2 : ((2:ℝ)^(2*s^6))^2 = 16^(s^6) := by
    rw [pow_mul,←pow_mul,show s^6*2=2*s^6 by omega,pow_mul]
    norm_num
  have c : (0:ℝ) ≤ ((s^6).centralBinom:ℝ)^2 := sq_nonneg _
  have hs := sq_nonneg ((2:ℝ)^(2*s^6)-(s:ℝ)^3*((s^6).centralBinom:ℝ))
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [h2]
  nlinarith

private theorem small_parameters (ε : ℝ) (he : 0<ε) :
    ∀ᶠ (s : ℕ) in atTop, let D : ℕ :=256*s^6; let L : ℕ :=s^2; let r : ℕ :=s^6
      2 ≤ s ∧ (4*((D:ℝ)+2) ≤ 2^(s+2)*ε) ∧ ((s:ℝ)+8 ≤ L*ε) ∧
      (2*((D:ℝ)+2*r+L) ≤ 2^(s+2)*ε) ∧
      (3*L*(r.centralBinom:ℝ) ≤ 2^(2*r)*ε) ∧ (1 ≤ (2:ℝ)^s*ε) := by
  have p := (tendsto_pow_const_div_const_pow_of_one_lt 6 (r:=(2:ℝ)) (by norm_num)).const_mul 2000
  have q : Tendsto (fun s : ℕ=> (20:ℝ)/s) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have p' : Tendsto (fun s : ℕ => 2000*((s:ℝ)^6/(2:ℝ)^s)) atTop (𝓝 0) := by simpa using p
  filter_upwards [eventually_ge_atTop 8,p'.eventually_lt_const he,q.eventually_lt_const he] with s hs hp hq
  dsimp only
  have hs0 : (0:ℝ)< s := by exact_mod_cast (by omega : 0< s)
  have h8 : (8:ℝ) ≤ s := by exact_mod_cast hs
  have h20 := (div_lt_iff₀ hs0).mp hq
  have hpow : (0:ℝ)<2^s := by positivity
  have h2000 : 2000*(s:ℝ)^6 ≤ 2^s*ε := by
    rw [←mul_div_assoc] at hp; linarith [(div_lt_iff₀ hpow).mp hp]
  have hstrong : 2000*(s:ℝ)^6 ≤ 2^(s+2)*ε := by
    rw [pow_add]; norm_num
    nlinarith [mul_nonneg hpow.le he.le]
  have h1 : (1:ℝ) ≤ (s:ℝ)^6 := one_le_pow₀ (by linarith) 
  have hs2 : (s:ℝ)^2 ≤ (s:ℝ)^6 := pow_le_pow_right₀ (by linarith) (by decide)
  have hc := central_at_scale s
  have hn : 0 ≤ (s:ℝ)^2*((s^6).centralBinom:ℝ) := by positivity
  push_cast
  refine ⟨by omega,by nlinarith,by nlinarith [mul_nonneg (sub_nonneg.mpr h20.le) hs0.le],by nlinarith,?_,by nlinarith⟩
  have hpos := mul_nonneg (sub_nonneg.mpr h20.le) hn
  have hc' := mul_le_mul_of_nonneg_right hc he.le
  nlinarith


private noncomputable def expected (j : Bool) (k : ℕ) :=
  if j then alpha k/2 else alpha k

private theorem expected_unit (j : Bool) (k : ℕ) : 0≤expected j k ∧ expected j k≤1 := by
  have h := block_unit false k 0; rw [block_false] at h
  have hp : (0:ℝ)<2^k := by positivity
  have ha : 0≤alpha k ∧ alpha k≤1 := by
    exact ⟨div_nonneg h.1 hp.le,(div_le_one hp).mpr h.2⟩
  cases j <;> simp only [expected,Bool.false_eq_true,if_false,if_true]
  · exact ha
  · constructor <;> linarith [ha.1,ha.2]

private theorem group_error (joint : Bool) (k r L a D : ℕ) (ε : ℝ) (hε : 0≤ε) (hL : 0<L)
    (hgroup : (a+1)*(2^(2*r)*2^(k+2)) ≤ 2^D)
    (hcut : 4*((D:ℝ)+2) ≤ 2^(k+2)*ε)
    (hwin : (k:ℝ)+8≤L*ε)
    (hside : 2*((D:ℝ)+2*r+L) ≤ 2^(k+2)*ε)
    (hbin : 3*L*(r.centralBinom:ℝ) ≤ 2^(2*r)*ε) :
    let G := 2^(2*r)*2^(k+2)
    |(∑ x ∈ range G,actual joint (a*G+x)) - G*expected joint (k+2)| ≤ G*(4*ε) := by
  let R:=2^(2*r)
  let K:=k+2
  let M:=2^K
  let g:=R*M
  let f:=block joint K
  let b:=weight a
  have hm : (0:ℝ)<M := by dsimp [M]; positivity
  have hr : (0:ℝ)<R := by dsimp [R]; positivity
  have hg' : (a+1)*g≤2^D := hgroup
  have hsize : 0<g := by dsimp [g,R,M]; positivity
  have hab : a<2^D := by nlinarith [show 1≤g by omega]
  have hbw : b≤D := w_bound D a hab
  have castM : (M:ℝ)=2^(k+2) := by simp [M,K]
  have castR : (R:ℝ)=2^(2*r) := by simp [R]
  rw [←castM] at hcut hside
  rw [←castR] at hbin
  have e1 : |(∑ x ∈ range g,actual joint (a*g+x)) - bin (2*r) f b| ≤ R*(M*ε) := by
    rw [←weights_sum]
    change |(∑ x ∈ range (R*M), (fun t=>actual joint (a*g+t)) x) - _| ≤ _
    rw [sum_by_blocks]
    have h := sum_error (range R) (fun y=>∑ u ∈ range M, actual joint (a*g+(y*M+u)))
      (fun y=>f (b+weight y)) (M*ε) (by
        intro y hy
        have h1 := mem_range.mp hy
        have hb : (a*R+y+1)*M ≤ 2^D := by
          apply le_trans _ hg'; dsimp [g]; rw [←Nat.mul_assoc]
          apply Nat.mul_le_mul_right; rw [Nat.add_mul]; omega
        have he := block_error joint K (a*R+y) D hb
        have w := w_split a (2*r) y h1
        change weight (a*R+y)=b+weight y at w
        rw [w] at he
        have eq : (∑u ∈ range M,actual joint (a*g+(y*M+u))) =
            (∑u ∈ range M,actual joint ((a*R+y)*M+u)) := by
          apply sum_congr rfl; intro u _; dsimp [g]; ring_nf
        rw [eq]; exact he.trans hcut)
    simpa only [card_range] using h
  have e2 : |bin (2*r) f b - R*(M*expected joint K)| ≤ R*(3*(M*ε)) := by
    cases joint with
    | false =>
      have hconst : bin (2*r) f b = R*plusBlock K := by
        dsimp [f,bin]; simp only [block_false,←Finset.sum_mul,sum_bin_weights,castR]
      rw [hconst]
      have hx : (M:ℝ)*expected false K = plusBlock K := by
        change (M:ℝ)*(plusBlock K/(2:ℝ)^K) = _
        dsimp [M]; push_cast; field_simp
      rw [hx,sub_self,abs_zero]; positivity
    | true =>
      let P:=plusBlock K/2
      have hb := bin_mean_error r b L f P M
        (M*((k:ℝ)+8)+2*((D:ℝ)+2*r+L)*L) hL (fun i=>by simpa [f,M] using block_unit true K i) (by
          intro j hj
          have h := window_block k (b+j) L
          change |(∑t ∈ range L, block true K (b+j+t)) - (L:ℝ)*(plusBlock K/2)| ≤ _
          have e : (L:ℝ)*(plusBlock K/2) = (L:ℝ)*plusBlock K/2 := by ring
          rw [e]
          refine h.trans ?_
          rw [castM]; push_cast
          gcongr; first | exact_mod_cast hbw | exact_mod_cast hj)
      rw [←castR] at hb
      have hh : (M:ℝ)*expected true K=P := by
        change (M:ℝ)*(plusBlock K/(2:ℝ)^K/2)=plusBlock K/2
        dsimp [M]; push_cast; field_simp
      rw [hh]
      refine hb.trans ?_
      have h1 := mul_le_mul_of_nonneg_right hbin hm.le
      have h2 := mul_le_mul_of_nonneg_left hwin hm.le
      have h3 := mul_le_mul_of_nonneg_right hside (Nat.cast_nonneg L)
      have hq : (M*((k:ℝ)+8)+2*((D:ℝ)+2*r+L)*L)/(L:ℝ) ≤ 2*(M*ε) :=
        (div_le_iff₀ (by exact_mod_cast hL)).mpr (by nlinarith)
      have hh' := mul_le_mul_of_nonneg_left hq hr.le
      nlinarith
  have he := abs_sub_le (∑ x ∈ range g,actual joint (a*g+x)) (bin (2*r) f b) (R*(M*expected joint K))
  change |(∑ x ∈ range g,actual joint (a*g+x)) - g*expected joint K| ≤ g*(4*ε)
  have hc : (g:ℝ)=R*(M:ℝ) := by simp [g]
  rw [hc,mul_assoc]
  linarith [show (R:ℝ)*(M*ε)+R*(3*(M*ε)) = R*(M*(4*ε)) by ring]


private theorem prefix_estimate (f : ℕ → ℝ) (hf : ∀i, 0 ≤ f i ∧ f i ≤ 1) (N G : ℕ)
    (hn : 0<N) (hg : 0<G) (v ε : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (he : 0 ≤ ε)
    (small : (G:ℝ) ≤ N*ε)
    (H : ∀ a, (a+1)*G ≤ N → |(∑i ∈ range G,f (a*G+i))-G*v| ≤ G*(4*ε)) :
    |(∑i ∈ range N,f i)/(N:ℝ)-v| ≤ 5*ε := by
  let q:=N/G
  let t:=N%G
  have hdec : q*G+t=N := by simpa [q,t,Nat.mul_comm] using Nat.div_add_mod N G
  have ht : t<G := Nat.mod_lt _ hg
  have full := sum_error (range q) (fun a=>∑i ∈ range G,f (a*G+i)) (fun _=>G*v) (G*(4*ε)) (by
    intro a ha; exact H a (by have hx:=mem_range.mp ha; nlinarith [Nat.mul_le_mul_right G (Nat.succ_le_of_lt hx)]))
  rw [←sum_by_blocks] at full; simp only [sum_const,card_range,nsmul_eq_mul] at full
  have tail : |(∑ i ∈ range t, f (q*G+i))-t*v| ≤ t := by
    have ht0 : 0 ≤ ∑ i ∈ range t,f (q*G+i) := sum_nonneg (fun i _=>(hf _).1)
    have ht1 : (∑ i ∈ range t,f (q*G+i)) ≤ t := by
      calc _ ≤ ∑ _i ∈ range t,(1:ℝ) := sum_le_sum (fun i _=>(hf _).2)
           _ = _ := by simp
    have hv0 := mul_nonneg (Nat.cast_nonneg t) hv.1
    have hv1 := mul_le_mul_of_nonneg_left hv.2 (Nat.cast_nonneg t)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have eq : (∑ i ∈ range N,f i) = (∑ i ∈ range (q*G), f i)+(∑ i ∈ range t,f (q*G+i)) := by
    rw [←sum_range_add,hdec]
  have dc : (q:ℝ)*G+t=N := by exact_mod_cast hdec
  have hn' : (0:ℝ)<N := by exact_mod_cast hn
  have hh : (q:ℝ)*G ≤ N := by linarith [show (0:ℝ) ≤ t by positivity]
  have hl := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 4*ε)
  have re : (t:ℝ) ≤ N*ε := (by exact_mod_cast ht.le : (t:ℝ) ≤ G).trans small
  have d : (∑ i ∈ range N,f i)/(N:ℝ)-v =
      (((∑i ∈ range (q*G),f i)-q*(G*v))+((∑i ∈ range t,f (q*G+i))-t*v))/N := by
    rw [eq]; field_simp; nlinarith [congrArg (fun x : ℝ=>x*v) dc]
  rw [d,abs_div,abs_of_pos hn',div_le_iff₀ hn']
  have tri := abs_add_le ((∑i ∈ range (q*G),f i)-q*(G*v)) ((∑i ∈ range t,f (q*G+i))-t*v)
  linarith [show (q:ℝ)*(G*(4*ε))=(q*G)*(4*ε) by ring]

private theorem approximates (j : Bool) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ (N : ℕ) in atTop, |(∑x ∈ range N,actual j x)/(N:ℝ)-expected j (scale N+2)| ≤ 5*ε := by
  filter_upwards [scale_tendsto.eventually (small_parameters ε he),eventually_ge_atTop 1] with N h hn
  obtain ⟨hs,cut,win,side,bino,rem⟩ := h
  let s:=scale N
  let G:=2^(2*s^6)*2^(s+2)
  have nlo := (base_bounds N hn).1
  have nhi := scale_upper N hn (by omega)
  have rg := remainder_scale N s hs nlo
  have rg' : (G:ℝ)*2^s ≤ N := by exact_mod_cast rg
  have sm : (G:ℝ) ≤ N*ε := by
    have u := mul_le_mul_of_nonneg_left rem (Nat.cast_nonneg G)
    have v := mul_le_mul_of_nonneg_right rg' he.le
    change 1 ≤ (2:ℝ)^s*ε at rem
    calc (G:ℝ) ≤ G*(2^s*ε) := by simpa using u
         _ = (G*2^s)*ε := by ring
         _ ≤ _ := v
  apply prefix_estimate _ (actual_mem j) N G hn (by dsimp [G]; positivity) _
    ε (expected_unit _ _) he.le sm
  intro a ha
  exact group_error j s (s^6) (s^2) a (256*s^6) ε he.le (by positivity)
    (ha.trans nhi) cut win side bino

private theorem limit_counts {c : ℝ} (hc : Tendsto alpha atTop (𝓝 c)) (j : Bool) :
    Tendsto (fun N : ℕ=>(∑x ∈ range N,actual j x)/(N:ℝ)) atTop
      (𝓝 (if j then c/2 else c)) := by
  have ht : Tendsto (fun N=>scale N+2) atTop atTop := tendsto_atTop_mono (fun _=>by omega) scale_tendsto
  have hv : Tendsto (fun N=>expected j (scale N+2)) atTop (𝓝 (if j then c/2 else c)) := by
    cases j
    · exact hc.comp ht
    · exact (hc.comp ht).div_const 2
  apply Metric.tendsto_nhds.mpr; intro ε he
  filter_upwards [approximates j (ε/20) (by positivity),
    (Metric.tendsto_nhds.mp hv) (ε/2) (by positivity)] with N ha hb
  rw [Real.dist_eq] at hb ⊢
  have tr := abs_sub_le ((∑x ∈ range N,actual j x)/(N:ℝ)) (expected j (scale N+2))
    (if j then c/2 else c)
  linarith

private theorem source_frequency (j : Bool) (N : ℕ) :
    frequency (if j then missed else self) N = (∑x ∈ range N,actual j x)/(N:ℝ) := by
  unfold frequency
  rw [natCast_card_filter]
  congr 1
  apply sum_congr rfl; intro i _
  cases j <;> simp [actual,mark]

private theorem solved : ∃ c : ℝ, Tendsto (frequency self) atTop (𝓝 c) ∧
    Tendsto (frequency missed) atTop (𝓝 (c/2)) := by
  obtain ⟨c,hc⟩ := alpha_limit
  refine ⟨c,?_,?_⟩
  · have e := funext (source_frequency false)
    change frequency self = _ at e
    rw [e]; exact limit_counts hc false
  · have e := funext (source_frequency true)
    change frequency missed = _ at e
    rw [e]; exact limit_counts hc true


end A227359Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a227359.main :=
  A227359Proof.solved
