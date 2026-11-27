import OMAStatements.S_oeis_a246600

/-!
# The asymptotic mean of binary submask divisors

Write the dividend as `d * (q + 1)`. The submask condition means that no binary
position is set in both `d` and `d*q`. The diagonal `q = 0` gives the constant
one. Fixed rows have periodic densities and fixed positive columns have density
zero. A dyadic bound on the count with both coordinates large makes these
individual limits sufficient to compute the full mean.
-/

namespace A246600Proof
open OMA.S_oeis_a246600 Finset Filter Topology
open scoped BigOperators


/-- The lowest h binary positions have no common one-bit. -/
private def ok : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | h+1,d,x => if d%2=1 ∧ x%2=1 then 0 else ok h (d/2) (x/2)

private def free : ℕ → ℕ → ℕ
  | 0,_ => 1
  | h+1,d => (if d%2=0 then 2 else 1)*free h (d/2)

private theorem ok_le (h d x : ℕ) : ok h d x ≤ 1 := by
  induction h generalizing d x with
  | zero => simp [ok]
  | succ h ih => simp only [ok]; split <;> first | omega | exact ih _ _

private theorem ok_iff (h d x : ℕ) :
    ok h d x=1 ↔ ∀ i < h, ¬(d.testBit i ∧ x.testBit i) := by
  induction h generalizing d x with
  | zero => simp [ok]
  | succ h ih =>
    have tt (j : ℕ) : j.testBit 0 = true ↔ j%2=1 := by
      simp [Nat.testBit_eq_decide_div_mod_eq]
    simp only [ok]
    by_cases hbad : d%2=1 ∧ x%2=1
    · rw [if_pos hbad]
      simp only [zero_ne_one, false_iff]
      exact fun hh => hh 0 (by omega) ⟨(tt _).mpr hbad.1,(tt _).mpr hbad.2⟩
    · rw [if_neg hbad,ih]
      constructor
      · intro hh i hi
        cases i with
        | zero => simpa only [tt] using hbad
        | succ i => simpa only [Nat.testBit_add_one] using hh i (by omega)
      · intro hh i hi
        simpa only [Nat.testBit_add_one] using hh (i+1) (by omega)

private theorem ok_period (h d x a b : ℕ) :
    ok h (d+2^h*a) (x+2^h*b) = ok h d x := by
  have hbit (m j i : ℕ) (hi : i<h) : (m+2^h*j).testBit i = m.testBit i := by
    have e : (m+2^h*j)%2^h=m%2^h := by simp [Nat.add_mod]
    have := congrArg (fun r : ℕ => r.testBit i) e
    change ((m+2^h*j)%2^h).testBit i = (m%2^h).testBit i at this
    simpa only [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and] using this
  have eq1 : ok h (d+2^h*a) (x+2^h*b)=1 ↔ ok h d x=1 := by
    simp only [ok_iff]
    exact forall_congr' fun i => forall_congr' fun hi => by rw [hbit _ _ i hi,hbit _ _ i hi]
  have := ok_le h (d+2^h*a) (x+2^h*b)
  have := ok_le h d x
  omega

private theorem sum_pairs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (s : ℕ) :
    ∑ i ∈ range (2*s), f i = ∑ i ∈ range s, (f (2*i)+f (2*i+1)) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.mul_succ, sum_range_succ (n := 2*s+1), sum_range_succ (n := 2*s),
      ih,sum_range_succ]; abel

private theorem odd_affine (h d b c : ℕ) (hb : b%2=1) :
    ∑ j ∈ range (2^h), ok h d (b*j+c) = free h d := by
  induction h generalizing d c with
  | zero => simp [ok,free]
  | succ h ih =>
    rw [pow_succ',sum_pairs]
    have he (j : ℕ) : b*(2*j)+c=2*(b*j)+c := by ring
    have ho (j : ℕ) : b*(2*j+1)+c=2*(b*j)+(b+c) := by ring
    have div2 (v w : ℕ) : (2*v+w)/2=v+w/2 := by omega
    have mod2 (v w : ℕ) : (2*v+w)%2=w%2 := by omega
    simp only [he,ho,ok,div2,mod2,free]
    rcases Nat.mod_two_eq_zero_or_one d with hd|hd <;>
      rcases Nat.mod_two_eq_zero_or_one c with hc|hc <;>
      have hbc : (b+c)%2=1-c%2 := by omega
    all_goals simp [hd,hc,hbc,Finset.sum_add_distrib,ih, two_mul]

private def pair (h d q : ℕ) := ok h d (d*q)

private theorem pair_period (h d q a b : ℕ) :
    pair h (d+2^h*a) (q+2^h*b)=pair h d q := by
  dsimp only [pair]
  rw [show (d+2^h*a)*(q+2^h*b)=d*q+2^h*(d*b+a*q+2^h*a*b) by ring]
  exact ok_period _ _ _ _ _

private theorem row_at (h d : ℕ) : ∑ q ∈ range (2^h), pair h d q = free h d := by
  induction h generalizing d with
  | zero => simp [pair,ok,free]
  | succ h ih =>
    rcases Nat.mod_two_eq_zero_or_one d with hd|hd
    · obtain ⟨e,he⟩ : 2∣d := Nat.dvd_of_mod_eq_zero hd
      subst d
      rw [pow_succ, Nat.mul_two,sum_range_add]
      have hterm (q : ℕ) : pair (h+1) (2*e) q = pair h e q := by
        simp [pair,ok,Nat.mul_assoc]
      have hper (q : ℕ) : pair h e (2^h+q)=pair h e q := by
        simpa [add_comm] using pair_period h e q 0 1
      simp only [hterm,hper,ih,free]
      rw [if_pos hd,show 2*e/2=e by omega,two_mul]
    · simpa [pair] using odd_affine (h+1) d d 0 hd

private theorem total_free (h : ℕ) : ∑ d ∈ range (2^h), free h d=3^h := by
  induction h with
  | zero => simp [free]
  | succ h ih =>
    rw [pow_succ',sum_pairs]
    have hp j : free (h+1) (2*j)+free (h+1) (2*j+1)=3*free h j := by
      simp only [free,show 2*j%2=0 by omega,show (2*j+1)%2=1 by omega,
        show (2*j+1)/2=j by omega,show 2*j/2=j by omega]
      norm_num; ring
    simp_rw [hp]
    rw [← mul_sum,ih,pow_succ']

private theorem submask_add (d x : ℕ) : d &&& (d+x)=d ↔ d &&& x=0 := by
  induction d using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases hd : d=0
    · simp [hd]
    have ih2 : (d/2) &&& (d/2+x/2) = d/2 ↔ (d/2) &&& (x/2)=0 := ih (d/2) (by omega) (x/2)
    have ex (a b : ℕ) : a=b ↔ a/2=b/2 ∧ (a%2=1 ↔ b%2=1) := by omega
    rw [ex (d &&& (d+x)) d,ex (d &&& x) 0,Nat.and_div_two,Nat.and_div_two,
      Nat.and_mod_two_eq_one,Nat.and_mod_two_eq_one]
    change ((d/2 &&& ((d+x)/2))=d/2 ∧ ((d%2=1 ∧ (d+x)%2=1) ↔ d%2=1)) ↔
      ((d/2 &&& (x/2))=0 ∧ ((d%2=1 ∧ x%2=1) ↔ 0=1))
    by_cases hbad : d%2=1 ∧ x%2=1
    · have hm : (d+x)%2=0 := by omega
      simp [hbad.1,hbad.2,hm]
    · have he : (d+x)/2=d/2+x/2 := by omega
      rw [he,ih2]; omega

private def good (d q : ℕ) : ℕ := if d &&& (d*q) = 0 then 1 else 0

private theorem good_le (d q : ℕ) : good d q ≤ 1 := by unfold good; split <;> omega
private theorem good_zero (d : ℕ) : good d 0 = 1 := by simp [good]
private theorem good_le_pair (h d q : ℕ) : good d q ≤ pair h d q := by
  unfold good; split
  next he =>
    have : pair h d q=1 := (ok_iff _ _ _).mpr fun i _ h => by
      have h0 := congrArg (fun z : ℕ => z.testBit i) he
      simp [Nat.testBit_and,h.1,h.2] at h0
    omega
  next => omega

private theorem pair_full {h d : ℕ} (hd : d<2^h) (q : ℕ) : pair h d q = good d q := by
  have hb := good_le_pair h d q
  have h1 := ok_le h d (d*q)
  change pair h d q ≤ 1 at h1
  by_cases hp : pair h d q = 1
  · have H := (ok_iff _ _ _).mp hp
    have hclear : d &&& (d*q)=0 := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_and,Nat.zero_testBit]
      by_cases hi : i<h
      · have := H i hi
        cases h1 : d.testBit i <;> cases h2 : (d*q).testBit i <;> simp_all
      · rw [Nat.testBit_lt_two_pow (hd.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))]
        simp
    simp [good,hclear,hp]
  · omega

private theorem free_mass {h d : ℕ} (hd : d<2^h) :
    free h d*2^d.bitIndices.length=2^h := by
  induction h generalizing d with
  | zero =>
    have : d=0 := by simpa using hd
    subst d; simp [free]
  | succ h ih =>
    have hhalf : d/2 < 2^h := by rw [pow_succ] at hd; omega
    have hh := ih hhalf
    rcases Nat.mod_two_eq_zero_or_one d with hb|hb
    · obtain ⟨e,he⟩ : 2∣d := Nat.dvd_of_mod_eq_zero hb
      subst d; simp only [free,if_pos hb,Nat.bitIndices_two_mul,List.length_map]
      rw [show 2*e/2=e by omega] at hh ⊢
      rw [mul_assoc,hh,pow_succ']
    · have hd' : d=2*(d/2)+1 := by omega
      rw [free,if_neg (by omega),one_mul,show d.bitIndices.length=(d/2).bitIndices.length+1 by
        conv_lhs => rw [hd',Nat.bitIndices_two_mul_add_one]; simp]
      rw [pow_succ,← mul_assoc,hh,pow_succ]

private theorem block_sum (f : ℕ → ℕ) (B : ℕ)
    (hp : ∀ x j, f (x+B*j)=f x) (m : ℕ) :
    ∑ x ∈ range (B*m), f x = m*(∑ x ∈ range B, f x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    simp only [show ∀ i, f (B*m+i)=f i from fun i => by rw [add_comm,hp]]
    ring

private theorem rectangle (h a b : ℕ) :
    ∑ d ∈ range (2^h*a), ∑ q ∈ range (2^h*b), pair h d q=a*b*3^h := by
  have hc d := block_sum (pair h d) (2^h)
    (fun q j => by simpa using pair_period h d q 0 j) b
  simp_rw [hc]
  rw [← mul_sum]
  have hr (d j : ℕ) : (∑ q ∈ range (2^h), pair h (d+2^h*j) q) =
      ∑ q ∈ range (2^h), pair h d q := by
    apply sum_congr rfl; intro q hq; simpa using pair_period h d q j 0
  rw [block_sum _ _ hr]
  simp_rw [row_at]; rw [total_free]; ring
private theorem grid (f : ℕ → ℕ) (A B : ℕ) :
    ∑ n ∈ range (A*B), f n = ∑ r ∈ range A, ∑ v ∈ range B, f (r+A*v) := by
  induction B with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    simp_rw [sum_range_succ (n:=b)]
    rw [sum_add_distrib]
    simp [add_comm]

private theorem pair_mono {i j : ℕ} (h : i≤j) (d q : ℕ) : pair j d q ≤ pair i d q := by
  have hj := ok_le j d (d*q)
  have hi := ok_le i d (d*q)
  change pair j d q ≤ 1 at hj
  change pair i d q ≤ 1 at hi
  by_cases H : pair j d q = 1
  · have : pair i d q=1 := (ok_iff _ _ _).mpr fun k hk =>
      (ok_iff _ _ _).mp H k (by omega)
    omega
  · omega

private theorem exclusion (h s b r : ℕ) (hr : r<2^h) (hs : 0<s) (hb : b%2=1) :
    ∃ v < 2^(s+1), pair (h+s+1) (r+2^h*v) (2^s*b)=0 := by
  let e : ℕ := if (b*r).testBit h then 0 else 1
  let v := 2^s+e
  have hh : 1 < 2^s := Nat.one_lt_two_pow (by omega)
  have he : e ≤ 1 := by dsimp [e]; split <;> omega
  have hpow : 2^s%2=0 := by obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (n:=s) (by omega); rw [ht,pow_succ]; simp
  have hv1 : v < 2^(s+1) := by dsimp [v]; rw [pow_succ]; omega
  have hbits : v.testBit s = true := by
    rw [show v=2^s+e by rfl,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow (show e<2^s by omega)]; rfl
  have hA : (r+2^h*v).testBit (h+s)=true := by
    rw [add_comm,Nat.testBit_two_pow_mul_add v hr]
    simp [hbits]
  have hB : ((r+2^h*v)*(2^s*b)).testBit (h+s)=true := by
    rw [show (r+2^h*v)*(2^s*b)=2^s*(2^h*(b*v)+b*r) by ring,Nat.testBit_two_pow_mul]
    simp only [Nat.le_add_left,decide_true,Bool.true_and,Nat.add_sub_cancel_right,
      Nat.testBit_mul_two_pow_add_eq]
    cases hb' : (b*r).testBit h <;> simp [v,e,hb',Nat.mul_mod,Nat.add_mod,hpow,hb]
  refine ⟨v,hv1,?_⟩
  have hv := ok_le (h+s+1) (r+2^h*v) ((r+2^h*v)*(2^s*b))
  change pair _ _ _ ≤ 1 at hv
  have hne : pair (h+s+1) (r+2^h*v) (2^s*b) ≠ 1 :=
    fun hp => (ok_iff _ _ _).mp hp (h+s) (by omega) ⟨hA,hB⟩
  omega

private theorem column_blocks (s b j : ℕ) (hs : 0<s) (hb : b%2=1) :
    ∑ d ∈ range (2^((s+1)*j)), pair ((s+1)*j) d (2^s*b) ≤ (2^(s+1)-1)^j := by
  induction j with
  | zero => simp [pair,ok]
  | succ j ih =>
    let h := (s+1)*j
    let B := 2^(s+1)
    have hb0 : 0<B := by dsimp [B]; positivity
    have hrow (r : ℕ) (hr : r<2^h) :
        ∑ v ∈ range B, pair (h+s+1) (r+2^h*v) (2^s*b) ≤ (B-1)*pair h r (2^s*b) := by
      by_cases H : pair h r (2^s*b)=0
      · rw [H,mul_zero]
        apply le_of_eq; apply sum_eq_zero; intro v _
        have hp := pair_mono (i:=h) (j:=h+s+1) (by omega) (r+2^h*v) (2^s*b)
        have hper := pair_period h r (2^s*b) v 0
        simp only [mul_zero,add_zero] at hper
        omega
      · have h1 : pair h r (2^s*b)=1 := by
          have hp := ok_le h r (r*(2^s*b)); change pair h r (2^s*b) ≤ 1 at hp; omega
        rw [h1,mul_one]
        obtain ⟨v,hv,hbad⟩ := exclusion h s b r hr hs hb
        have hlt := sum_lt_sum (s:=range B) (g:=fun _ => (1:ℕ))
          (f:=fun v => pair (h+s+1) (r+2^h*v) (2^s*b))
          (fun v _ => ok_le _ _ _) ⟨v,mem_range.mpr hv,by omega⟩
        simp only [sum_const,card_range,smul_eq_mul,mul_one] at hlt
        omega
    rw [Nat.mul_succ,← add_assoc,pow_add (2:ℕ) ((s+1)*j+s) 1]
    change (∑ d ∈ range (2^(h+s)*2), pair (h+s+1) d (2^s*b)) ≤ _
    rw [show 2^(h+s)*2=2^h*B by dsimp [B]; rw [pow_add,pow_succ]; ring,grid]
    calc
      _ ≤ ∑ r ∈ range (2^h), (B-1)*pair h r (2^s*b) := sum_le_sum fun r hr => hrow r (mem_range.mp hr)
      _ = (B-1)*(∑ r ∈ range (2^h),pair h r (2^s*b)) := (mul_sum ..).symm
      _ ≤ _ := by rw [pow_succ']; exact Nat.mul_le_mul_left _ ih

/- Counting admissible pairs and the diagonal. -/

private def pts (N : ℕ) := ((range (N+1)) ×ˢ (range (N+1))).filter
  (fun t => 0<t.1 ∧ t.1*(t.2+1)≤N ∧ good t.1 t.2=1)

private theorem mem_pts {N d q : ℕ} : (d,q) ∈ pts N ↔ 0<d ∧ d*(q+1)≤N ∧ good d q=1 := by
  simp only [pts,mem_filter,mem_product,mem_range]
  constructor
  · exact And.right
  · intro h
    have := Nat.le_mul_of_pos_right (m:=q+1) d (by omega)
    have := Nat.le_mul_of_pos_left (q+1) h.1
    exact ⟨⟨by omega,by omega⟩,h⟩

private def proper (N : ℕ) := (pts N).filter (fun t=>0<t.2)

private theorem mem_proper {N d q : ℕ} : (d,q) ∈ proper N ↔
    0<d ∧ 0<q ∧ d*(q+1)≤N ∧ good d q=1 := by
  simp only [proper,mem_filter,mem_pts]; tauto

private theorem mask_iff (d q : ℕ) : good d q=1 ↔ d &&& (d*(q+1))=d := by
  rw [show d*(q+1)=d+d*q by ring,submask_add]
  simp [good]

private theorem sum_term (N : ℕ) : ∑ k ∈ range N,term (k+1) = N + (proper N).card := by
  let f (t : ℕ × ℕ) := t.1*(t.2+1)-1
  have hf : Set.MapsTo f (pts N) (range N) := by
    rintro ⟨d,q⟩ ht
    have H := mem_pts.mp ht
    have hp : 0<d*(q+1) := Nat.mul_pos H.1 (by omega)
    apply mem_range.mpr
    dsimp [f]; omega
  have fibers (k : ℕ) (hk : k<N) :
      ((pts N).filter (fun t=>f t=k)).card = term (k+1) := by
    unfold term
    apply card_nbij Prod.fst
    · rintro ⟨d,q⟩ ht
      obtain ⟨ht,he⟩ := mem_filter.mp ht
      obtain ⟨hd,hn,hg⟩ := mem_pts.mp ht
      have hp := Nat.mul_pos hd (show 0<q+1 by omega)
      change d*(q+1)-1=k at he
      have e : k+1=d*(q+1) := by omega
      apply mem_filter.mpr
      exact ⟨Nat.mem_divisors.mpr ⟨⟨q+1,e⟩,by omega⟩,e ▸ (mask_iff d q).mp hg⟩
    · rintro ⟨d,q⟩ h ⟨e,r⟩ h' he
      change d=e at he
      subst e
      obtain ⟨ha,ha'⟩ := mem_filter.mp h
      obtain ⟨hb,hb'⟩ := mem_filter.mp h'
      have hd := (mem_pts.mp ha).1
      have hpos := Nat.mul_pos hd (show 0<q+1 by omega)
      have hpos' := Nat.mul_pos hd (show 0<r+1 by omega)
      change d*(q+1)-1=k at ha'
      change d*(r+1)-1=k at hb'
      have := Nat.mul_left_cancel hd (show d*(q+1)=d*(r+1) by omega)
      congr 1; omega
    · intro d hd
      obtain ⟨hd,hg⟩ := mem_filter.mp hd
      obtain ⟨⟨m,hm⟩,_⟩ := Nat.mem_divisors.mp hd
      cases m with
      | zero => simp at hm
      | succ q =>
        have hp : 0<d := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hm
        refine ⟨(d,q), mem_filter.mpr ⟨mem_pts.mpr ⟨hp,by omega,(mask_iff d q).mpr (hm ▸ hg)⟩,?_⟩,rfl⟩
        change d*(q+1)-1=k; omega
  have he : (pts N).card = ∑ k ∈ range N,term (k+1) :=
    (card_eq_sum_card_fiberwise hf).trans (sum_congr rfl fun k hk=>fibers k (mem_range.mp hk))
  have hdiag : ((pts N).filter (fun t=>¬0<t.2)).card=N := by
    rw [← card_range N]
    apply card_nbij (fun t=>t.1-1)
    · rintro ⟨d,q⟩ ht
      obtain ⟨ht,hq⟩ := mem_filter.mp ht
      change ¬0<q at hq
      have h0 : q=0 := by omega
      subst q
      obtain ⟨hd,hn,_⟩ := mem_pts.mp ht
      simp at hn
      apply mem_range.mpr; change d-1<N; omega
    · rintro ⟨d,q⟩ ht ⟨e,r⟩ hu he
      obtain ⟨ht,hq⟩ := mem_filter.mp ht
      obtain ⟨hu,hr⟩ := mem_filter.mp hu
      have hd := (mem_pts.mp ht).1
      have he' := (mem_pts.mp hu).1
      change ¬0<q at hq
      change ¬0<r at hr
      change d-1=e-1 at he
      congr 1 <;> omega
    · intro k hk
      refine ⟨(k+1,0),mem_filter.mpr ⟨mem_pts.mpr ⟨by omega,by simpa using mem_range.mp hk,good_zero _⟩,by simp⟩,by simp⟩
  have hs := card_filter_add_card_filter_not (s:=pts N) (fun t=>0<t.2)
  change (proper N).card + _ = _ at hs
  omega

private def row (N d : ℕ) := ((proper N).filter (fun t=>t.1=d)).card
private def col (N q : ℕ) := ((proper N).filter (fun t=>t.2=q)).card

private theorem row_eq {d : ℕ} (hd : 0<d) (N : ℕ) : row N d =
    ((range (N/d)).filter (fun q=>0<q ∧ good d q=1)).card := by
  apply card_nbij Prod.snd
  · rintro ⟨e,q⟩ ht
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    change e=d at he; subst e
    obtain ⟨_,hq,hn,hg⟩ := mem_proper.mp ht
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_div_iff_mul_le hd).mpr ((Nat.mul_comm _ _).trans_le hn)),hq,hg⟩
  · rintro ⟨e,q⟩ ht ⟨v,r⟩ hu he
    obtain ⟨_,hh⟩ := mem_filter.mp ht
    obtain ⟨_,hh'⟩ := mem_filter.mp hu
    change e=d at hh; change v=d at hh'; change q=r at he
    congr 1; omega
  · intro q hq
    obtain ⟨hn,hq,hg⟩ := mem_filter.mp hq
    have hh := (Nat.le_div_iff_mul_le hd).mp (mem_range.mp hn)
    exact ⟨(d,q),mem_filter.mpr ⟨mem_proper.mpr ⟨hd,hq,(Nat.mul_comm _ _).trans_le hh,hg⟩,rfl⟩,rfl⟩

private theorem col_bound (N q : ℕ) : col N q ≤ ∑ d ∈ range (N+1),good d q := by
  let s := (range (N+1)).filter (fun d=>good d q=1)
  have hs : col N q ≤ s.card := by
    apply card_le_card_of_injOn Prod.fst
    · rintro ⟨d,r⟩ ht
      obtain ⟨ht,hr⟩ := mem_filter.mp ht
      change r=q at hr; subst r
      obtain ⟨hd,hq,hn,hg⟩ := mem_proper.mp ht
      have := Nat.le_mul_of_pos_right (m:=q+1) d (by omega)
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),hg⟩
    · rintro ⟨d,r⟩ ht ⟨e,s⟩ hu he
      obtain ⟨_,hr⟩ := mem_filter.mp ht
      obtain ⟨_,hs⟩ := mem_filter.mp hu
      change r=q at hr; change s=q at hs; change d=e at he
      congr 1; omega
  apply hs.trans
  rw [show s.card = _ by exact card_filter _ _]
  apply sum_le_sum
  intro d _
  split <;> omega

/- A mean-value lemma for periodic integer sequences. -/

/-- Divide a periodic prefix sum by the original length, allowing the prefix length
to be the integer quotient of that length by a fixed positive integer. -/
private theorem periodic_mean (f : ℕ → ℕ) (p B : ℕ) (hp : 0<p) (hB : 0<B)
    (hper : ∀ x j, f (x+B*j)=f x) :
    Tendsto (fun N : ℕ => (↑(∑ x ∈ range (N/p),f x) : ℝ)/N) atTop
      (𝓝 ((↑(∑ x ∈ range B,f x) : ℝ)/(p*B))) := by
  let F := ∑ x ∈ range B,f x
  have hlim := tendsto_const_div_atTop_nhds_zero_nat (F : ℝ)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp hlim ε hε
  refine ⟨max n 1,fun N hN=>?_⟩
  have hn0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hpb : 0<p*B := Nat.mul_pos hp hB
  let j := N/(p*B)
  have hj : j*(p*B)≤N := Nat.div_mul_le_self _ _
  have hj' : N < (j+1)*(p*B) := by simpa [mul_comm] using Nat.lt_mul_div_succ N hpb
  have h1 : B*j≤N/p := (Nat.le_div_iff_mul_le hp).mpr (by simpa [mul_assoc,mul_left_comm,mul_comm] using hj)
  have h2 : N/p≤B*(j+1) := le_of_lt ((Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_assoc,mul_left_comm,mul_comm] using hj'))
  let S := ∑ x ∈ range (N/p), f x
  have hlo : j*F ≤ S := by
    rw [show j*F=∑ x ∈ range (B*j),f x by exact (block_sum f B hper j).symm]
    exact sum_le_sum_of_subset (range_mono h1)
  have hhi : S ≤ (j+1)*F := by
    rw [show (j+1)*F=∑ x ∈ range (B*(j+1)),f x by exact (block_sum f B hper _).symm]
    exact sum_le_sum_of_subset (range_mono h2)
  have pB : 0 < (p:ℝ)*B := by positivity
  have hjr : (j:ℝ)*((p:ℝ)*B) ≤ N := by exact_mod_cast hj
  have hjr' : (N:ℝ) ≤ (j+1:ℝ)*((p:ℝ)*B) := by exact_mod_cast hj'.le
  have hlo' : (j:ℝ)*F ≤ S := by exact_mod_cast hlo
  have hhi' : (S:ℝ) ≤ (j+1:ℝ)*F := by exact_mod_cast hhi
  have e1 : (j:ℝ)*F ≤ (N:ℝ)*F/((p:ℝ)*B) := by
    apply (le_div_iff₀ pB).mpr
    calc _ = ((j:ℝ)*((p:ℝ)*B))*F := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hjr (by positivity)
  have e2 : (N:ℝ)*F/((p:ℝ)*B) ≤ (j+1:ℝ)*F := by
    apply (div_le_iff₀ pB).mpr
    calc _ ≤ ((j+1:ℝ)*((p:ℝ)*B))*F := mul_le_mul_of_nonneg_right hjr' (by positivity)
         _ = _ := by ring
  have e3 : (F:ℝ)/N<ε := by simpa [Real.dist_eq,abs_of_nonneg (show 0≤(F:ℝ)/N by positivity)] using hn N (by omega)
  rw [Real.dist_eq]
  change |(S:ℝ)/N-(F:ℝ)/((p:ℝ)*B)|<ε
  rw [show (S:ℝ)/N-(F:ℝ)/((p:ℝ)*B)=((S:ℝ)-(N:ℝ)*F/((p:ℝ)*B))/N by field_simp,abs_div,abs_of_pos hn0]
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith,by linarith⟩) hn0.le) e3

/- Limits along fixed rows and fixed positive columns. -/

private theorem row_limit {d : ℕ} (hd : 0<d) :
    Tendsto (fun N : ℕ => (row N d : ℝ)/N) atTop (𝓝 (weight d)) := by
  let B := 2^d
  have he : d<2^d := Nat.lt_two_pow_self
  have hper x j : good d (x+B*j)=good d x := by
    rw [←pair_full he,←pair_full he]; simpa [B] using pair_period d d x 0 j
  have hsum : (∑ q ∈ range B,good d q)=free d d := by
    simpa only [pair_full he] using row_at d d
  have mass : (free d d : ℝ)*(2:ℝ)^d.bitIndices.length=B := by exact_mod_cast free_mass he
  have hlim := periodic_mean (good d) d B hd (by dsimp [B]; positivity) hper
  rw [hsum,show (free d d : ℝ)/((d:ℝ)*B)=weight d by
    unfold weight; have hpos : (0:ℝ)<B := by dsimp [B]; positivity
    field_simp; nlinarith [mass]] at hlim
  have hs := hlim.sub (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  rw [sub_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hm : 0<N/d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hN)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (n:=N/d) (by omega)
  have hr : (∑ q ∈ range (N/d),good d q)=row N d+1 := by
    rw [row_eq hd,card_filter,hm,sum_range_succ',sum_range_succ']
    simp only [good_zero,lt_self_iff_false,false_and,if_false,add_zero]
    congr 1
    apply sum_congr rfl; intro q _
    have h := good_le d (q+1)
    split <;> omega
  change (↑(∑ q ∈ range (N/d),good d q) : ℝ)/N-1/N=(row N d : ℝ)/N
  rw [hr,Nat.cast_add,Nat.cast_one,add_div]; ring

private theorem odd_column {q d : ℕ} (hq : Odd q) (hd : 0<d) : good d q = 0 := by
  obtain ⟨s,b,hb,e⟩ := Nat.exists_eq_two_pow_mul_odd (n:=d) (by omega)
  subst d
  have B (z : ℕ) (hz : Odd z) : (2^s*z).testBit s = true := by
    simp [Nat.testBit_eq_decide_div_mod_eq,Nat.odd_iff.mp hz]
  have hh : (2^s*b) &&& ((2^s*b)*q)≠0 := by
    intro h
    have hh := congrArg (fun n : ℕ => n.testBit s) h
    simp [Nat.testBit_and,B b hb,Nat.mul_assoc,B (b*q) (hb.mul hq)] at hh
  simp [good,hh]

private theorem col_limit {q : ℕ} (hq : 0<q) :
    Tendsto (fun N : ℕ => (col N q : ℝ)/N) atTop (𝓝 0) := by
  obtain ⟨s,b,hb,e⟩ := Nat.exists_eq_two_pow_mul_odd (n:=q) (by omega)
  by_cases hs : s=0
  · have hodd : Odd q := by simpa [e,hs] using hb
    have hz (N : ℕ) : col N q=0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨d,r⟩ ht
      obtain ⟨ht,hr⟩ := mem_filter.mp ht
      change r=q at hr; subst r
      obtain ⟨hd,_,_,hg⟩ := mem_proper.mp ht
      rw [odd_column hodd hd] at hg; omega
    simp [hz]
  · let B := 2^(s+1)
    have hB : 1<B := Nat.one_lt_two_pow (by omega)
    let r : ℝ := (↑(B-1):ℝ)/B
    have hR : 0≤r := by dsimp [r]; positivity
    have hR' : r<1 := by
      apply (div_lt_one (by exact_mod_cast (show 0<B by omega))).mpr
      exact_mod_cast (show B-1<B by omega)
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hR hR'
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨j,hj⟩ := Metric.tendsto_atTop.mp hg (ε/2) (by positivity)
    have hj' : r^j<ε/2 := by
      simpa [Real.dist_eq,abs_of_nonneg hR] using hj j le_rfl
    let h := (s+1)*j
    let f := fun d=>pair h d q
    have hper x k : f (x+2^h*k)=f x := by simpa [f] using pair_period h x q k 0
    have hh := periodic_mean f 1 (2^h) (by decide) (by positivity) hper
    simp only [Nat.div_one,Nat.cast_one,one_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
    let a : ℝ := (↑(∑ d ∈ range (2^h),f d) : ℝ)/2^h
    have ha : a≤r^j := by
      dsimp only [a,r]
      rw [div_pow,show (2:ℝ)^h=(B:ℝ)^j by dsimp [B,h]; push_cast; rw [pow_mul]]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (∑ d ∈ range (2^h), f d)≤(B-1)^j by
        simpa [h,f,B,e] using column_blocks s b j (by omega) (Nat.odd_iff.mp hb))
    have hlim := hh.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    change Tendsto _ _ (𝓝 (a+0)) at hlim
    rw [add_zero] at hlim
    obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
    refine ⟨max n 1,fun N hN=>?_⟩
    have hn0 : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
    have hcol : col N q ≤ (∑ d ∈ range N,f d)+1 := by
      apply (col_bound N q).trans
      rw [sum_range_succ]
      exact Nat.add_le_add (sum_le_sum fun d _=>good_le_pair h d q) (good_le _ _)
    have hcol' : (col N q:ℝ)/N ≤ (↑(∑ d ∈ range N,f d):ℝ)/N+1/N := by
      rw [←add_div]; apply div_le_div_of_nonneg_right _ hn0.le; exact_mod_cast hcol
    have H := hn N (by omega)
    change dist ((↑(∑ d ∈ range N,f d):ℝ)/N+1/N) a < ε/2 at H
    rw [Real.dist_eq,abs_lt] at H
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
    linarith

/- Uniform estimates for pairs whose smaller coordinate is large. -/

private def tag (t : ℕ × ℕ) := Nat.log 2 (min t.1 t.2)

private def shell (N i : ℕ) := (proper N).filter (fun t => tag t=i)
private def tail (N K : ℕ) := (proper N).filter (fun t => 2^K ≤ min t.1 t.2)

private def rect (i A B : ℕ) :=
  ((range A) ×ˢ (range B)).filter (fun t=>pair i t.1 t.2=1)

private theorem card_rect (i a b : ℕ) : (rect i (2^i*a) (2^i*b)).card=a*b*3^i := by
  rw [rect,card_filter,sum_product,← rectangle i a b]
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro q hq
  change (if pair i d q=1 then 1 else 0)=pair i d q
  have H : pair i d q≤1 := ok_le .. 
  split <;> omega

private theorem shell_bound (N i : ℕ) : ((shell N i).card : ℝ) ≤ 8*N*(3/4:ℝ)^i := by
  let D := 2^i
  have hD : 0<D := by dsimp [D]; positivity
  let M := N/D/D+1
  have hM : N/D<D*M := Nat.lt_mul_div_succ _ hD
  have hmin {d q : ℕ} (ht : (d,q) ∈ shell N i) :
      D≤ min d q ∧ min d q<D*2 ∧ d*q≤N ∧ pair i d q=1 := by
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    obtain ⟨hd,hq,hn,hg⟩ := mem_proper.mp ht
    change Nat.log 2 (min d q)=i at he
    have hm : min d q≠0 := by omega
    have h₁ := Nat.pow_log_le_self 2 hm
    have h₂ := Nat.lt_pow_succ_log_self (b:=2) (by decide) (min d q)
    rw [he] at h₁
    rw [he,pow_succ] at h₂
    have hg' := good_le_pair i d q
    have hh : pair i d q≤1 := ok_le ..
    exact ⟨h₁,h₂,(Nat.mul_le_mul_left _ (Nat.le_succ _)).trans hn,by omega⟩
  by_cases hsq : D*D≤N
  · have hcover : shell N i ⊆ rect i (D*2) (D*M) ∪ rect i (D*M) (D*2) := by
      rintro ⟨d,q⟩ ht
      obtain ⟨hlo,hhi,hn,hg⟩ := hmin ht
      have hd : d≤N/D := (Nat.le_div_iff_mul_le hD).mpr
        ((Nat.mul_le_mul_left d (hlo.trans (min_le_right _ _))).trans hn)
      have hq : q≤N/D := (Nat.le_div_iff_mul_le hD).mpr (by
        rw [mul_comm]; exact (Nat.mul_le_mul_right q (hlo.trans (min_le_left _ _))).trans hn)
      apply mem_union.mpr
      by_cases H : d≤q
      · rw [min_eq_left H] at hhi
        exact Or.inl (mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hhi,mem_range.mpr (hq.trans_lt hM)⟩,hg⟩)
      · rw [min_eq_right (by omega)] at hhi
        exact Or.inr (mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (hd.trans_lt hM),mem_range.mpr hhi⟩,hg⟩)
    have hc := (card_le_card hcover).trans (card_union_le _ _)
    rw [show (rect i (D*2) (D*M)).card=2*M*3^i from card_rect i 2 M,
      show (rect i (D*M) (D*2)).card=M*2*3^i from card_rect i M 2] at hc
    have hm : M*(D*D)≤2*N := by
      have h := Nat.div_mul_le_self N (D*D)
      dsimp only [M]; rw [Nat.div_div_eq_div_mul,add_mul,one_mul]; omega
    have hn : (shell N i).card*(4^i)≤8*N*3^i := by
      rw [show (4:ℕ)^i=D*D by dsimp [D]; rw [←mul_pow]; rfl]
      calc _ ≤ (2*M*3^i+M*2*3^i)*(D*D) := Nat.mul_le_mul_right _ hc
           _ = (M*(D*D))*(4*3^i) := by ring
           _ ≤ (2*N)*(4*3^i) := Nat.mul_le_mul_right _ hm
           _ = _ := by ring
    rw [div_pow,←mul_div_assoc,le_div_iff₀ (by positivity)]
    exact_mod_cast hn
  · have hz : shell N i=∅ := eq_empty_iff_forall_notMem.mpr (by
      rintro ⟨d,q⟩ ht
      obtain ⟨hlo,_,hn,_⟩ := hmin ht
      exact hsq ((Nat.mul_le_mul (hlo.trans (min_le_left _ _)) (hlo.trans (min_le_right _ _))).trans hn))
    rw [hz,card_empty,Nat.cast_zero]
    positivity

private theorem tail_bound (N K : ℕ) : ((tail N K).card : ℝ) ≤ 32*N*(3/4:ℝ)^K := by
  have ht : Set.MapsTo tag (tail N K) (Ico K (N+1)) := by
    rintro ⟨d,q⟩ ht
    obtain ⟨hp,hm⟩ := mem_filter.mp ht
    obtain ⟨hd,hq,hn,hg⟩ := mem_proper.mp hp
    have hd' : d≤N := (Nat.le_mul_of_pos_right d (show 0<q+1 by omega)).trans hn
    exact mem_Ico.mpr ⟨Nat.le_log_of_pow_le (by decide) hm,
      Nat.lt_succ_of_le ((Nat.log_le_self _ _).trans ((min_le_left d q).trans hd'))⟩
  have ha : ∀ i, ((tail N K).filter (fun t=>tag t=i)).card ≤ (shell N i).card := by
    intro i; apply card_le_card
    intro t ht
    obtain ⟨ht,hh⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨(mem_filter.mp ht).1,hh⟩
  have hs : ∀ m, (∑ i ∈ Ico K m, (3/4:ℝ)^i) ≤ 4*(3/4:ℝ)^K := by
    intro m
    by_cases he : K≤ m
    · have H : (∑ i ∈ Ico K m, (3/4:ℝ)^i)=4*((3/4:ℝ)^K-(3/4:ℝ)^m) := by
        induction m,he using Nat.le_induction with
        | base => simp
        | succ m hm ih => rw [sum_Ico_succ_top hm,ih,pow_succ]; ring
      rw [H]; have : 0≤(3/4:ℝ)^m := by positivity
      linarith
    · simp [Ico_eq_empty_of_le (by omega : m≤K)]; positivity
  rw [card_eq_sum_card_fiberwise ht,Nat.cast_sum]
  calc _ ≤ ∑ i ∈ Ico K (N+1),8*N*(3/4:ℝ)^i := by
         apply sum_le_sum; intro i hi
         exact (show (((tail N K).filter (fun t=>tag t=i)).card : ℝ) ≤ ((shell N i).card : ℝ) by exact_mod_cast ha i).trans (shell_bound _ _)
       _ = (8*(N:ℝ)) * (∑ i ∈ Ico K (N+1),(3/4:ℝ)^i) := (mul_sum ..).symm
       _ ≤ (8*(N:ℝ)) * (4*(3/4:ℝ)^K) := mul_le_mul_of_nonneg_left (hs _) (by positivity)
       _ = _ := by ring

/- Passage from the finite row and column estimates to the full limit. -/

private theorem small_fibers (s : Finset (ℕ×ℕ)) (g : ℕ×ℕ → ℕ)
    (hg : ∀ t ∈ s,0<g t) (L : ℕ) :
    (∑ k ∈ range L,(s.filter (fun t=>g t=k+1)).card) =
      (s.filter (fun t=>g t-1<L)).card := by
  have hh := sum_card_fiberwise_eq_card_filter s (range L) (fun t=>g t-1)
  simp only [mem_range] at hh
  rw [←hh]
  apply sum_congr rfl
  intro k _
  congr 1; apply filter_congr; intro t ht
  have := hg t ht
  omega

private noncomputable def rows (N L : ℕ) : ℝ := ∑ k ∈ range L,(row N (k+1) : ℝ)/N
private noncomputable def cols (N L : ℕ) : ℝ := ∑ k ∈ range L,(col N (k+1) : ℝ)/N
private noncomputable def ws (L : ℕ) := ∑ k ∈ range L,weight (k+1)

private theorem row_sums (L : ℕ) : Tendsto (fun N=>rows N L) atTop (𝓝 (ws L)) :=
  tendsto_finsetSum _ fun k _=>row_limit (by omega)
private theorem col_sums (L : ℕ) : Tendsto (fun N=>cols N L) atTop (𝓝 0) := by
  simpa only [cols,sum_const_zero] using tendsto_finsetSum (range L)
    (f:=fun k N=>(col N (k+1):ℝ)/N) (a:=fun _=>0) (fun k _=>col_limit (by omega))

private theorem lower (N L : ℕ) : rows N L ≤ ((proper N).card:ℝ)/N := by
  unfold rows
  rw [←sum_div,←Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show (∑ k ∈ range L,row N (k+1))≤(proper N).card by
    unfold row
    rw [small_fibers _ Prod.fst (by rintro ⟨d,q⟩ ht; exact (mem_proper.mp ht).1)]
    exact card_le_card (filter_subset ..))

private theorem upper (N K : ℕ) (hN : 0<N) : ((proper N).card : ℝ)/N ≤
    rows N (2^K)+cols N (2^K)+32*(3/4:ℝ)^K := by
  let L := 2^K
  let R := (proper N).filter (fun t=>t.1-1<L)
  let C := (proper N).filter (fun t=>t.2-1<L)
  have hc : proper N ⊆ R ∪ C ∪ tail N K := by
    rintro ⟨d,q⟩ ht
    by_cases hr : d-1<L
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ht,hr⟩))
    by_cases hq : q-1<L
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ht,hq⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨ht,(show L≤ min d q by omega)⟩)
  have hr := small_fibers (proper N) Prod.fst (by rintro ⟨d,q⟩ ht; exact (mem_proper.mp ht).1) L
  have hq := small_fibers (proper N) Prod.snd (by rintro ⟨d,q⟩ ht; exact (mem_proper.mp ht).2.1) L
  have H : (proper N).card ≤ (∑ k ∈ range L,row N (k+1))+
      (∑ k ∈ range L,col N (k+1))+(tail N K).card := by
    unfold row col; rw [hr,hq]
    exact (card_le_card hc).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  have H' : ((proper N).card:ℝ)≤(∑ k ∈ range L,(row N (k+1):ℝ))+
      (∑ k ∈ range L,(col N (k+1):ℝ))+(tail N K).card := by exact_mod_cast H
  have hn0 : (0:ℝ)<N := by exact_mod_cast hN
  change _ ≤ rows N L+cols N L+_
  unfold rows cols
  rw [←sum_div,←sum_div,←add_div,div_le_iff₀ hn0,add_mul,div_mul_cancel₀ _ hn0.ne']
  linarith [tail_bound N K]

private theorem bounded (N : ℕ) : ((proper N).card:ℝ)/N ≤ 32 := by
  have ht : tail N 0=proper N := by
    apply filter_true_of_mem
    rintro ⟨d,q⟩ h
    obtain ⟨hd,hq,_,_⟩ := mem_proper.mp h
    change 2^0≤ min d q
    simp; omega
  have h := tail_bound N 0
  rw [ht,pow_zero,mul_one] at h
  by_cases hN : N=0
  · simp [hN]
  · exact (div_le_iff₀ (by exact_mod_cast (show 0<N by omega))).mpr h

private theorem full_mean : Summable (fun k : ℕ=>weight (k+1)) ∧
    Tendsto (fun N : ℕ=>((proper N).card:ℝ)/N) atTop (𝓝 (∑' k : ℕ,weight (k+1))) := by
  have hw : Summable (fun k : ℕ=>weight (k+1)) := by
    apply summable_of_sum_range_le (c:=32) (fun k=>by unfold weight; positivity)
    intro L
    exact le_of_tendsto_of_tendsto' (row_sums L) tendsto_const_nhds (fun N=>(lower N L).trans (bounded N))
  refine ⟨hw,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  let S := ∑' k : ℕ,weight (k+1)
  have hp : Tendsto (fun K : ℕ=>32*(3/4:ℝ)^K) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(32:ℝ))).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r:=(3/4:ℝ)) (by norm_num) (by norm_num))
  obtain ⟨k,hk⟩ := Metric.tendsto_atTop.mp hp (ε/4) (by positivity)
  obtain ⟨l,hl⟩ := Metric.tendsto_atTop.mp hw.hasSum.tendsto_sum_nat (ε/4) (by positivity)
  let K := max k l
  let L := 2^K
  have hK : 32*(3/4:ℝ)^K<ε/4 := by
    have hh := hk K (le_max_left ..)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hh
    exact hh
  have hL : l≤L := (le_max_right k l).trans ((Nat.lt_two_pow_self (n:=K)).le)
  have he := hl L hL
  change dist (ws L) S < ε/4 at he
  rw [Real.dist_eq,abs_lt] at he
  obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp (row_sums L) (ε/4) (by positivity)
  obtain ⟨m,hm⟩ := Metric.tendsto_atTop.mp (col_sums L) (ε/4) (by positivity)
  refine ⟨max (max n m) 1,fun N hN=>?_⟩
  have hr := hn N (by omega)
  have hc := hm N (by omega)
  rw [Real.dist_eq,abs_lt] at hr hc
  have hlow := lower N L
  have hu := upper N K (by omega)
  change _ ≤ rows N L+cols N L+_ at hu
  change dist (((proper N).card:ℝ)/N) S<ε
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end A246600Proof

open OMA.S_oeis_a246600 A246600Proof Filter Topology in
theorem OMA.solution : type_of% @OMA.S_oeis_a246600.main := by
  obtain ⟨hs,hm⟩ := full_mean
  refine ⟨hs,((tendsto_const_nhds (x:=(1:ℝ))).add hm).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [←Nat.cast_sum,sum_term,Nat.cast_add,add_div,div_self (by exact_mod_cast (show N≠0 by omega))]

