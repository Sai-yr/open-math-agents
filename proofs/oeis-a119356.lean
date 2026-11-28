import OMAStatements.S_oeis_a119356

/-!
# Density of squarefree square pyramidal numbers

After multiplying the sum of squares by six, its three linear factors
are pairwise coprime. The primes two and three give a joint local
condition modulo 216. Each larger prime excludes three classes modulo
its square, so the Chinese remainder theorem gives the finite densities.
For an index below N a missing prime square divides a positive linear
factor of size at most 2N+1. Summing the large-square errors uniformly
justifies the passage from finite products to natural density.
-/

namespace A119356Proof
open OMA.S_oeis_a119356 Finset

private def cubic (n : ℕ) := n*(n+1)*(2*n+1)

private theorem six_sum (n : ℕ) : 6*pyramidal n=cubic n := by
  induction n with
  | zero => simp [pyramidal,cubic]
  | succ n ih =>
    have eq : pyramidal (n+1)=pyramidal n+(n+1)^2 := sum_range_succ _ _
    rw [eq,Nat.mul_add,ih]; unfold cubic; ring

private def smallOK (n : ℕ) := ¬24∣cubic n ∧ ¬54∣cubic n

private instance (n : ℕ) : Decidable (smallOK n) := inferInstanceAs (Decidable (¬24∣cubic n ∧ ¬54∣cubic n))

private theorem cubic_mod {a b M : ℕ} (h : a≡b [MOD M]) : cubic a≡cubic b [MOD M] :=
  (h.mul (h.add_right 1)).mul ((h.mul_left 2).add_right 1)

private theorem small_iff (n : ℕ) : smallOK n ↔ ¬2^2∣pyramidal n ∧ ¬3^2∣pyramidal n := by
  have e := six_sum n
  unfold smallOK
  rw [←e,show 24=6*2^2 by decide,show 54=6*3^2 by decide]
  simp only [Nat.mul_dvd_mul_iff_left (by decide : 0<6)]

private theorem small_period (n : ℕ) : smallOK (n%216) ↔ smallOK n := by
  have h := cubic_mod (Nat.mod_modEq n 216)
  have h1 := h.of_dvd (by decide : 24∣216)
  have h2 := h.of_dvd (by decide : 54∣216)
  unfold smallOK
  exact and_congr (not_congr (h1.dvd_iff dvd_rfl)) (not_congr (h2.dvd_iff dvd_rfl))

private theorem small_card : ((range 216).filter smallOK).card=144 := by decide +kernel

private def bad (q : ℕ) : Finset ℕ := {0,q-1,q/2}
private def good (q : ℕ) (n : ℕ) := n%q ∉ bad q

private instance (q n : ℕ) : Decidable (good q n) := inferInstanceAs (Decidable (n%q ∉ bad q))

private theorem three_classes (q : ℕ) (hq : 5≤q) (odd : q%2=1) (n : ℕ) :
    n%q ∈ bad q ↔ q∣n ∨ q∣n+1 ∨ q∣2*n+1 := by
  let u:=n%q
  have hq0 : 0<q := by omega
  have hu : u<q := Nat.mod_lt _ hq0
  have hm : u≡n [MOD q] := Nat.mod_modEq _ _
  have h1 := (hm.add_right 1).dvd_iff (dvd_refl q)
  have h2 := ((hm.mul_left 2).add_right 1).dvd_iff (dvd_refl q)
  have hd1 : q∣u+1 ↔ u=q-1 := by
    constructor
    · intro hd; have := Nat.le_of_dvd (Nat.succ_pos u) hd; omega
    · intro h; rw [show u+1=q by omega]
  have hd2 : q∣2*u+1 ↔ u=q/2 := by
    constructor
    · rintro ⟨t,ht⟩
      have tpos : 0<t := by
        by_contra! hz
        have he : t=0 := by omega
        rw [he,mul_zero] at ht; omega
      have tle : t≤1 := by by_contra! hh; have := Nat.mul_le_mul_left q (show 2≤t by omega); omega
      have : t=1 := by omega
      rw [this,mul_one] at ht; omega
    · intro h; rw [show 2*u+1=q by omega]
  change u∈bad q ↔ _
  rw [←hm.dvd_iff (dvd_refl q),←h1,←h2,hd1,hd2]
  have hd : q∣u ↔ u=0 := ⟨fun h=>by by_contra! hz; have := Nat.le_of_dvd (by omega : 0<u) h; omega,
    fun h=>h ▸ dvd_zero _⟩
  rw [hd]; simp [bad]

private theorem good_card (q : ℕ) (hq : 5≤q) : ((range q).filter (good q)).card=q-3 := by
  classical
  have eq : (range q).filter (good q) = range q \ bad q := by
    ext i; simp only [mem_filter,mem_sdiff,mem_range,good]
    by_cases hi : i<q <;> simp [hi,Nat.mod_eq_of_lt]
  have sub : bad q⊆range q := by intro i hi; simp [bad] at hi; simp; omega
  have hc : (bad q).card=3 := by
    simp [bad,show q-1≠q/2 by omega,show 0≠q-1 by omega,show 0≠q/2 by omega]
  rw [eq,card_sdiff_of_subset sub,card_range,hc]

private theorem local_prime (n p : ℕ) (hp : p.Prime) (h5 : 5≤p) :
    good (p^2) n ↔ ¬p^2∣pyramidal n := by
  have hpr : p.Coprime 6 := by
    rw [show 6=2*3 by decide,Nat.coprime_mul_iff_right]
    exact ⟨(Nat.coprime_primes hp Nat.prime_two).mpr (by omega),
      (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)⟩
  have hq := hpr.pow_left 2
  have e : p^2∣cubic n ↔ p^2∣pyramidal n := by rw [←six_sum]; exact hq.dvd_mul_left
  have a : n.Coprime (n+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have b : n.Coprime (2*n+1) := by rw [add_comm,Nat.coprime_add_mul_right_right]; simp
  have c : (n+1).Coprime (2*n+1) := by
    rw [show 2*n+1=n+(n+1) by omega,Nat.coprime_add_self_right]; exact a.symm
  have hpp : IsPrimePow (p^2) := hp.isPrimePow.pow (by decide)
  have cp := (Nat.coprime_mul_iff_left.mpr ⟨b,c⟩).isPrimePow_dvd_mul hpp
  have e' : p^2∣cubic n ↔ p^2∣n ∨ p^2∣n+1 ∨ p^2∣2*n+1 := by
    rw [cubic,cp,a.isPrimePow_dvd_mul hpp,or_assoc]
  have hodd := hp.odd_of_ne_two (by omega)
  have od : p^2%2=1 := Nat.odd_iff.mp (hodd.pow)
  unfold good
  rw [three_classes _ (by nlinarith) od,←e',e]

end A119356Proof

namespace A119356Proof
open Finset

private theorem crt_count (m q : ℕ) (hm : 0< m) (hq : 0<q) (co : m.Coprime q)
    (f g : ℕ → Prop) [DecidablePred f] [DecidablePred g]
    (hf : ∀n, f (n%m) ↔ f n) (hg : ∀n,g (n%q) ↔ g n) :
    ((range (m*q)).filter (fun n=>f n ∧ g n)).card =
      ((range m).filter f).card*((range q).filter g).card := by
  rw [←card_product]
  apply card_bij (fun x _=>(x%m,x%q))
  · intro x hx
    obtain ⟨_,hx1,hx2⟩ := mem_filter.mp hx
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hm),(hf _).mpr hx1⟩,
      mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hq),(hg _).mpr hx2⟩⟩
  · intro x hx y hy h
    have hxs := mem_range.mp (mem_filter.mp hx).1
    have hys := mem_range.mp (mem_filter.mp hy).1
    have h₁ : x≡y [MOD m] := congrArg Prod.fst h
    have h₂ : x≡y [MOD q] := congrArg Prod.snd h
    have e := (Nat.modEq_and_modEq_iff_modEq_mul co).mp ⟨h₁,h₂⟩
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hxs,Nat.mod_eq_of_lt hys] using e
  · rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    obtain ⟨ha,fa⟩ := mem_filter.mp ha
    obtain ⟨hb,fb⟩ := mem_filter.mp hb
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    let x:=Nat.chineseRemainder co a b
    have xa : x.val%m=a := by
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt ha'] using x.property.1
    have xb : x.val%q=b := by
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt hb'] using x.property.2
    exact ⟨x.val,mem_filter.mpr ⟨mem_range.mpr (Nat.chineseRemainder_lt_mul co a b hm.ne' hq.ne'),
      (hf _).mp (by rw [xa]; exact fa),(hg _).mp (by rw [xb]; exact fb)⟩,Prod.ext xa xb⟩

private theorem periodic_error (m N : ℕ) (hm : 0< m) (f : ℕ → Prop) [DecidablePred f]
    (hf : ∀n, f (n%m) ↔ f n) :
    |(((range N).filter f).card:ℝ) - N * ((((range m).filter f).card:ℝ)/m)| ≤ m := by
  let C:=((range m).filter f).card
  have h (a : ℕ) : (∑ n ∈ range a, (if f n then (1:ℝ) else 0)) = ((range a).filter f).card :=
    sum_boole _ _
  have blk (q : ℕ) : (∑ i ∈ range (q*m), (if f i then (1:ℝ) else 0)) = q*C := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.add_mul,one_mul,sum_range_add,ih]
      have he : (∑ i ∈ range m,(if f (q*m+i) then (1:ℝ) else 0))=C := by
        rw [←h]
        apply sum_congr rfl; intro i hi
        have eq : (q*m+i)%m=i := by simp [Nat.add_mod,Nat.mod_eq_of_lt (mem_range.mp hi)]
        have ff : f (q*m+i) ↔ f i := by simpa only [eq] using (hf (q*m+i)).symm
        simp only [ff]
      rw [he]; push_cast; ring
  let q:=N/m
  let t:=N%m
  have ht : t< m := Nat.mod_lt _ hm
  have dc : q*m+t=N := by simpa [q,t,Nat.mul_comm] using Nat.div_add_mod N m
  let z:=∑i ∈ range t, if f (q*m+i) then (1:ℝ) else 0
  have hdec : (((range N).filter f).card:ℝ) = q*C+z := by rw [←h,←dc,sum_range_add,blk]
  have h0 : 0≤z := sum_nonneg (by intro i hi; split_ifs <;> norm_num)
  have h1 : z≤t := by
    calc _ ≤ ∑ _i ∈ range t,(1:ℝ) := sum_le_sum (by intro i hi; split_ifs <;> norm_num)
         _ = _ := by simp
  have hc : (C:ℝ)≤ m := by exact_mod_cast ((card_le_card (filter_subset f (range m))).trans_eq (card_range m))
  have mpos : (0:ℝ)< m := by exact_mod_cast hm
  have f0 : 0≤(C:ℝ)/m := by positivity
  have f1 : (C:ℝ)/m≤1 := (div_le_one mpos).mpr hc
  have hdc : (q:ℝ)*m+t=N := by exact_mod_cast dc
  have e : (q:ℝ)*C+z - N*((C:ℝ)/m)=z - t*((C:ℝ)/m) := by
    rw [←hdc]; field_simp; ring
  rw [hdec]; change |(q:ℝ)*C+z-N*((C:ℝ)/m)|≤ m
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left f1 (Nat.cast_nonneg t)
  have h3 := mul_nonneg (Nat.cast_nonneg t) f0
  have h4 : (t:ℝ)< m := by exact_mod_cast ht
  apply abs_le.mpr; constructor <;> linarith

end A119356Proof

namespace A119356Proof
open Finset OMA.S_oeis_a119356
open scoped Classical

private def eligible (S : Finset ℕ) := ∀ p ∈ S, p.Prime ∧ 5≤p

private def period (S : Finset ℕ) := 216*∏ p ∈ S, p^2
private def test (S : Finset ℕ) (n : ℕ) := smallOK n ∧ ∀p ∈ S,good (p^2) n

private instance (S : Finset ℕ) (n : ℕ) : Decidable (test S n) :=
  inferInstanceAs (Decidable (smallOK n ∧ ∀ p ∈ S,good (p^2) n))

private theorem period_pos (S : Finset ℕ) (hs : eligible S) : 0<period S := by
  apply Nat.mul_pos (by decide)
  apply prod_pos; intro p hp; have := (hs p hp).2; positivity

private theorem test_period (S : Finset ℕ) (n : ℕ) : test S (n%period S) ↔ test S n := by
  have h0 : 216∣period S := dvd_mul_right _ _
  have he : smallOK (n%period S) ↔ smallOK n := by
    rw [←small_period (n%period S),Nat.mod_mod_of_dvd _ h0,small_period]
  have he' (p : ℕ) (hp : p∈S) : good (p^2) (n%period S) ↔ good (p^2) n := by
    have h1 : p^2∣period S := (dvd_prod_of_mem (fun i : ℕ=>i^2) hp).trans (dvd_mul_left _ _)
    simp only [good,Nat.mod_mod_of_dvd _ h1]
  unfold test; rw [he]; exact and_congr_right (fun _=>forall_congr' (fun p=>forall_congr' (he' p)))

private theorem test_card (S : Finset ℕ) (hs : eligible S) :
    ((range (period S)).filter (test S)).card=144*∏ p ∈ S,(p^2-3) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [period,prod_empty,mul_one]
    have e : (range 216).filter (test ∅) = (range 216).filter smallOK :=
      filter_congr (fun n _=>by simp [test])
    rw [e]; exact small_card
  | insert p S hp ih =>
    have hprime := (hs p (mem_insert_self ..)).1
    have h5 := (hs p (mem_insert_self ..)).2
    have hs' : eligible S := fun v hv=>hs v (mem_insert_of_mem hv)
    have h0 : (period S).Coprime (p^2) := by
      apply Nat.Coprime.pow_right
      unfold period
      rw [Nat.coprime_mul_iff_left,show 216=2^3*3^3 by decide,Nat.coprime_mul_iff_left]
      refine ⟨⟨(Nat.coprime_primes Nat.prime_two hprime).mpr (by omega) |>.pow_left 3,
        (Nat.coprime_primes Nat.prime_three hprime).mpr (by omega) |>.pow_left 3⟩,?_⟩
      apply Nat.Coprime.prod_left; intro r hr
      exact ((Nat.coprime_primes (hs' r hr).1 hprime).mpr (ne_of_mem_of_not_mem hr hp)).pow_left 2
    have eq : period (insert p S)=period S*p^2 := by rw [period,period,prod_insert hp]; ring
    have tt : test (insert p S) = fun n=>test S n ∧ good (p^2) n := by
      funext n; apply propext; simp [test]; tauto
    rw [eq]
    have ef : (range (period S*p^2)).filter (test (insert p S)) =
        (range (period S*p^2)).filter (fun n=>test S n ∧ good (p^2) n) :=
      filter_congr (fun n _=>Iff.of_eq (congrFun tt n))
    rw [ef,crt_count _ _ (period_pos _ hs') (by positivity) h0 _ _
      (test_period S) (fun n=>by simp [good]),ih hs',good_card _ (by nlinarith),prod_insert hp]
    ring

private def cutoff (B : ℕ) := (Icc 5 B).filter Nat.Prime

private theorem cutoff_ok (B : ℕ) : eligible (cutoff B) := by
  intro p hp; obtain ⟨hi,hp⟩ := mem_filter.mp hp; exact ⟨hp,(mem_Icc.mp hi).1⟩

private theorem factor_rate (S : Finset ℕ) (hs : eligible S) :
    ((((range (period S)).filter (test S)).card:ℝ)/(period S:ℝ)) =
      (2/3:ℝ)*∏ p ∈ S,(1-3/(p:ℝ)^2) := by
  rw [test_card _ hs,period]
  push_cast
  rw [mul_div_mul_comm,←Finset.prod_div_distrib]
  have h : ∀p ∈ S, (((p^2-3:ℕ):ℝ)/(p:ℝ)^2) = 1-3/(p:ℝ)^2 := by
    intro p hp
    have h5 := (hs p hp).2
    rw [Nat.cast_sub (by nlinarith : 3≤p^2),Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  rw [prod_congr rfl h]
  norm_num

private theorem cutoff_rate (B : ℕ) (hb : 3≤B) :
    ((((range (period (cutoff B))).filter (test (cutoff B))).card:ℝ)/(period (cutoff B):ℝ)) = 4*euler B := by
  rw [factor_rate _ (cutoff_ok B),euler]
  have eq : (range (B+1)).filter Nat.Prime=insert 2 (insert 3 (cutoff B)) := by
    ext p; simp only [cutoff,mem_insert,mem_filter,mem_range,mem_Icc]
    constructor
    · rintro ⟨hl,hp⟩
      by_cases h5 : 5≤p
      · exact Or.inr (Or.inr ⟨⟨h5,by omega⟩,hp⟩)
      · have : p≤4 := by omega
        interval_cases p <;> norm_num at *
    · rintro (rfl|rfl|⟨⟨_,hp⟩,pp⟩)
      · exact ⟨by omega,Nat.prime_two⟩
      · exact ⟨by omega,Nat.prime_three⟩
      · exact ⟨by omega,pp⟩
  have h2 : 2∉insert 3 (cutoff B) := by simp [cutoff]
  have h3 : 3∉cutoff B := by simp [cutoff]
  rw [eq,prod_insert h2,prod_insert h3]; norm_num; ring

end A119356Proof

namespace A119356Proof
open Finset OMA.S_oeis_a119356
open scoped Classical

private theorem reciprocal_tail (K N : ℕ) (hk : 0<K) :
    (∑ t ∈ range N, 1/(((K+t+1:ℕ):ℝ)^2)) ≤ 1/(K:ℝ) - 1/(K+N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]; push_cast
    have hpos : (0:ℝ)<K+N := by positivity
    have hstep : 1/((K:ℝ)+N+1)^2 ≤ 1/(K+N:ℝ)-1/(K+N+1:ℝ) := by
      field_simp; nlinarith
    push_cast at ih
    rw [show (K:ℝ)+(N+1)=K+N+1 by ring]
    linarith

private theorem class_bound (N q v : ℕ) (_hq : 0<q) :
    ((range N).filter (fun n=>n%q=v)).card ≤ N/q+1 := by
  let S := (range N).filter (fun n=>n%q=v)
  have hsub : S.image (fun n=>n/q) ⊆ range (N/q+1) := by
    intro j hj; obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hn).1).le))
  have hi : Set.InjOn (fun n : ℕ=>n/q) (↑S : Set ℕ) := by
    intro x hx y hy h
    have xh := (mem_filter.mp hx).2
    have yh := (mem_filter.mp hy).2
    have e1 := Nat.div_add_mod x q
    have e2 := Nat.div_add_mod y q
    change x/q=y/q at h
    rw [h,xh] at e1; rw [yh] at e2; omega
  have hh := card_le_card hsub
  rwa [card_image_of_injOn hi,card_range] at hh

private def fails (N q : ℕ) := (range N).filter (fun n=>n%q∈bad q)

private theorem fail_bound (N q : ℕ) (hq : 0<q) : (fails N q).card≤3*(N/q+1) := by
  let f := fun v=>(range N).filter (fun n=>n%q=v)
  have sb : fails N q ⊆ (bad q).biUnion f := by
    intro n hn; obtain ⟨hr,hh⟩:=mem_filter.mp hn
    exact mem_biUnion.mpr ⟨_,hh,mem_filter.mpr ⟨hr,rfl⟩⟩
  have hb : (bad q).card≤3 := by
    unfold bad
    calc _ ≤ _ := card_insert_le ..
         _ ≤ _ := by have := card_insert_le (q-1) ({q/2}:Finset ℕ); simp at this; omega
  calc
    _ ≤ ∑ v ∈ bad q, (f v).card := (card_le_card sb).trans card_biUnion_le
    _ ≤ ∑ _v ∈ bad q,(N/q+1) := sum_le_sum (fun _ _=>class_bound _ _ _ hq)
    _ = (bad q).card*(N/q+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hb

private theorem union_bound (N B H : ℕ) (hB : 0<B) :
    (((range H).biUnion (fun t=>fails N ((B+t+1)^2))).card:ℝ) ≤
      3*(N:ℝ)/B+3*H := by
  have h : ((range H).biUnion (fun t=>fails N ((B+t+1)^2))).card ≤
      ∑ t ∈ range H,3*(N/((B+t+1)^2)+1) := by
    exact card_biUnion_le.trans (sum_le_sum (fun _ _=>fail_bound _ _ (by positivity)))
  have h1 : (((range H).biUnion (fun t=>fails N ((B+t+1)^2))).card:ℝ) ≤
      ∑ t ∈ range H,3*(((N/((B+t+1)^2):ℕ):ℝ)+1) := by exact_mod_cast h
  have h2 : (∑ t ∈ range H,((N/((B+t+1)^2):ℕ):ℝ)) ≤ N*(1/(B:ℝ)) := by
    calc
      _ ≤ ∑ t ∈ range H,(N:ℝ)*(1/(((B+t+1:ℕ):ℝ)^2)) := by
        apply sum_le_sum; intro t _
        rw [←div_eq_mul_one_div,←Nat.cast_pow]
        exact Nat.cast_div_le
      _ = (N:ℝ)*(∑ t ∈ range H,1/(((B+t+1:ℕ):ℝ)^2)) := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left ((reciprocal_tail _ _ hB).trans (sub_le_self _ (by positivity))) (Nat.cast_nonneg _)
  rw [←mul_sum, sum_add_distrib] at h1
  simp only [sum_const,card_range,nsmul_one] at h1
  linarith [show (3:ℝ)*N/B=3*(N*(1/B)) by ring]

end A119356Proof

namespace A119356Proof
open OMA.S_oeis_a119356 Finset Filter Topology

private noncomputable def fac (p : ℕ) : ℝ := 1-3/(p:ℝ)^2

private theorem fac_bounds {p : ℕ} (hp : p.Prime) : 0≤fac p ∧ fac p≤1 := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hs : (0:ℝ)<(p:ℝ)^2 := by positivity
  unfold fac
  refine ⟨sub_nonneg.mpr ((div_le_one hs).mpr (by nlinarith)),sub_le_self _ (by positivity)⟩

private theorem prod_lower (S : Finset ℕ) (hs : eligible S) :
    1 - ∑ p ∈ S, (3/(p:ℝ)^2) ≤ ∏ p ∈ S,fac p := by
  induction S using Finset.induction with
  | empty => simp
  | insert p S hp ih =>
    have h := ih (fun v hv=>hs v (mem_insert_of_mem hv))
    have hc := fac_bounds (hs p (mem_insert_self ..)).1
    have hu : ∏ v ∈ S,fac v ≤ 1 := prod_le_one (fun i hi=>(fac_bounds (hs i (mem_insert_of_mem hi)).1).1)
      (fun i hi=>(fac_bounds (hs i (mem_insert_of_mem hi)).1).2)
    rw [prod_insert hp,sum_insert hp,fac]
    have hpos : (0:ℝ)≤3/(p:ℝ)^2 := by positivity
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hu)]

private theorem cut_recip (B : ℕ) : (∑ p ∈ cutoff B, 3/(p:ℝ)^2) ≤ 3/4 := by
  have sub : cutoff B ⊆ Ico 5 (5+B) := by
    intro p hp; have h := mem_Icc.mp (mem_filter.mp hp).1
    exact mem_Ico.mpr ⟨h.1,by omega⟩
  calc
    _ ≤ ∑ p ∈ Ico 5 (5+B),3/(p:ℝ)^2 := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ =>by positivity)
    _ = 3*(∑ t ∈ range B,1/(((4+t+1:ℕ):ℝ)^2)) := by
      rw [sum_Ico_eq_sum_range,mul_sum]
      simp only [Nat.add_sub_cancel_left]
      apply sum_congr rfl
      intro i _
      rw [show 4+i+1=5+i by omega]; ring
    _ ≤ _ := by
      have h := reciprocal_tail 4 B (by decide)
      have h0 : (0:ℝ) ≤ 1/((4:ℕ)+B:ℝ) := by positivity
      have h1 := h.trans (sub_le_self _ h0)
      norm_num only [Nat.cast_ofNat] at h1
      linarith

private theorem euler_floor (B : ℕ) (hb : 3≤B) : (1/24:ℝ) ≤ euler B := by
  have he := (factor_rate _ (cutoff_ok B)).symm.trans (cutoff_rate B hb)
  have h := prod_lower (cutoff B) (cutoff_ok B)
  have hl := cut_recip B
  unfold fac at h; linarith

private theorem euler_desc : Antitone euler := by
  apply antitone_nat_of_succ_le; intro n
  have hpos : 0≤euler n := by
    exact prod_nonneg (fun i hi=>(fac_bounds (mem_filter.mp hi).2).1)
  unfold euler
  rw [range_add_one,filter_insert]
  split_ifs with h
  · rw [prod_insert (by simp)]
    have hc := (fac_bounds h).2
    exact mul_le_of_le_one_left hpos hc
  · exact le_rfl

private theorem euler_limit : ∃ C : ℝ, 0<C ∧ Tendsto euler atTop (𝓝 C) := by
  have floor (B : ℕ) : (1/24:ℝ)≤euler B := by
    exact (euler_floor (max 3 B) (le_max_left _ _)).trans (euler_desc (le_max_right _ _))
  have hb : BddBelow (Set.range euler) := ⟨1/24,by rintro _ ⟨B,rfl⟩; exact floor B⟩
  exact ⟨_,lt_of_lt_of_le (by norm_num : (0:ℝ)<1/24) (le_ciInf floor),tendsto_atTop_ciInf euler_desc hb⟩

end A119356Proof

namespace A119356Proof
open Finset OMA.S_oeis_a119356
open scoped Classical

private theorem sq_criterion (n : ℕ) :
    Squarefree (pyramidal n) ↔ ∀ p, p.Prime → ¬p^2∣pyramidal n := by
  simpa only [sq] using (Nat.squarefree_iff_prime_squarefree (n:=pyramidal n))

private theorem actual_test (n B : ℕ) (h : Squarefree (pyramidal n)) : test (cutoff B) n := by
  have hp := (sq_criterion n).mp h
  refine ⟨(small_iff n).mpr ⟨hp 2 Nat.prime_two,hp 3 Nat.prime_three⟩,?_⟩
  intro p hv
  obtain ⟨hpr,h5⟩ := cutoff_ok B p hv
  exact (local_prime n p hpr h5).mpr (hp p hpr)

private def height (N : ℕ) := Nat.sqrt (2*N+1)+1

private theorem omitted (n N B : ℕ) (hn : n<N) (ht : test (cutoff B) n)
    (hbad : ¬Squarefree (pyramidal n)) :
    n∈(range (height N)).biUnion (fun t=>fails N ((B+t+1)^2)) := by
  rw [sq_criterion] at hbad
  push Not at hbad
  obtain ⟨p,hp,hd⟩ := hbad
  have hsmall := (small_iff n).mp ht.1
  have h5 : 5≤p := by
    by_contra! h
    have ht2 : p ≠ 2 := by rintro rfl; exact hsmall.1 hd
    have ht3 : p ≠ 3 := by rintro rfl; exact hsmall.2 hd
    interval_cases p <;> norm_num at *
  have hlarge : B<p := by
    by_contra! hle
    have hv : p∈cutoff B := mem_filter.mpr ⟨mem_Icc.mpr ⟨h5,hle⟩,hp⟩
    exact (local_prime n p hp h5).mp (ht.2 p hv) hd
  have hres : n%(p^2)∈bad (p^2) := by
    by_contra hc; exact (local_prime n p hp h5).mp hc hd
  have hn0 : 0<n := by
    by_contra! h
    have e : n=0 := by omega
    subst n; exact (by decide : ¬smallOK 0) ht.1
  have bound : p^2≤2*N+1 := by
    have od : p^2%2=1 := Nat.odd_iff.mp ((hp.odd_of_ne_two (by omega)).pow)
    rcases (three_classes _ (by nlinarith) od n).mp hres with hl|hl|hl
    · have := Nat.le_of_dvd hn0 hl; omega
    · have := Nat.le_of_dvd (Nat.succ_pos n) hl; omega
    · have := Nat.le_of_dvd (Nat.succ_pos _) hl; omega
  have hroot := Nat.le_sqrt'.mpr bound
  refine mem_biUnion.mpr ⟨p-(B+1),mem_range.mpr (by unfold height; omega),?_⟩
  rw [show B+(p-(B+1))+1=p by omega]
  exact mem_filter.mpr ⟨mem_range.mpr hn,hres⟩

private theorem comparison (N B : ℕ) (hN : 0<N) (hB : 3≤B) :
    |frequency N-4*euler B| ≤ (period (cutoff B):ℝ)/N + 3/(B:ℝ) + 3*((height N:ℝ)/N) := by
  classical
  let S := (range N).filter (fun n=>Squarefree (pyramidal n))
  let T := (range N).filter (test (cutoff B))
  let U := (range (height N)).biUnion (fun t=>fails N ((B+t+1)^2))
  have hst : S⊆T := by
    intro n hn; obtain ⟨hr,hs⟩:=mem_filter.mp hn; exact mem_filter.mpr ⟨hr,actual_test n B hs⟩
  have htu : T⊆S∪U := by
    intro n hn; obtain ⟨hr,ht⟩:=mem_filter.mp hn
    by_cases hs : Squarefree (pyramidal n)
    · exact mem_union_left _ (mem_filter.mpr ⟨hr,hs⟩)
    · exact mem_union_right _ (omitted n N B (mem_range.mp hr) ht hs)
  have a : (S.card:ℝ) ≤ T.card := by exact_mod_cast card_le_card hst
  have b : (T.card:ℝ) ≤ S.card + (U.card:ℝ) := by
    exact_mod_cast ((card_le_card htu).trans (card_union_le S U))
  have c : (U.card:ℝ) ≤ 3*(N:ℝ)/B+3*height N := union_bound _ _ _ (by omega)
  have per := periodic_error (period (cutoff B)) N (period_pos _ (cutoff_ok B)) (test (cutoff B)) (test_period _)
  rw [cutoff_rate B hB] at per
  change |(T.card:ℝ)-N*(4*euler B)| ≤ _ at per
  have hpos : (0:ℝ)<N := by exact_mod_cast hN
  have tail := div_le_div_of_nonneg_right c hpos.le
  have small : (0:ℝ)≤3/(B:ℝ) + 3*((height N:ℝ)/N) := by positivity
  have per' := div_le_div_of_nonneg_right per hpos.le
  rw [←abs_of_pos hpos,←abs_div] at per'
  rw [abs_of_pos hpos,sub_div,mul_div_cancel_left₀ _ hpos.ne'] at per'
  have taileq : (3*(N:ℝ)/B+3*height N)/N=3/(B:ℝ)+3*((height N:ℝ)/N) := by
    field_simp
  rw [taileq] at tail
  have a' := div_le_div_of_nonneg_right a hpos.le
  have b' := div_le_div_of_nonneg_right b hpos.le
  rw [add_div] at b'
  change |(S.card:ℝ)/N-4*euler B|≤_
  obtain ⟨hm,hp⟩:=abs_le.mp per'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end A119356Proof

namespace A119356Proof
open OMA.S_oeis_a119356 Filter Topology Finset

private theorem root_ratio : Tendsto (fun N : ℕ => (height N:ℝ)/N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (8:ℝ)).eventually_lt_const (sq_pos_of_pos hε)
  filter_upwards [ht,eventually_ge_atTop 1] with N h Npos
  have hN : (1:ℝ) ≤ N := by exact_mod_cast Npos
  have hN0 : (0:ℝ) < N := by linarith
  let s := Nat.sqrt (2*N+1)
  have hs : (s:ℝ)^2 ≤ 2*(N:ℝ)+1 := by exact_mod_cast Nat.sqrt_le' (2*N+1)
  have hb : ((s:ℝ)+1)^2 ≤ 8*(N:ℝ) := by nlinarith [sq_nonneg ((s:ℝ)-1)]
  have he := (div_lt_iff₀ hN0).mp h
  have hh := mul_lt_mul_of_pos_right he hN0
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ hN0]
  change ((s+1 : ℕ):ℝ) < ε*N
  push_cast
  by_contra! hc
  have hz := pow_le_pow_left₀ (by positivity : 0 ≤ ε*(N:ℝ)) hc 2
  nlinarith

private theorem solved : ∃ C : ℝ, 0<C ∧ Tendsto euler atTop (𝓝 C) ∧
    Tendsto frequency atTop (𝓝 (4*C)) := by
  obtain ⟨C,hpos,hC⟩ := euler_limit
  refine ⟨C,hpos,hC,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have e1 := (Metric.tendsto_nhds.mp hC) (ε/16) (by positivity)
  have e2 := (tendsto_const_div_atTop_nhds_zero_nat (3:ℝ)).eventually_lt_const
    (show 0<ε/4 by positivity)
  obtain ⟨B,hB,h1,h2⟩ := ((eventually_ge_atTop 3).and (e1.and e2)).exists
  have e3 := (tendsto_const_div_atTop_nhds_zero_nat (period (cutoff B):ℝ)).eventually_lt_const
    (show 0<ε/4 by positivity)
  have e4 := root_ratio.eventually_lt_const (show 0<ε/12 by positivity)
  filter_upwards [eventually_ge_atTop 1,e3,e4] with N hN h3 h4
  have he := comparison N B (by omega) hB
  rw [Real.dist_eq] at h1 ⊢
  have h5 : |4*euler B-4*C|<4*(ε/16) := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    linarith
  calc
    _ ≤ |frequency N-4*euler B| + |4*euler B-4*C| := abs_sub_le .. 
    _ < ε := by linarith

end A119356Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a119356.main :=
  A119356Proof.solved
