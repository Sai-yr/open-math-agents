import OMAReductions.R_Erdos931_erdos_931_R1
import Mathlib

/-! A block of three consecutive integers beyond 18 has at least four prime divisors.
The remaining configurations with equal prime supports are checked in a finite box. -/

open Finset

namespace SmallPrimeSupport

private def smooth (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3

private lemma divisor_large {p q e : ℕ} (hp : p.Prime) (hq : p < q) (hd : q ∣ p^e) :
    p^2 ∣ q := by
  obtain ⟨i,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  have h : 2 ≤ i := by
    by_contra! hi
    interval_cases i <;> simp_all
  exact pow_dvd_pow _ h

private lemma square_factors {z e p : ℕ} (hz : 0 < z) (h : z^2 = p^e+1) :
    z-1 ∣ p^e ∧ z+1 ∣ p^e := by
  have hh : (z-1)*(z+1)=p^e := by
    have := Nat.sub_add_cancel (show 1≤z by omega)
    nlinarith
  rw [← hh]
  exact ⟨dvd_mul_right _ _,dvd_mul_left _ _⟩

private lemma odd_power_mod {p m : ℕ} (h : p^2 ≡ 1 [MOD m]) (r : ℕ) :
    p^(2*r+1) ≡ p [MOD m] := by
  rw [pow_succ,pow_mul]
  simpa using (h.pow r).mul_right p

-- For large exponents the two powers cannot differ by one.
private lemma powers_not_adjacent {a b : ℕ} (ha : 9 < 2^a) (hb : 9 < 3^b) :
    2^a+1 ≠ 3^b ∧ 3^b+1 ≠ 2^a := by
  constructor
  · intro he
    have ht : 3 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha
    have h8 : 8 ∣ 2^a := pow_dvd_pow 2 ht
    have evenB : b%2=0 := by
      by_contra hn
      have h := odd_power_mod (p:=3) (m:=8) (by decide) (b/2)
      rw [show 2*(b/2)+1=b by omega] at h
      change 3^b%8 = 3%8 at h
      omega
    let z := 3^(b/2)
    have hz : z^2=2^a+1 := by
      dsimp [z]; rw [← pow_mul,show b/2*2=b by omega,he]
    have hpos : 0<z := by dsimp [z]; positivity
    have hlarge : 3<z := by nlinarith only [ha,hz,hpos]
    obtain ⟨hm,hp⟩ := square_factors hpos hz
    have hm4 := divisor_large Nat.prime_two (show 2<z-1 by omega) hm
    have hp4 := divisor_large Nat.prime_two (show 2<z+1 by omega) hp
    change 4 ∣ z-1 at hm4
    change 4 ∣ z+1 at hp4
    omega
  · intro he
    have ht : 1 ≤ b := by
      by_contra! h
      interval_cases b; norm_num at hb
    have h3 : 3 ∣ 3^b := dvd_pow_self _ (by omega)
    have evenA : a%2=0 := by
      by_contra hn
      have h := odd_power_mod (p:=2) (m:=3) (by decide) (a/2)
      rw [show 2*(a/2)+1=a by omega] at h
      change 2^a%3 = 2%3 at h
      omega
    let z := 2^(a/2)
    have hz : z^2=3^b+1 := by
      dsimp [z]; rw [← pow_mul,show a/2*2=a by omega,he]
    have hpos : 0<z := by dsimp [z]; positivity
    have hlarge : 3<z := by nlinarith only [hb,hz,hpos]
    obtain ⟨hm,hp⟩ := square_factors hpos hz
    have div3 (d : ℕ) (hd : 1<d) (hdv : d ∣ 3^b) : 3 ∣ d := by
      obtain ⟨i,_,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdv
      apply dvd_pow_self
      rintro rfl
      simp at hd
    have hm3 := div3 (z-1) (by omega) hm
    have hp3 := div3 (z+1) (by omega) hp
    omega

private lemma pure {n p q : ℕ} (hn : 0<n) (hs : smooth n)
    (h : (p=2 ∧ q=3) ∨ (p=3 ∧ q=2)) (hq : ¬ q ∣ n) :
    ∃ a : ℕ, n=p^a := by
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd hn.ne' ?_⟩
  intro d hd hdv
  rcases hs d hd hdv with rfl | rfl <;> rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto

private lemma no_neighbors {x y : ℕ} (hx : 9<x) (hy : 9<y) (sx : smooth x) (sy : smooth y)
    (ho : ¬ 2 ∣ y) (near : x+1=y ∨ y+1=x) : False := by
  obtain ⟨b,rfl⟩ := pure (by omega : 0<y) sy (p:=3) (Or.inr ⟨rfl,rfl⟩) ho
  have hb : b≠0 := by rintro rfl; norm_num at hy
  have h3 := dvd_pow_self 3 hb
  have h3x : ¬ 3 ∣ x := by omega
  obtain ⟨a,rfl⟩ := pure (by omega : 0<x) sx (p:=2) (Or.inl ⟨rfl,rfl⟩) h3x
  exact near.elim (powers_not_adjacent hx hy).1 (powers_not_adjacent hx hy).2

private lemma smooth_consecutive {x : ℕ} (hx : 9<x) (sx : smooth x) (sy : smooth (x+1)) : False := by
  by_cases h : 2 ∣ x
  · exact no_neighbors hx (by omega) sx sy (by omega) (Or.inl rfl)
  · exact no_neighbors (by omega) hx sy sx h (Or.inr rfl)

private lemma smooth_two_apart {x : ℕ} (hx : 18<x) (sx : smooth x) (sy : smooth (x+2)) : False := by
  by_cases he : 2 ∣ x
  · obtain ⟨t,rfl⟩ := he
    have inherit {u v : ℕ} (huv : u ∣ v) (hv : smooth v) : smooth u :=
      fun p hp hd => hv p hp (hd.trans huv)
    apply smooth_consecutive (x:=t) (by omega) (inherit (dvd_mul_left _ _) sx)
    apply inherit (v:=2*t+2) _ sy
    exact ⟨2,by ring⟩
  · obtain ⟨a,ha⟩ := pure (by omega : 0<x) sx (p:=3) (Or.inr ⟨rfl,rfl⟩) he
    obtain ⟨b,hb⟩ := pure (by omega : 0<x+2) sy (p:=3) (Or.inr ⟨rfl,rfl⟩) (by omega)
    have ha0 : a≠0 := by rintro rfl; simp at ha; omega
    have hb0 : b≠0 := by rintro rfl; simp at hb
    have h1 := dvd_pow_self 3 ha0
    have h2 := dvd_pow_self 3 hb0
    omega

private lemma at_most_one_bad {n : ℕ} (S : Finset ℕ)
    (cover : ∀ x : ℕ, n+1 ≤ x → x ≤ n+3 → ∀ p : ℕ, p.Prime → p ∣ x → p ∈ S)
    (hS : S.card ≤ 3) {x y : ℕ} (h₁ : n+1≤x) (h₂ : x<y) (h₃ : y≤n+3)
    (hx : ¬smooth x) : smooth y := by
  have mem₂ : 2 ∈ S := by
    by_cases hd : 2 ∣ n+1
    · exact cover (n+1) (by omega) (by omega) 2 Nat.prime_two hd
    · exact cover (n+2) (by omega) (by omega) 2 Nat.prime_two (by omega)
  have mem₃ : 3 ∈ S := by
    by_cases hd : 3 ∣ n+1
    · exact cover (n+1) (by omega) (by omega) 3 Nat.prime_three hd
    by_cases he : 3 ∣ n+2
    · exact cover (n+2) (by omega) (by omega) 3 Nat.prime_three he
    · exact cover (n+3) (by omega) (by omega) 3 Nat.prime_three (by omega)
  unfold smooth at hx
  push Not at hx
  obtain ⟨p,hp,hpx,hp₂,hp₃⟩ := hx
  have pmem := cover x h₁ (by omega) p hp hpx
  intro q hq hqy
  by_contra! hn
  have qmem := cover y (by omega) h₃ q hq hqy
  have hpq : p=q := by
    by_contra hpq
    have sub : ({p,q,2,3} : Finset ℕ) ⊆ S := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> assumption
    have card : ({p,q,2,3} : Finset ℕ).card=4 := by simp [hpq,hp₂,hp₃,hn.1,hn.2]
    have := card_le_card sub
    omega
  subst q
  have hd := Nat.dvd_sub hqy hpx
  have hl := Nat.le_of_dvd (show 0<y-x by omega) hd
  have := hp.two_le
  omega

private lemma offset_bound {n k : ℕ} (hk : 3≤k)
    (hcard : (∏ i ∈ Icc 1 k, (n+i)).primeFactors.card ≤ 3) : n < 18 := by
  by_contra! hn
  let S := (∏ i ∈ Icc 1 k, (n+i)).primeFactors
  have cover (x : ℕ) (h₁ : n+1≤x) (h₂ : x≤n+3) (p : ℕ) (hp : p.Prime) (hd : p ∣ x) :
      p ∈ S := by
    apply Nat.mem_primeFactors.mpr
    refine ⟨hp,hd.trans ?_,?_⟩
    · have hmem : x-n ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
      simpa [show n+(x-n)=x by omega] using dvd_prod_of_mem (fun i => n+i) hmem
    · apply prod_ne_zero_iff.mpr
      intro i hi
      have := (mem_Icc.mp hi).1
      omega
  by_cases h₁ : smooth (n+1)
  · by_cases h₂ : smooth (n+2)
    · exact smooth_consecutive (by omega) h₁ h₂
    · exact smooth_two_apart (by omega) h₁
        (at_most_one_bad S cover hcard (by omega) (by omega) (by omega) h₂)
  · have h₂ : smooth (n+2) := at_most_one_bad S cover hcard (by omega) (by omega) (by omega) h₁
    have h₃ : smooth (n+3) := at_most_one_bad S cover hcard (by omega) (by omega) (by omega) h₁
    exact smooth_consecutive (by omega) h₂ h₃

private lemma length_bound {n k : ℕ} (hcard : (∏ i ∈ Icc 1 k, (n+i)).primeFactors.card ≤ 3) : k < 7 := by
  by_contra! hk
  let S := (∏ i ∈ Icc 1 k, (n+i)).primeFactors
  have mem {p : ℕ} (hp : p.Prime) (hle : p ≤ 7) : p ∈ S := by
    have hr := Nat.mod_lt n hp.pos
    have hi : p - n%p ∈ Icc 1 k := mem_Icc.mpr ⟨by omega,by omega⟩
    have hd : p ∣ n+(p-n%p) := by
      refine ⟨n/p+1,?_⟩
      rw [Nat.mul_succ]
      have := Nat.mod_add_div n p
      omega
    apply Nat.mem_primeFactors.mpr
    refine ⟨hp,hd.trans (dvd_prod_of_mem (fun i => n+i) hi),?_⟩
    apply prod_ne_zero_iff.mpr
    intro i hi
    have := (mem_Icc.mp hi).1
    omega
  have hsub : ({2,3,5,7} : Finset ℕ) ⊆ S := by
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> exact mem (by decide) (by decide)
  have hc := card_le_card hsub
  have hs : ({2,3,5,7} : Finset ℕ).card=4 := by decide
  change S.card ≤ 3 at hcard
  omega

-- Compute the union incrementally, so the finite check only factors small individual entries.
private def primes (n : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | k+1 => primes n k ∪ (n+k+1).primeFactors

private lemma primes_eq (n k : ℕ) : (∏ i ∈ Icc 1 k, (n+i)).primeFactors = primes n k := by
  induction k with
  | zero => simp [primes]
  | succ k ih =>
    rw [prod_Icc_succ_top (by omega : 1≤k+1),Nat.primeFactors_mul,ih]
    · simp [primes,Nat.add_assoc]
    · apply prod_ne_zero_iff.mpr
      intro i hi
      have := (mem_Icc.mp hi).1
      omega
    · omega

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
private lemma bounded :
    ∀ n₂ : Fin 18, (n₂ : ℕ) ≠ 7 →
    ∀ k₂ : Fin 7, 3 ≤ (k₂ : ℕ) → (primes n₂ k₂).card ≤ 3 →
    ∀ n₁ : Fin ((n₂ : ℕ)+1), ∀ k₁ : Fin ((n₂ : ℕ)-(n₁ : ℕ)+1), 3 ≤ (k₁ : ℕ) →
      primes n₁ k₁ ≠ primes n₂ k₂ := by decide +kernel

set_option maxRecDepth 2000 in
private lemma at_seven :
    ∀ n₁ k₁ k₂ : Fin 8, 3 ≤ (k₂ : ℕ) → 3 ≤ (k₁ : ℕ) → (n₁ : ℕ)+(k₁ : ℕ) ≤ 7 →
    ((primes n₁ k₁ = primes 7 k₂ ∧ (primes 7 k₂).card ≤ 3) ↔
      (k₂ : ℕ) = 3 ∧ ((n₁ : ℕ)+(k₁ : ℕ) = 5 ∨ (n₁ : ℕ)+(k₁ : ℕ) = 6)) := by decide +kernel

-- Erdős's original equation (10) does not order the lengths. The same list
-- of seven configurations works even with both lengths quantified independently.
theorem classification (k₁ k₂ n₁ n₂ : ℕ) (hk₁ : 3≤k₁) (hk₂ : 3≤k₂) (hsep : n₁+k₁≤n₂) :
    ((∏ i ∈ Icc 1 k₁, (n₁+i)).primeFactors = (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors ∧
      (∏ j ∈ Icc 1 k₂, (n₂+j)).primeFactors.card ≤ 3) ↔
        n₂=7 ∧ k₂=3 ∧ (n₁+k₁=5 ∨ n₁+k₁=6) := by
  constructor
  · rintro ⟨heq,hc⟩
    have bound := offset_bound hk₂ hc
    have kl := length_bound hc
    rw [primes_eq,primes_eq] at heq
    rw [primes_eq] at hc
    by_cases hb : n₂ = 7
    · subst n₂
      exact ⟨rfl,(at_seven ⟨n₁,by omega⟩ ⟨k₁,by omega⟩ ⟨k₂,by omega⟩ hk₂ hk₁ hsep).mp ⟨heq,hc⟩⟩
    · exact False.elim (bounded ⟨n₂,bound⟩ hb ⟨k₂,kl⟩ hk₂ hc
        ⟨n₁,by change n₁<n₂+1; omega⟩ ⟨k₁,by change k₁<n₂-n₁+1; omega⟩ hk₁ heq)
  · rintro ⟨rfl,rfl,hend⟩
    rw [primes_eq,primes_eq]
    exact (at_seven ⟨n₁,by omega⟩ ⟨k₁,by omega⟩ ⟨3,by decide⟩ (by decide) hk₁ hsep).mpr ⟨rfl,hend⟩

end SmallPrimeSupport

theorem OMA.solution : OMA.R_Erdos931_erdos_931_R1.H1 := by
  intro k₁ k₂ n₁ n₂ hk₂ hk₁ hsep
  exact SmallPrimeSupport.classification k₁ k₂ n₁ n₂ (hk₂.trans hk₁) hk₂ hsep
