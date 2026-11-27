import OMAStatements.S_mo_455020
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

open Finset OMA.S_mo_455020

namespace MirrorGcd

private lemma size {m i c : ℕ} (hm : 3 ≤ m) (hi : 1 ≤ i) (hc : c ≤ 2) :
    1 < entry m i c := by
  unfold entry
  have := Nat.mul_le_mul hm (show 2 ≤ i+1 by omega)
  omega

private lemma pair_sum {m n i c : ℕ} (hm : 3 ≤ m) (hi : i ∈ Icc 1 n) (hc : c ≤ 2) :
    entry m i c + entry m (n+1-i) c = target m n c := by
  obtain ⟨hil,hih⟩ := mem_Icc.mp hi
  let j := n+1-i
  have hji : i+j=n+1 := by dsimp [j]; omega
  have hj : 1 ≤ j := by omega
  have h1 := size hm hil hc
  have h2 := size hm hj hc
  have he : m*(i+1)+m*(j+1)=m*(n+3) := by nlinarith [congrArg (m*·) hji]
  change entry m i c + entry m j c = _
  unfold entry at *
  unfold target
  omega

private lemma test_iff {m n : ℕ} (hm : 3 ≤ m) :
    passes m n ↔ ∀ i ∈ Icc 1 n, ∀ c : ℕ, c = 1 ∨ c = 2 →
      (entry m i c).gcd (entry m (n+1-i) c) = 1 := by
  have local_iff (i : ℕ) (hi : i ∈ Icc 1 n) :
      finalEntry m n i = m*(i+1) ↔
      ∀ c : ℕ, c=1 ∨ c=2 → (entry m i c).gcd (entry m (n+1-i) c) = 1 := by
    obtain ⟨hil,hih⟩ := mem_Icc.mp hi
    let j := n+1-i
    let x := entry m i 2
    let y := entry m j 2
    let g := x.gcd y
    have hx : 1 < x := size hm hil (by decide)
    have hy : 1 < y := size hm (by dsimp [j]; omega) (by decide)
    have hix : entry m i 1 = x+1 := by dsimp [x,entry] at *; omega
    have hiy : entry m j 1 = y+1 := by dsimp [y,entry] at *; omega
    have hij : m*(i+1) = x+2 := by dsimp [x,entry] at *; omega
    have hg : 0 < g := Nat.gcd_pos_of_pos_left y (by omega)
    have hh : 0 < (x+g).gcd (y+g) := Nat.gcd_pos_of_pos_left _ (by omega)
    change (if i=j then x+2*g else x+g+(x+g).gcd (y+g)) = _ ↔ _
    rw [hij]
    constructor
    · intro h c hc
      by_cases heq : i=j
      · have hxy : x=y := by dsimp [x,y]; rw [heq]
        have hgx : g=x := by simp [g,hxy]
        rw [if_pos heq] at h
        omega
      · rw [if_neg heq] at h
        have hgone : g=1 := by omega
        have hhone : (x+1).gcd (y+1) = 1 := by rw [hgone] at h hh; omega
        rcases hc with rfl | rfl
        · change (entry m i 1).gcd (entry m j 1) = 1
          rw [hix,hiy]
          exact hhone
        · exact hgone
    · intro h
      have hg1 : g=1 := h 2 (Or.inr rfl)
      have hh1 := h 1 (Or.inl rfl)
      change (entry m i 1).gcd (entry m j 1) = 1 at hh1
      rw [hix,hiy] at hh1
      rw [hg1,hh1]
      split <;> omega
  exact ⟨fun h i hi => (local_iff i hi).mp (h i hi),
    fun h i hi => (local_iff i hi).mpr (h i hi)⟩

private lemma twin_passes {m n : ℕ} (hm : 3 ≤ m) (hp : twins m n) : passes m n := by
  apply (test_iff hm).mpr
  intro i hi c hc
  have hprime : (target m n c).Prime := by rcases hc with rfl | rfl; exact hp.2; exact hp.1
  have hbound : c ≤ 2 := by omega
  let x := entry m i c
  let y := entry m (n+1-i) c
  have hsum : x+y=target m n c := pair_sum hm hi hbound
  have hx : 0<x := by have := size hm (mem_Icc.mp hi).1 hbound; omega
  have hy : 0<y := by
    have := size hm (show 1 ≤ n+1-i by have := (mem_Icc.mp hi).2; omega) hbound
    omega
  have hd : x.gcd y ∣ target m n c := hsum ▸ Nat.dvd_add (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..)
  rcases (Nat.dvd_prime hprime).mp hd with h | h
  · exact h
  · have := Nat.le_of_dvd hx (Nat.gcd_dvd_left x y)
    omega

private lemma hits_factor {m n c p : ℕ} (hm : 3 ≤ m) (hc : c≤2) (hp : p.Prime)
    (hpn : p ≤ n) (hpm : ¬p ∣ m) : ∃ i ∈ Icc 1 n, p ∣ entry m i c := by
  let : Fact p.Prime := ⟨hp⟩
  have hunit : (m : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp hpm
  let r : ZMod p := (c : ZMod p)/m-2
  let i := r.val+1
  have hi : i ∈ Icc 1 n := by
    apply mem_Icc.mpr
    dsimp [i]
    have := r.val_lt
    omega
  refine ⟨i,hi,(ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
  have hbound : c ≤ m*(i+1) := by nlinarith
  rw [entry, Nat.cast_sub hbound, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  change (m : ZMod p)*((↑(r.val+1) : ZMod p)+1)-c = 0
  rw [Nat.cast_add,Nat.cast_one,ZMod.natCast_zmod_val]
  dsimp [r]
  field_simp
  ring

private lemma exact_test (m n : ℕ) (hm : 3 ≤ m) (odd : Odd m) (hn : m+3 ≤ n)
    (hpass : passes m n) (c : ℕ) (hc : c=1 ∨ c=2) : (target m n c).Prime := by
  have hc2 : c≤2 := by omega
  have hraw : 6 < m*(n+3) := by nlinarith
  have hN : 1 < target m n c := by unfold target; omega
  by_contra composite
  let p := (target m n c).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ target m n c := Nat.minFac_dvd _
  have hpsq : p^2 ≤ target m n c := Nat.minFac_sq_le_self (by omega) composite
  have hpn : p ≤ n := by
    have hh := Nat.mul_le_mul_right (n+3) hn
    have hle : target m n c ≤ m*(n+3) := Nat.sub_le .. 
    nlinarith
  have hr : target m n c + 2*c = m*(n+3) := by unfold target; omega
  have hpm : ¬p ∣ m := by
    intro hdvd
    have h2c := (Nat.dvd_add_iff_right hd).mpr (hr ▸ dvd_mul_of_dvd_left hdvd (n+3))
    have h4 : p ∣ 2^2 := h2c.trans (by rcases hc with rfl | rfl <;> decide)
    have h2 : p=2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)
    exact odd.not_two_dvd_nat (h2 ▸ hdvd)
  obtain ⟨i,hi,hiDiv⟩ := hits_factor hm hc2 hp hpn hpm
  have he := pair_sum hm hi hc2
  have hjDiv := (Nat.dvd_add_iff_right hiDiv).mpr (he ▸ hd)
  have hgcd := (test_iff hm).mp hpass i hi c hc
  exact hp.not_dvd_one (hgcd ▸ Nat.dvd_gcd hiDiv hjDiv)

end MirrorGcd

theorem OMA.solution : type_of% @OMA.S_mo_455020.main := by
  intro m hm hodd
  refine ⟨fun n _ h => MirrorGcd.twin_passes hm h, m+3,?_⟩
  intro n hn
  exact ⟨fun h => ⟨MirrorGcd.exact_test m n hm hodd hn h 2 (Or.inr rfl),
    MirrorGcd.exact_test m n hm hodd hn h 1 (Or.inl rfl)⟩,
    MirrorGcd.twin_passes hm⟩
