import OMAStatements.S_oeis_a331021
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Tactic

namespace WieferichFactors

private lemma exponent_reduction {k p : ℕ} (hk : 1 < k) (hp : p.Prime)
    (hpk : p ∣ k) (hsq : p^2 ∣ 2^(k-1)-1) : p^2 ∣ 2^(p-1)-1 := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have htwo : 2 ∣ 2^(k-1)-1 := (by decide : 2 ∣ 2^2).trans hsq
    rw [show k-1=(k-2)+1 by omega, pow_succ] at htwo
    have hpos : 0 < 2^(k-2) := by positivity
    omega
  have hcop : Nat.Coprime 2 (p^2) := ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_right 2
  have heuler := Nat.pow_totient_mod_eq_one (by have := hp.two_le; nlinarith : 1 < p^2) hcop
  rw [Nat.totient_prime_pow_succ hp 1, pow_one] at heuler
  have he : 1 ≡ 2^(p*(p-1)) [MOD p^2] := by
    change 1 % p^2 = _
    rw [Nat.mod_eq_of_lt (by have := hp.two_le; nlinarith : 1 < p^2)]
    exact heuler.symm
  have hE : p^2 ∣ 2^(p*(p-1))-1 := he.dvd'
  let d := Nat.gcd (k-1) (p*(p-1))
  have hpow := Nat.dvd_gcd hsq hE
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at hpow
  have hnot : ¬ p ∣ k-1 := by
    intro hd
    have hh := Nat.dvd_sub hpk hd
    rw [show k-(k-1)=1 by omega] at hh
    exact hp.not_dvd_one hh
  have hc : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hnot).symm.coprime_dvd_left (Nat.gcd_dvd_left _ _)
  have hd : d ∣ p-1 := hc.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)
  have hh := Nat.gcd_dvd_right (2^d-1) (2^(p-1)-1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_eq_left hd] at hh
  exact hpow.trans hh

end WieferichFactors

theorem OMA.solution : type_of% @OMA.S_oeis_a331021.main := by
  intro k hk hlarge
  have hk1 : 1 < k := by
    by_contra! h
    have : k=1 := by omega
    simp [this] at hlarge
  let g := Nat.gcd (k^2) (2^(k-1)-1)
  change k < g at hlarge
  obtain ⟨p,hv⟩ := Nat.exists_factorization_lt_of_lt hk.ne' hlarge
  have hvg : 0 < g.factorization p := by omega
  have hp : p.Prime := by
    by_contra hn
    rw [Nat.factorization_eq_zero_of_not_prime g hn] at hvg
    omega
  have hpg := Nat.dvd_of_factorization_pos hvg.ne'
  have hpk := hp.dvd_of_dvd_pow (hpg.trans (Nat.gcd_dvd_left (k^2) (2^(k-1)-1)))
  have hvk := hp.factorization_pos_of_dvd hk.ne' hpk
  have hsq : p^2 ∣ g := (hp.pow_dvd_iff_le_factorization (hk.trans hlarge).ne').mpr (by omega)
  exact ⟨p,hp,hpk,WieferichFactors.exponent_reduction hk1 hp hpk (hsq.trans (Nat.gcd_dvd_right _ _))⟩
