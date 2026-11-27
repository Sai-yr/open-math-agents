import OMAStatements.S_oeis_a340896
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

open OMA.S_oeis_a340896

namespace DivisorCountTriangle

/-- Doubling every exponent more than doubles the divisor count once two
positive exponents are present. The other factors can only increase. -/
private lemma two_factor_bound (s : Finset ℕ) (a : ℕ → ℕ) (hs : s.Nontrivial)
    (ha : ∀ i ∈ s, 0 < a i) :
    2 * (∏ i ∈ s, (a i + 1)) ≤ ∏ i ∈ s, (2 * a i + 1) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := hs
  have hq' : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have pair : 2 * ((a p + 1) * (a q + 1)) ≤ (2 * a p + 1) * (2 * a q + 1) := by
    nlinarith [Nat.mul_pos (ha p hp) (ha q hq)]
  have rest : (∏ i ∈ (s.erase p).erase q, (a i + 1)) ≤
      ∏ i ∈ (s.erase p).erase q, (2 * a i + 1) :=
    Finset.prod_le_prod' fun i _ => by omega
  rw [← s.mul_prod_erase (fun i => a i + 1) hp,
      ← (s.erase p).mul_prod_erase (fun i => a i + 1) hq',
      ← s.mul_prod_erase (fun i => 2 * a i + 1) hp,
      ← (s.erase p).mul_prod_erase (fun i => 2 * a i + 1) hq']
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul pair rest

private lemma square_bound {n : ℕ} (hn : 0 < n) (h : n.primeFactors.Nontrivial) :
    2 * n.divisors.card ≤ (n ^ 2).divisors.card := by
  rw [Nat.card_divisors hn.ne', Nat.card_divisors (pow_ne_zero 2 hn.ne'),
    Nat.primeFactors_pow n (by decide : 2 ≠ 0), Nat.factorization_pow]
  simpa only [Finsupp.smul_apply, smul_eq_mul] using
    two_factor_bound n.primeFactors n.factorization h fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn.ne'
        (Nat.dvd_of_mem_primeFactors hp)

private lemma prime_pow_in_row {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p ^ e) ^ 2 ∈ row (p ^ e) := by
  refine ⟨pow_pos (pow_pos hp.pos e) 2, dvd_pow_self _ (by decide), ?_⟩
  rw [← pow_mul, ← ArithmeticFunction.sigma_zero_apply, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  omega

end DivisorCountTriangle

open DivisorCountTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a340896.main := by
  intro n hn
  constructor
  · intro h
    by_cases h1 : n = 1
    · exact ⟨2, 0, Nat.prime_two, by simpa using h1⟩
    by_contra hno
    have hnp : ¬ IsPrimePow n := by
      intro hpp
      obtain ⟨p, e, hp, _, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      exact hno ⟨p, e, hp, rfl⟩
    have htwo := (Nat.not_isPrimePow_iff_nontrivial_of_two_le (by omega : 2 ≤ n)).mp hnp
    exact (Nat.not_lt_of_ge (square_bound hn htwo)) h.2.2
  · rintro ⟨p, e, hp, rfl⟩
    exact prime_pow_in_row hp e
