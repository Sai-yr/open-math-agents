import OMAStatements.S_mo_509919

/-!
The primes used here occur in the actual initial segment of divisors.
A uniform upper bound on the second-largest such prime is the residual
arithmetic problem. H1 converts any such bound to a polynomial upper
bound on the original integer, with the rank k held fixed.
-/
namespace OMA.R_mo_509919_R1

open OMA.S_mo_509919

def H1 : Prop := ∀ k n B : ℕ, (k ≤ n.divisors.card ∧ n = sumSqSmallestDivisors k n) → 2 ≤ B →
  k * (k * B^(2*(k-1)))^(2*(k-1)) < n →
  ∃ p ∈ ((n.divisors.sort (· ≤ ·)).take k), ∃ q ∈ ((n.divisors.sort (· ≤ ·)).take k),
    p.Prime ∧ q.Prime ∧ B < p ∧ B < q ∧ p ≠ q

def H2 : Prop := ∀ k : ℕ, ∃ B : ℕ, 2 ≤ B ∧ ∀ n : ℕ,
  (k ≤ n.divisors.card ∧ n = sumSqSmallestDivisors k n) →
  ¬ (∃ p ∈ ((n.divisors.sort (· ≤ ·)).take k), ∃ q ∈ ((n.divisors.sort (· ≤ ·)).take k),
    p.Prime ∧ q.Prime ∧ B < p ∧ B < q ∧ p ≠ q)

section Proof

theorem main : H1 → H2 → type_of% @OMA.S_mo_509919.main := by
  intro gap cutoff k
  obtain ⟨B,hB,limited⟩ := cutoff k
  apply (Set.finite_Iic (k * (k * B^(2*(k-1)))^(2*(k-1)))).subset
  intro n hn
  exact le_of_not_gt (fun h => limited n hn (gap k n B hn hB h))

end Proof

end OMA.R_mo_509919_R1
