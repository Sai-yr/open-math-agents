import Mathlib

/-!
# Conditional averages of a permutation score in Euclidean space

Source: Penelope Benenati, MathOverflow 365609, July 14, 2020, CC BY-SA 4.0.
https://mathoverflow.net/questions/365609/distance-properties-of-the-permutations-of-a-set-of-points-in-a-euclidean-space

A permutation maps a point's index to its position. The score sums the
weight of the first pair in each increasing triple of positions. The mean
gives equal weight to all permutations satisfying the indicated comparison.
-/

namespace OMA.S_mo_365609
open Finset

def tripleScore {n : ℕ} {K : Type*} [AddCommMonoid K]
    (w : Fin n → Fin n → K) (p : Equiv.Perm (Fin n)) : K :=
  ∑ i, ∑ j, ∑ k, if p i < p j ∧ p j < p k then w i j else 0

noncomputable def score {d n : ℕ} (points : Fin n → EuclideanSpace ℝ (Fin d))
    (p : Equiv.Perm (Fin n)) : ℝ :=
  tripleScore (fun i j => 1 - dist (points i) (points j)) p

def preceding {n : ℕ} (i j : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter fun p => p i < p j

def meanBefore {n : ℕ} {K : Type*} [Field K] (value : Equiv.Perm (Fin n) → K)
    (i j : Fin n) : K :=
  (∑ p ∈ preceding i j, value p) / ((preceding i j).card : K)

theorem main : ∀ (d n : ℕ) (points : Fin n → EuclideanSpace ℝ (Fin d)),
    Function.Injective points → (∀ i j, dist (points i) (points j) ≤ 1) →
    (∃ i j, dist (points i) (points j) = 1) →
    ∀ p : Equiv.Perm (Fin n), (∀ q, score points q ≤ score points p) →
    ∀ i j, p i < p j → meanBefore (score points) j i ≤ meanBefore (score points) i j := by
  sorry

end OMA.S_mo_365609
