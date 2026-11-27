import OMAStatements.S_oeis_a362559
import Mathlib.Tactic

open OMA.S_oeis_a362559

namespace PartitionWeights

private lemma shift (l : List ℕ) (i : ℕ) :
    weightedFrom (i+1) l = weightedFrom i l + l.sum := by
  induction l generalizing i with
  | nil => simp [weightedFrom]
  | cons x xs ih =>
    simp only [weightedFrom, List.sum_cons]
    rw [ih (i+1)]
    ring

private lemma append_last (l : List ℕ) (i x : ℕ) :
    weightedFrom i (l ++ [x]) = weightedFrom i l + (i+l.length)*x := by
  induction l generalizing i with
  | nil => simp [weightedFrom]
  | cons y ys ih =>
    simp only [List.cons_append,weightedFrom,List.length_cons]
    rw [ih]
    ring

private lemma reversal (l : List ℕ) :
    weightedFrom 1 l + weightedFrom 1 l.reverse = (l.length+1)*l.sum := by
  induction l with
  | nil => simp [weightedFrom]
  | cons x xs ih =>
    simp only [weightedFrom,List.reverse_cons,append_last,List.length_reverse,List.length_cons,List.sum_cons]
    rw [shift xs 1]
    nlinarith only [ih]

end PartitionWeights

theorem OMA.solution : type_of% @OMA.S_oeis_a362559.main := by
  intro n p
  let l := p.parts.sort (· ≥ ·)
  change n ∣ weightedFrom 1 l ↔ n ∣ weightedFrom 1 l.reverse
  have hs : l.sum = n := by
    change (l : Multiset ℕ).sum = n
    simp [l,p.parts_sum]
  have ht : n ∣ weightedFrom 1 l + weightedFrom 1 l.reverse := by
    rw [PartitionWeights.reversal,hs]
    exact dvd_mul_left _ _
  exact ⟨fun h => (Nat.dvd_add_iff_right h).mpr ht, fun h => (Nat.dvd_add_iff_left h).mpr ht⟩
