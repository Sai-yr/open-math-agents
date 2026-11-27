import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Sort

/-!
# Divisibility of the weighted sum under partition reversal

Source: OEIS A362559 and its complement A362560, Gus Wiseman (2023),
OEIS Foundation, CC BY-SA 4.0. The original parts are listed in descending
order. The first part has weight 1, the second weight 2, and so on.
https://oeis.org/A362559
-/

namespace OMA.S_oeis_a362559

def weightedFrom (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => i*x + weightedFrom (i+1) xs

theorem main : ∀ (n : ℕ) (p : Nat.Partition n),
    let parts := p.parts.sort (· ≥ ·)
    n ∣ weightedFrom 1 parts ↔ n ∣ weightedFrom 1 parts.reverse := by
  sorry

end OMA.S_oeis_a362559
