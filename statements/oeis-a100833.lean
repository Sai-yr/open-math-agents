import Mathlib

/-!
# The least palindrome-free and squarefree sequence

OEIS A100833 uses one-based positions. Each new entry is the least
positive integer that leaves the prefix free from all palindromic
factors of length at least two and all adjacent repeated blocks.
Robert Israel conjectured the explicit expression below for all terms.
-/
namespace OMA.S_oeis_a100833

def admissible (a : ℕ → ℕ) (N : ℕ) : Prop :=
  (∀ i L : ℕ, 1 ≤ i → 2 ≤ L → i+L ≤ N+1 →
    ¬ ∀ j < L, a (i+j) = a (i+(L-1-j))) ∧
  (∀ i h : ℕ, 1 ≤ i → 0 < h → i+2*h ≤ N+1 →
    ¬ ∀ j < h, a (i+j) = a (i+h+j))

def greedy (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n →
    0 < a n ∧ admissible a n ∧
    ∀ c : ℕ, 0 < c → c < a n → ¬ admissible (Function.update a n c) n

def formula (n : ℕ) : ℕ :=
  if n%3 = 1 then 1 else if n%3 = 2 then 2 else 3 + (n/3).factorization 2

theorem main : greedy formula ∧ ∀ a : ℕ → ℕ, greedy a →
    ∀ n : ℕ, 0 < n → a n = formula n := by
  sorry

end OMA.S_oeis_a100833
