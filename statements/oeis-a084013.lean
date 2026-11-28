import Mathlib

/-!
# Existence of decimal palindromic multiples of prescribed length

OEIS A084013 is the least n-digit palindromic multiple of n, with a
zero entry if there is no witness. A084015 asks for the greatest such
multiple and has exactly the same zero-entry conjecture. For n divisible
by ten the source allows the zeros that become leading zeros after
reversal to be ignored.
-/
namespace OMA.S_oeis_a084013

def qualifies (n x : ℕ) : Prop :=
  0 < x ∧ n ∣ x ∧ (Nat.digits 10 x).length = n ∧
    (if 10 ∣ n then
      let core := (Nat.digits 10 x).dropWhile (· == 0)
      core.reverse = core
    else (Nat.digits 10 x).reverse = Nat.digits 10 x)

noncomputable def a (n : ℕ) : ℕ := open Classical in
  if h : ∃ x : ℕ, qualifies n x then Nat.find h else 0

theorem main : ∀ n : ℕ, 0 < n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a084013
