import OMAStatements.S_oeis_a290650
import Mathlib.Tactic

open OMA.S_oeis_a290650

private lemma positive_term (i : ℕ) : 0 < term i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [term]
    split
    · omega
    · positivity

/-- Starting anywhere, the successive halvings must eventually end. -/
private lemma odd_after (i : ℕ) : ∃ j ≥ i, term j % 2 ≠ 0 := by
  by_contra! h
  have descend (r : ℕ) : term (i+r)+r ≤ term i := by
    induction r with
    | zero => simp
    | succ r ih =>
      change term ((i+r)+1)+(r+1) ≤ term i
      rw [term, if_pos (h (i+r) (by omega))]
      have hp := positive_term (i+r)
      omega
  have := descend (term i+1)
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a290650.main := by
  intro B
  obtain ⟨j, hj, ho⟩ := odd_after B
  refine ⟨j+1, ?_⟩
  rw [term, if_neg ho]
  have hp := positive_term j
  have ht := Nat.mul_le_mul_right (j+2) hp
  omega
