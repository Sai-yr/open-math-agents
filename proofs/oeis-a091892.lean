import OMAStatements.S_oeis_a091892

/-!
# Two equal-weight partitions of 331775

The binary expansion of 331776 starts with 10, and has twelve trailing
zeros and four other zeros. It reaches the proposed threshold exactly.
The singleton and the nine-part partition below both have only parts of
binary weight fourteen.
-/
namespace A091892Proof
open OMA.S_oeis_a091892

private def blocks : List ℕ :=
  [30719,31743,32255,32511,32639,32703,32735,49135,57335]

private def nine : Nat.Partition 331775 where
  parts := (blocks : Multiset ℕ)
  parts_pos := by
    intro j hj
    have h : ∀ j ∈ blocks, 0 < j := by decide +kernel
    exact h j hj
  parts_sum := by decide +kernel

private def one : Nat.Partition 331775 where
  parts := {331775}
  parts_pos := by simp
  parts_sum := by simp

private theorem admissible_nine : ∀ j ∈ nine.parts, weight j = weight 331775 := by
  change ∀ j ∈ blocks, weight j = weight 331775
  decide +kernel

private theorem admissible_one : ∀ j ∈ one.parts, weight j = weight 331775 := by
  simp [one]

private theorem unique_fails : ¬ member 331775 := by
  rintro ⟨p,_,hp⟩
  have h : nine = one := (hp _ admissible_nine).trans (hp _ admissible_one).symm
  have size := congrArg (fun p : Nat.Partition 331775 => p.parts.card) h
  have hn : nine.parts.card=9 := by decide +kernel
  have ho : one.parts.card=1 := by decide +kernel
  change nine.parts.card=one.parts.card at size
  omega

private theorem passes : threshold 331775 := by
  unfold threshold
  decide +kernel

end A091892Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091892.main) := by
  intro h
  exact A091892Proof.unique_fails ((h.2 331775 (by decide)).mpr A091892Proof.passes)

