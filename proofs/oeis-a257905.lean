import OMAStatements.S_oeis_a257905

open OMA.S_oeis_a257905

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a257905.main) := by
  intro conjecture
  have same : (orbit 0 5 5).a = (orbit 0 5 7).a := by decide
  have indices : (5 : ℕ) = 7 := (conjecture 0 5).1.1 same
  exact (by decide : (5 : ℕ) ≠ 7) indices
