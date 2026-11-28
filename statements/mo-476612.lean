import Mathlib

/-!
# Sums of capped upper bounds

Source: https://mathoverflow.net/questions/476612/a-surprisingly-simple-and-difficult-problem-on-sums-of-upper-bounds

Indices begin at zero, so the weight of entry k is 1/sqrt(k+1). The capped
threshold is the largest feasible level in [0,1]. This equals the smaller
of 1 and the solution of the question's positive-part cost equation.
-/
namespace OMA.S_mo_476612

noncomputable def cost (p : ℕ → ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (t+1), max (x-p k) 0 / Real.sqrt (k+1)

noncomputable def threshold (p : ℕ → ℝ) (C : ℝ) (t : ℕ) : ℝ :=
  sSup {x ∈ Set.Icc (0:ℝ) 1 | cost p t x ≤ C}

noncomputable def excess (p : ℕ → ℝ) (C : ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (threshold p C t-p t)

def UnitData (p : ℕ → ℝ) : Prop := ∀ t, p t ∈ Set.Icc (0:ℝ) 1

/-- For each fixed positive budget the proposed square-root-times-polylog
bound is uniform over the data at every sufficiently large horizon.
A nonnegative integer log exponent suffices for an arbitrary polylog.
The exponent, implicit constant and initial horizon may depend on C. -/
theorem main :
    ∀ C : ℝ, 0 < C → ∃ d : ℕ, ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
      ∀ T : ℕ, N ≤ T → ∀ p : ℕ → ℝ, UnitData p →
        excess p C T ≤ K*C*Real.sqrt T*(1+Real.log T)^d := by
  sorry

end OMA.S_mo_476612
