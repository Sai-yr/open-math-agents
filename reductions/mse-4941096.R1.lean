import OMAStatements.S_mse_4941096

/-!
The first step forces a local configuration at minimum outdegree. Every
out-neighbor of a particular minimum-degree vertex must have an arc to
another member of that same neighborhood, which has at least three members.
The residual case is whether an example with this configuration is possible.
-/
namespace OMA.R_mse_4941096_R1

open OMA.S_mse_4941096

def H1 : Prop := ∀ out : ℤ → Finset ℤ, exampleGraph out → ∃ v,
  (∀ x, (out v).card ≤ (out x).card) ∧ 3 ≤ (out v).card ∧
  ∀ u ∈ out v, ∃ w ∈ out v, w ∈ out u

def H2 : Prop := ∀ (out : ℤ → Finset ℤ) (v : ℤ),
  (∀ x, (out v).card ≤ (out x).card) → 3 ≤ (out v).card →
  (∀ u ∈ out v, ∃ w ∈ out v, w ∈ out u) → ¬exampleGraph out

section Proof

theorem main : H1 → H2 → type_of% @OMA.S_mse_4941096.main := by
  intro obstruction residual ⟨out, hg⟩
  obtain ⟨v, hmin, hcard, hcycle⟩ := obstruction out hg
  exact residual out v hmin hcard hcycle hg

end Proof

end OMA.R_mse_4941096_R1
