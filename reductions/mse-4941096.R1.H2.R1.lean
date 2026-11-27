import OMAReductions.R_mse_4941096_R1

/-!
# Long arcs in an example on the integer line

The first step forces a source of a long arc in every interval of a specified
length. The second step restricts the residual existence question to graphs
satisfying this condition for every global bandwidth bound.
-/
namespace OMA.R_mse_4941096_R1_H2_R1

open OMA.S_mse_4941096

def H1 : Prop := ∀ out : ℤ → Finset ℤ, exampleGraph out →
  (∀ x, 3 ≤ (out x).card) →
  ∀ W : ℕ, (∀ x y, y ∈ out x → x - (W : ℤ) ≤ y ∧ y ≤ x + W) →
  ∀ L : ℤ, ∃ x, L ≤ x ∧ x < L + 2 * (W : ℤ) + 56 ∧
    ∃ y ∈ out x, x + 4 ≤ y ∨ y + 4 ≤ x

def H2 : Prop := ∀ (out : ℤ → Finset ℤ) (v : ℤ),
  (∀ x, (out v).card ≤ (out x).card) → 3 ≤ (out v).card →
  (∀ u ∈ out v, ∃ w ∈ out v, w ∈ out u) →
  (∀ W : ℕ, (∀ x y, y ∈ out x → x - (W : ℤ) ≤ y ∧ y ≤ x + W) →
    ∀ L : ℤ, ∃ x, L ≤ x ∧ x < L + 2 * (W : ℤ) + 56 ∧
      ∃ y ∈ out x, x + 4 ≤ y ∨ y + 4 ≤ x) →
  ¬exampleGraph out

section Proof

theorem main : H1 → H2 → OMA.R_mse_4941096_R1.H2 := by
  intro longArcs residual out v minimum degree sinkFree graph
  exact residual out v minimum degree sinkFree
    (longArcs out graph (fun x => degree.trans (minimum x))) graph

end Proof

end OMA.R_mse_4941096_R1_H2_R1
