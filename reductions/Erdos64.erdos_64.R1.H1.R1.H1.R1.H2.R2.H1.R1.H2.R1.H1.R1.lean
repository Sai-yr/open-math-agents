import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1

/-!
# Hexagonal patches in abelian matching covers

Two vertex-disjoint hexagons with nonzero voltages and a handle of length two
force a simple cycle of length 16 or 32. An elementary packing argument on the
finite base then forces its order to be divisible by three in every potential
counterexample with an embedded coordinate patch. No finiteness assumption is
needed on the abelian voltage group.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H1_R1
open SimpleGraph

def H1 : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Finite B] (a b : B),
    a ≠ 0 → b ≠ 0 → a ≠ b →
    Function.Injective (fun i : Fin 8 × Fin 4 => i.1.val • a + i.2.val • b) →
    ¬ 3 ∣ Nat.card B →
    ∀ (V : Type) [AddCommGroup V] (w : B → Fin 3 → V),
    let G := SimpleGraph.fromRel fun l r : Bool × B × V =>
      ∃ (i : B) (k : Fin 3) (g : V),
        l = (false,i,g) ∧ r = (true,i + (![0,a,b] : Fin 3 → B) k,g + w i k)
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

def H2 : Prop :=
  ∀ (B : Type) [AddCommGroup B] [Finite B] (a b : B),
    a ≠ 0 → b ≠ 0 → a ≠ b → AddSubgroup.closure ({a,b} : Set B) = ⊤ →
    (3 ∣ Nat.card B ∨ ¬ Function.Injective (fun i : Fin 8 × Fin 4 => i.1.val • a + i.2.val • b)) →
    ∀ (V : Type) [AddCommGroup V] (w : B → Fin 3 → V),
    let G := SimpleGraph.fromRel fun l r : Bool × B × V =>
      ∃ (i : B) (k : Fin 3) (g : V),
        l = (false,i,g) ∧ r = (true,i + (![0,a,b] : Fin 3 → B) k,g + w i k)
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

section Proof

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1.H1 := by
  intro honeycomb residual B _ _ a b ha hb hab gen
  by_cases rect : Function.Injective (fun i : Fin 8 × Fin 4 => i.1.val • a + i.2.val • b)
  · by_cases three : 3 ∣ Nat.card B
    · exact residual B a b ha hb hab gen (Or.inl three)
    · exact honeycomb B a b ha hb hab rect three
  · exact residual B a b ha hb hab gen (Or.inr rect)

end Proof
end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H1_R1
