import OMAReductions.R_UnionClosed_union_closed_R1_H3_R1

/-!
# Four-element members in a possible Frankl counterexample

A four-element member with all four frequencies below one half must admit
a disjoint nonempty witness, or two such witnesses in an even family.
In the trace family above a witness, singletons outnumber triples. The
previous three-element restriction is retained in the residual statement.
-/
namespace OMA.R_UnionClosed_union_closed_R1_H3_R1_H2_R1

open Finset

def H1 : Prop := ∀ (m : ℕ) (A : Finset (Finset (Fin m))) (e : Fin 4 ↪ Fin m),
  UnionClosed.IsUnionClosed A → (univ : Finset (Fin 4)).map e ∈ A →
  (∀ X ∈ A, X.card ≠ 1) →
  (∀ i, 2 * (A.filter (fun X => e i ∈ X)).card < A.card) →
  let S := (univ : Finset (Fin 4)).map e
  let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 4)).filter (fun i => e i ∈ X)
  let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
  let bad := A.filter fun B =>
    let F := patterns B
    B.Nonempty ∧ Disjoint B S ∧ ∅ ∈ F ∧
      (F.filter (fun R => R.card = 3)).card <
        ((univ : Finset (Fin 4)).filter (fun i => {i} ∈ F)).card
  (if A.card % 2 = 0 then 2 else 1) ≤ bad.card

def H2 : Prop := ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
  UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2) →
  (∃ X ∈ A, X ≠ ∅) →
  (∀ e : Fin 3 ↪ Fin m, (univ : Finset (Fin 3)).map e ∈ A →
    let S := (univ : Finset (Fin 3)).map e
    let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 3)).filter (fun i => e i ∈ X)
    let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
    let bad := A.filter fun B => Disjoint B S ∧ ∃ T ∈ (univ : Finset (Finset (Fin 3))),
      T.Nonempty ∧ T ≠ univ ∧ patterns B = insert univ T.powerset
    (if A.card % 2 = 0 then 6 else 3) ≤ bad.card) →
  (∀ e : Fin 4 ↪ Fin m, (univ : Finset (Fin 4)).map e ∈ A →
    let S := (univ : Finset (Fin 4)).map e
    let tr := fun X : Finset (Fin m) => (univ : Finset (Fin 4)).filter (fun i => e i ∈ X)
    let patterns := fun B : Finset (Fin m) => (A.filter (fun X => X \ S = B)).image tr
    let bad := A.filter fun B =>
      let F := patterns B
      B.Nonempty ∧ Disjoint B S ∧ ∅ ∈ F ∧
        (F.filter (fun R => R.card = 3)).card <
          ((univ : Finset (Fin 4)).filter (fun i => {i} ∈ F)).card
    (if A.card % 2 = 0 then 2 else 1) ≤ bad.card) →
  ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

section Proof

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_R1_H3_R1.H2 := by
  intro obstruction residual m A hn hu hs he triples
  by_contra h
  apply h
  apply residual m A hn hu hs he triples
  intro e hm
  apply obstruction m A e hu hm (fun X hX => (hs X hX).1)
  intro i
  have r : ((A.filter (fun X => e i ∈ X)).card : ℚ) < (1 / 2 : ℚ) * A.card :=
    lt_of_not_ge fun hi => h ⟨e i,hi⟩
  have r' : (2 : ℚ) * (A.filter (fun X => e i ∈ X)).card < A.card := by linarith
  exact_mod_cast r'

end Proof

end OMA.R_UnionClosed_union_closed_R1_H3_R1_H2_R1
