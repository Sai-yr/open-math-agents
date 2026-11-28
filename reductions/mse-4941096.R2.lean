import OMAStatements.S_mse_4941096

/-!
# Translations with two infinite vertex orbits

The first hypothesis rules out any example admitting a translation on two
integer tracks. The numbering of the tracks is arbitrary. In particular a
period-two example in the original ordering is covered, at every bandwidth.
The second hypothesis excludes a finite configuration on 2k vertices in
every example of minimum outdegree k. The third retains both restrictions.
-/
namespace OMA.R_mse_4941096_R2

open OMA.S_mse_4941096

def H1 : Prop := ∀ out : ℤ → Finset ℤ,
  (∃ (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → Finset ℤ),
    ∀ (i j : Bool) (n d : ℤ),
      f (j,n+d) ∈ insert (f (i,n)) (out (f (i,n))) ↔ d ∈ B i j) →
  ¬exampleGraph out

def H2 : Prop := ∀ out : ℤ → Finset ℤ, exampleGraph out →
  ∀ k : ℕ, 0<k → (∀ z, k≤(out z).card) →
    ¬∃ v : ℕ → ℤ, (∀ i < 2*k, ∀ j < 2*k, v i=v j → i=j) ∧
      (∀ i<k, ∀ z, z∈out (v i) ↔ ∃ j, i<j ∧ j≤ i+k ∧ v j=z)

def H3 : Prop := ∀ out : ℤ → Finset ℤ,
  (¬∃ (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → Finset ℤ),
    ∀ (i j : Bool) (n d : ℤ),
      f (j,n+d) ∈ insert (f (i,n)) (out (f (i,n))) ↔ d ∈ B i j) →
  (∀ k : ℕ, 0<k → (∀ z, k≤(out z).card) →
    ¬∃ v : ℕ → ℤ, (∀ i < 2*k, ∀ j < 2*k, v i=v j → i=j) ∧
      (∀ i<k, ∀ z, z∈out (v i) ↔ ∃ j, i<j ∧ j≤ i+k ∧ v j=z)) →
  ¬exampleGraph out

section Proof

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mse_4941096.main := by
  intro symmetric windows rest ⟨out,hg⟩
  by_cases h : ∃ (f : (Bool × ℤ) ≃ ℤ) (B : Bool → Bool → Finset ℤ),
      ∀ (i j : Bool) (n d : ℤ),
        f (j,n+d) ∈ insert (f (i,n)) (out (f (i,n))) ↔ d∈B i j
  · exact symmetric out h hg
  · exact rest out h (windows out hg) hg

end Proof
end OMA.R_mse_4941096_R2
