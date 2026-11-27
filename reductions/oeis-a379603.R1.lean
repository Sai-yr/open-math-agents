import OMAStatements.S_oeis_a379603

/-! The first step solves the even case and gives witnesses in both parities.
The remaining step excludes larger candidates of odd length. -/
namespace OMA.R_oeis_a379603_R1
open OMA.S_oeis_a379603

def H1 : Prop := ∀ n : ℕ, 5≤n →
  largest (2*n) (evenValue n) ∧ eligible (2*n+1) (10*evenValue n+6)

def H2 : Prop := ∀ n : ℕ, 5≤n → ∀ y, eligible (2*n+1) y → y ≤ 10*evenValue n+6

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a379603.main := by
  intro he ho n hn
  exact ⟨(he n hn).1,(he n hn).2,ho n hn⟩

end OMA.R_oeis_a379603_R1
