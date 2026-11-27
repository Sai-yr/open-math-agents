import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1

/-! Constrain the factorization of (p+11)/4 on the remaining classes. -/
namespace OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1

/-- A nonsquare prime divisor modulo eleven forces a three-term expansion
unless the complete multiset of non-1 residues is one of three exceptions. -/
def H1 : Prop := ∀ p : ℕ, 11 < p → p%12 = 1 → p%11 ≠ 0 →
  let r := ((((p+11)/4).primeFactorsList.map (fun (q : ℕ) => (q : ZMod 11))).filter (· != 1))
  (∃ a ∈ r, a ∈ ([2,6,7,8,10] : List (ZMod 11))) → ¬(r.Perm [2,3] ∨ r.Perm [3,6] ∨ r.Perm [2,3,6]) → ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

/-- On the remaining primes, either all factors are squares modulo eleven,
or the non-1 residues form one of the exceptional multisets. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p%24 = 1 →
    (p%840 = 1 ∨ p%840 = 121 ∨ p%840 = 169 ∨ p%840 = 289 ∨ p%840 = 361 ∨ p%840 = 529) →
    (p%11 = 1 ∨ p%11 = 2 ∨ p%11 = 3 ∨ p%11 = 4 ∨ p%11 = 5 ∨ p%11 = 6 ∨ p%11 = 9) →
    let r := ((((p+11)/4).primeFactorsList.map (fun (q : ℕ) => (q : ZMod 11))).filter (· != 1))
    ((∃ a ∈ r, a ∈ ([2,6,7,8,10] : List (ZMod 11))) → (r.Perm [2,3] ∨ r.Perm [3,6] ∨ r.Perm [2,3,6])) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4/p : ℚ) = 1/x+1/y+1/z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1.H1 := by
  intro cover remaining p hp h24 h840 h11
  let r := ((((p+11)/4).primeFactorsList.map (fun (q : ℕ) => (q : ZMod 11))).filter (· != 1))
  have big : 11 < p := by have := hp.two_le; omega
  by_cases casesLeft : (∃ a ∈ r, a ∈ ([2,6,7,8,10] : List (ZMod 11))) → (r.Perm [2,3] ∨ r.Perm [3,6] ∨ r.Perm [2,3,6])
  · exact remaining p hp h24 h840 h11 casesLeft
  · apply cover p big (by omega) (by omega)
    · by_contra h
      exact casesLeft (fun a => False.elim (h a))
    · intro h
      exact casesLeft (fun _ => h)

end OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1
