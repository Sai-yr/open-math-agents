import OMAStatements.S_mo_481671

/-!
A counterexample on the 32 objects A(i,j), B(i,j), with i and j modulo 4.
The certificate below verifies the ranks in sixteen explicit ballots. The
argument against every pair of possible ballots uses two directed 4-cycles.
-/

namespace MajorityCounterexample
open OMA.S_mo_481671

private def a (i j : Fin 4) : Fin 32 := ⟨8 * i.val + 2 * j.val, by omega⟩
private def b (i j : Fin 4) : Fin 32 := ⟨8 * i.val + 2 * j.val + 1, by omega⟩

/-- Ballot h omits row h/4 and column h%4. Their seven A's come first and
their seven B's last. All other cells appear in cyclic lexicographic order,
B immediately before A. Rows and columns start immediately after the omission. -/
private def rank (h : Fin 16) (x : Fin 32) : Fin 32 :=
  let i := (x.val / 8 + 4 - h.val / 4) % 4
  let j := (x.val / 2 % 4 + 4 - h.val % 4) % 4
  let tag := x.val % 2
  if i = 0 ∨ j = 0 then
    Fin.ofNat 32 ((if i = 0 then j else i + 3) + 25 * tag)
  else
    Fin.ofNat 32 (7 + 2 * ((i - 1) * 3 + (j - 1)) + (1 - tag))

set_option maxRecDepth 12000 in
private theorem distinctRanks : ∀ (h : Fin 16) (x y : Fin 32),
    rank h x = rank h y → x = y := by decide +kernel

private noncomputable def ballot (h : Fin 16) : Equiv.Perm (Fin 32) :=
  Equiv.ofBijective (rank h) (Finite.injective_iff_bijective.mp fun _ _ => distinctRanks h _ _)

private noncomputable def profile := (List.finRange 16).map ballot

set_option maxRecDepth 12000 in
/-- In all sixteen ballots A(i,j) precedes both B(i,j+1) and
every B(i+1,k). In nine ballots B(i,j) precedes A(i,j). -/
private theorem counts :
    (∀ i j : Fin 4, multiplicity profile (a i j) (b i (j + 1)) = 2) ∧
    (∀ i j k : Fin 4, multiplicity profile (a i j) (b (i + 1) k) = 2) ∧
    (∀ i j : Fin 4,
        profile.countP (fun p => decide (p (b i j) < p (a i j))) = 9 ∧
        multiplicity profile (b i j) (a i j) = 1) := by decide +kernel

private lemma pairBoth {n : ℕ} (p q : Equiv.Perm (Fin n)) (x y : Fin n)
    (h : 2 ≤ multiplicity [p,q] x y) : p x < p y ∧ q x < q y := by
  by_cases he : x = y
  · simp [OMA.S_mo_481671.multiplicity, he] at h
  by_cases hp : p x < p y <;> by_cases hq : q x < q y <;>
    simp [OMA.S_mo_481671.multiplicity, he, hp, hq] at h ⊢

private lemma pairEither {n : ℕ} (p q : Equiv.Perm (Fin n)) (x y : Fin n)
    (h : 1 ≤ multiplicity [p,q] x y) : p x < p y ∨ q x < q y := by
  by_cases he : x = y
  · simp [OMA.S_mo_481671.multiplicity, he] at h
  by_cases hp : p x < p y <;> by_cases hq : q x < q y <;>
    simp [OMA.S_mo_481671.multiplicity, he, hp, hq] at h ⊢

private lemma noCycle (f : Fin 4 → Fin 32) (h : ∀ i, f i < f (i + 1)) : False := by
  have h0 : f 0 < f 1 := h 0
  have h1 : f 1 < f 2 := h 1
  have h2 : f 2 < f 3 := h 2
  have h3 : f 3 < f 0 := h 3
  exact (lt_irrefl (f 0)) (((h0.trans h1).trans h2).trans h3)

theorem impossible : ¬ (type_of% @OMA.S_mo_481671.main) := by
  intro cover
  obtain ⟨p,q,dominates⟩ := cover 32 (by decide) profile (by decide +kernel)
  have inner (i j : Fin 4) : p (a i j) < p (b i (j + 1)) :=
    (pairBoth p q _ _ ((counts.1 i j) ▸ dominates _ _)).1
  have outer (i j k : Fin 4) : q (a i j) < q (b (i + 1) k) :=
    (pairBoth p q _ _ ((counts.2.1 i j k) ▸ dominates _ _)).2
  have diagonal (i j : Fin 4) : p (b i j) < p (a i j) ∨ q (b i j) < q (a i j) :=
    pairEither p q _ _ ((counts.2.2 i j).2 ▸ dominates _ _)
  -- In each row, p cannot reverse all four diagonals.
  have missing (i : Fin 4) : ∃ j, ¬ p (b i j) < p (a i j) := by
    by_contra! all
    exact noCycle (fun j => p (b i j)) fun j => (all j).trans (inner i j)
  choose j hj using missing
  -- Thus q reverses a diagonal in every row, producing an outer 4-cycle.
  apply noCycle fun i => q (b i (j i))
  intro i
  exact ((diagonal i (j i)).resolve_left (hj i)).trans (outer i (j i) (j (i + 1)))

end MajorityCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_481671.main) :=
  MajorityCounterexample.impossible
