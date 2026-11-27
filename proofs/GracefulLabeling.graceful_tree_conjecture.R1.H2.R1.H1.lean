import OMAReductions.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1

/-!
# Proof of the component criterion for reflecting a partial labeling
-/

open SimpleGraph OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1

/-- Adjacent vertices away from the axis, or vertices whose labels are reflections. -/
private def linked {V : Type*} (T : SimpleGraph V) (f : V → ℕ) (k : ℕ) (a b : V) : Prop :=
  (T.Adj a b ∧ 2 * f a ≠ k ∧ 2 * f b ≠ k) ∨ f a + f b = k

/-- Reflect labels on a chosen set in the axis with doubled coordinate k. -/
private noncomputable def foldLabels {V : Type*} (f : V → ℕ) (k : ℕ) (s : Set V) (a : V) : ℕ := by
  classical
  exact if a ∈ s then k - f a else f a

private lemma mixed_reflection {a b k : ℕ} (ha : a ≤ k)
    (h : Nat.dist (k - a) b = Nat.dist a b) : 2 * a = k ∨ 2 * b = k := by
  simp only [Nat.dist] at h
  omega

private lemma reflects_distance {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    Nat.dist (k - a) (k - b) = Nat.dist a b := by
  simp only [Nat.dist]
  omega

theorem OMA.solution : OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1.H1 := by
  classical
  intro V T f q h t hf hbound ht hh
  let k := q + h
  have hk (a : V) : f a ≤ k := (hbound a).trans (Nat.le_add_right ..)
  change (∃ s : Set V, let g := foldLabels f k s
    Function.Injective g ∧ (∀ x, g x < q) ∧
      ∀ a b, T.Adj a b → Nat.dist (g a) (g b) = Nat.dist (f a) (f b)) ↔ ∀ x, Relation.ReflTransGen (linked T f k) t x → h < f x
  constructor
  · rintro ⟨s, hi, hb, he⟩
    have htop : t ∈ s := by
      by_contra hn
      have := hb t
      simp [foldLabels, hn, ht] at this
    have propagate {a b : V} (ha : a ∈ s) (hab : linked T f k a b) : b ∈ s := by
      by_contra hn
      rcases hab with ⟨hadj, hax, hbx⟩ | hpair
      · have hd := he a b hadj
        simp only [foldLabels, ha, hn, if_true, if_false] at hd
        rcases mixed_reflection (hk a) hd with h | h
        · exact hax h
        · exact hbx h
      · have hab' : foldLabels f k s a = foldLabels f k s b := by
          simp only [foldLabels, ha, hn, if_true, if_false]
          omega
        exact hn (hi hab' ▸ ha)
    intro x hreach
    have hx : x ∈ s := by
      induction hreach with
      | refl => exact htop
      | tail _ hlink ihr => exact propagate ihr hlink
    have hv := hb x
    simp only [foldLabels, hx, if_true] at hv
    omega
  · intro hclear
    let s : Set V := {x | Relation.ReflTransGen (linked T f k) t x}
    have hstep {a b : V} (ha : a ∈ s) (hab : linked T f k a b) : b ∈ s :=
      Relation.ReflTransGen.tail ha hab
    have unequal {a b : V} (ha : a ∈ s) (hb : b ∉ s) : k - f a ≠ f b := by
      intro he
      exact hb (hstep ha (Or.inr (by have := hk a; omega)))
    have fixed {a b : V} (ha : a ∈ s) (hb : b ∉ s) (hab : T.Adj a b) :
        Nat.dist (k - f a) (f b) = Nat.dist (f a) (f b) := by
      have hp : 2 * f a = k ∨ 2 * f b = k := by
        by_contra! hn
        exact hb (hstep ha (Or.inl ⟨hab, hn.1, hn.2⟩))
      have := hk a
      simp only [Nat.dist]
      rcases hp with hp | hp <;> omega
    refine ⟨s, ?_, ?_, ?_⟩
    · intro a b hab
      by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
        simp only [foldLabels, ha, hb, if_true, if_false] at hab
      · apply hf
        have := hk a
        have := hk b
        omega
      · exact False.elim (unequal ha hb hab)
      · exact False.elim (unequal hb ha hab.symm)
      · exact hf hab
    · intro a
      by_cases ha : a ∈ s
      · have := hclear a ha
        simp only [foldLabels, ha, if_true]
        omega
      · have hne : f a ≠ q := by
          intro hx
          have hEq := hf (hx.trans ht.symm)
          subst a
          exact ha Relation.ReflTransGen.refl
        simpa [foldLabels, ha] using lt_of_le_of_ne (hbound a) hne
    · intro a b hab
      by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
        simp only [foldLabels, ha, hb, if_true, if_false]
      · exact reflects_distance (hk a) (hk b)
      · exact fixed ha hb hab
      · simpa only [Nat.dist_comm] using fixed hb ha hab.symm
