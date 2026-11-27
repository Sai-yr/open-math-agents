import OMAReductions.R_mse_4941096_R1
import Mathlib.Tactic

open Finset OMA.S_mse_4941096

namespace StrictSecondNeighborhood

private lemma reachable_closed {out : ℤ → Finset ℤ} {P : ℤ → Prop}
    (h : ∀ a, P a → ∀ b ∈ out a, P b) {v w : ℤ} (hv : P v)
    (hw : Relation.ReflTransGen (fun i j => j ∈ out i) v w) : P w := by
  induction hw with
  | refl => exact hv
  | tail _ hab ih => exact h _ ih _ hab

private lemma has_successor {out : ℤ → Finset ℤ}
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j ∈ out i) v w)
    (v : ℤ) : (out v).Nonempty := by
  by_contra h
  have hp : v+1 = v := reachable_closed (P := fun x => x=v)
    (fun _ hx y hy => by subst_vars; exact (h ⟨y,hy⟩).elim) rfl (strong v (v+1))
  omega

/-- If each vertex in the neighborhood has an arc to another member, its
cardinality is at least three: the first three vertices of a walk are distinct. -/
private lemma three {out : ℤ → Finset ℤ} {v : ℤ} (hn : (out v).Nonempty)
    (irr : ∀ x, x ∉ out x) (asym : ∀ x y, y ∈ out x → x ∉ out y)
    (h : ∀ x ∈ out v, ∃ y ∈ out v, y ∈ out x) : 3 ≤ (out v).card := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb, hab⟩ := h a ha
  obtain ⟨c, hc, hbc⟩ := h b hb
  have h₁ : a ≠ b := by rintro rfl; exact irr a hab
  have h₂ : b ≠ c := by rintro rfl; exact irr b hbc
  have h₃ : a ≠ c := by rintro rfl; exact asym a b hab hbc
  have sub : ({a,b,c} : Finset ℤ) ⊆ out v := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  simpa [h₁,h₂,h₃] using card_le_card sub

/-- A path whose closed out-neighborhoods cover every succeeding step is
incompatible with strong connectivity, finite indegrees and infinitely many
vertices. Every tail would have to contain an in-neighbor of 0 or 0 itself. -/
private lemma no_spine (out : ℤ → Finset ℤ)
    (strong : ∀ v w, Relation.ReflTransGen (fun i j => j ∈ out i) v w)
    (W : ℕ) (bound : ∀ v w, w ∈ out v → v-(W:ℤ) ≤ w ∧ w ≤ v+(W:ℤ))
    (s : ℕ → ℤ)
    (step : ∀ i, ∀ x ∈ out (s i), ∀ y ∈ out x, y ∈ out (s i) ∨ y ∈ out (s (i+1))) : False := by
  classical
  let star (i : ℕ) := insert (s i) (out (s i))
  have advance (i : ℕ) (x : ℤ) (hx : x ∈ star i) (y : ℤ) (hy : y ∈ out x) :
      y ∈ star i ∨ y ∈ star (i+1) := by
    rcases mem_insert.mp hx with he | hm
    · exact Or.inl (mem_insert_of_mem (he ▸ hy))
    · exact (step i x hm y hy).imp mem_insert_of_mem mem_insert_of_mem
  have distinct (a b : ℕ) (hab : a < b) : s a ≠ s b := by
    intro he
    let C := (range b).biUnion star
    have hclosed (x : ℤ) (hx : x ∈ C) (y : ℤ) (hy : y ∈ out x) : y ∈ C := by
      obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
      rcases advance i x hxi y hy with h | h
      · exact mem_biUnion.mpr ⟨i,hi,h⟩
      · by_cases hk : i+1 < b
        · exact mem_biUnion.mpr ⟨i+1,mem_range.mpr hk,h⟩
        · have hij : i+1=b := by have := mem_range.mp hi; omega
          have hs : star (i+1) = star a := by simp only [star, hij, ← he]
          exact mem_biUnion.mpr ⟨a,mem_range.mpr hab,hs ▸ h⟩
    have inside : s a ∈ C := mem_biUnion.mpr ⟨a,mem_range.mpr hab,mem_insert_self ..⟩
    obtain ⟨z,hz⟩ := C.exists_notMem
    exact hz (reachable_closed hclosed inside (strong _ z))
  have inj : Function.Injective s := by
    intro a b he
    rcases lt_trichotomy a b with h | h | h
    · exact (distinct a b h he).elim
    · exact h
    · exact (distinct b a h he.symm).elim
  have finite : (s ⁻¹' Set.Icc (-(W : ℤ)) W).Finite :=
    (Set.finite_Icc _ _).preimage inj.injOn
  obtain ⟨M, hM⟩ := finite.bddAbove
  let N := M+1
  have hall (z : ℤ) : ∃ i ≥ N, z ∈ star i := by
    apply reachable_closed (P := fun z => ∃ i ≥ N, z ∈ star i) _ _ (strong (s N) z)
    · rintro x ⟨i,hi,hx⟩ y hy
      rcases advance i x hx y hy with h | h
      · exact ⟨i,hi,h⟩
      · exact ⟨i+1,by omega,h⟩
    · exact ⟨N,le_rfl,mem_insert_self ..⟩
  obtain ⟨i, hi, hzero⟩ := hall 0
  have hstrip : s i ∈ Set.Icc (-(W:ℤ)) W := by
    rcases mem_insert.mp hzero with h | h
    · simp [← h]
    · have := bound _ _ h
      constructor <;> omega
  have hle := hM (show i ∈ s ⁻¹' Set.Icc (-(W:ℤ)) W from hstrip)
  dsimp [N] at hi
  omega

theorem obstruction : OMA.R_mse_4941096_R1.H1 := by
  classical
  intro out hg
  obtain ⟨irr, asym, strong, ⟨W, bound⟩, equal⟩ := hg
  let minimum (v : ℤ) := ∀ x, (out v).card ≤ (out x).card
  let cycle (v : ℤ) := ∀ u ∈ out v, ∃ w ∈ out v, w ∈ out u
  suffices h : ∃ v, minimum v ∧ cycle v by
    obtain ⟨v,hm,hc⟩ := h
    exact ⟨v,hm,three (has_successor strong v) irr asym hc,hc⟩
  by_contra hnone
  have choose_step (v : ℤ) : ∃ u : ℤ, minimum v →
      u ∈ out v ∧ minimum u ∧ out u = second out v := by
    by_cases hm : minimum v
    · have hn : ¬cycle v := fun h => hnone ⟨v,hm,h⟩
      change ¬∀ u ∈ out v, ∃ w ∈ out v, w ∈ out u at hn
      push Not at hn
      obtain ⟨u, hu, sink⟩ := hn
      have sub : out u ⊆ second out v := by
        intro w hw
        exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨u,hu,hw⟩,fun hv => sink w hv hw⟩
      have he := eq_of_subset_of_card_le sub ((equal v) ▸ hm u)
      exact ⟨u,fun _ => ⟨hu,fun x => by rw [he, ← equal v]; exact hm x,he⟩⟩
    · exact ⟨v,fun hv => (hm hv).elim⟩
  choose f hf using choose_step
  have hex : ∃ n : ℕ, ∃ v : ℤ, (out v).card = n := ⟨_,0,rfl⟩
  obtain ⟨start, hstart⟩ := Nat.find_spec hex
  have hm0 : minimum start := fun x => hstart ▸ Nat.find_min' hex ⟨x,rfl⟩
  let s (i : ℕ) := f^[i] start
  have next (i : ℕ) : s (i+1) = f (s i) := Function.iterate_succ_apply' ..
  have hm (i : ℕ) : minimum (s i) := by
    induction i with
    | zero => exact hm0
    | succ i ih => rw [next]; exact (hf _ ih).2.1
  apply no_spine out strong W bound s
  intro i x hx y hy
  by_cases h : y ∈ out (s i)
  · exact Or.inl h
  · right
    rw [next, (hf _ (hm i)).2.2]
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,hx,hy⟩,h⟩

end StrictSecondNeighborhood

theorem OMA.solution : OMA.R_mse_4941096_R1.H1 := StrictSecondNeighborhood.obstruction
