import OMAReductions.R_UnionClosed_union_closed_R1_H3_R2
import Mathlib

/-!
For each coordinate compare the largest lower endpoint and the smallest
upper endpoint. If every projection has a common point, the coordinatewise
choice belongs to all boxes. Otherwise find two boxes on opposite sides of
an integer cut. Rectangularity of their union yields adjacent points on a
common coordinate line. Rectangularity of the union of any third box with
each of the two extreme boxes forces the projection of that third box onto
the line to lie in the third box itself. Thus the two points hit the family.
-/

namespace BoxTransversal
open Finset

variable {d : ℕ}
abbrev Grid (d : ℕ) := Fin d → ℤ

structure Box (d : ℕ) where
  lo : Grid d
  hi : Grid d
  valid : ∀ i, lo i ≤ hi i

def In (b : Box d) (x : Grid d) : Prop := ∀ i, b.lo i ≤ x i ∧ x i ≤ b.hi i

def Between (x y z : Grid d) : Prop :=
  ∀ j, (x j ≤ z j ∧ z j ≤ y j) ∨ (y j ≤ z j ∧ z j ≤ x j)

theorem in_lo (b : Box d) : In b b.lo := fun j => ⟨le_rfl,b.valid j⟩
theorem in_hi (b : Box d) : In b b.hi := fun j => ⟨b.valid j,le_rfl⟩

theorem convex {b : Box d} {x y z : Grid d} (hx : In b x) (hy : In b y)
    (hz : Between x y z) : In b z := by
  intro j
  have := hx j
  have := hy j
  rcases hz j with h|h <;> omega

abbrev splice (x : Grid d) (i : Fin d) (v : ℤ) : Grid d := Function.update x i v

theorem between_splice (x y : Grid d) (i : Fin d) (v : ℤ)
    (h : (x i ≤ v ∧ v ≤ y i) ∨ (y i ≤ v ∧ v ≤ x i)) :
    Between x y (splice x i v) := by
  intro j
  by_cases eq : j = i
  · subst j; simpa [splice] using h
  · simp only [splice,Function.update_of_ne eq]
    omega

/-- Every box meets one of two equal or consecutive points on one coordinate line. -/
theorem transversal {T : Type*} [Fintype T] [Nonempty T] (b : T → Box d)
    (joint : ∀ a c x y z, In (b a) x → In (b c) y → Between x y z →
      In (b a) z ∨ In (b c) z) :
    ∃ p q : Grid d, (∃ a, In (b a) p) ∧ (∃ a, In (b a) q) ∧
      (p = q ∨ ∃ i, q = splice p i (p i+1)) ∧ ∀ a, In (b a) p ∨ In (b a) q := by
  classical
  let upper (i : Fin d) := (univ.image (fun a : T => (b a).lo i)).max'
    (univ_nonempty.image _)
  have dominates (a : T) (i : Fin d) : (b a).lo i ≤ upper i :=
    le_max' _ _ (mem_image_of_mem (fun c : T => (b c).lo i) (mem_univ a))
  by_cases common : ∀ a, In (b a) upper
  · let a : T := Classical.choice ‹Nonempty T›
    exact ⟨upper,upper,⟨a,common a⟩,⟨a,common a⟩,Or.inl rfl,fun a => Or.inl (common a)⟩
  push Not at common
  obtain ⟨bad, hbad⟩ := common
  obtain ⟨i,hi⟩ : ∃ i, (b bad).hi i < upper i := by
    by_contra! h
    exact hbad fun i => ⟨dominates bad i,h i⟩
  let lower := (univ.image (fun a : T => (b a).hi i)).min' (univ_nonempty.image _)
  have lower_le (a : T) : lower ≤ (b a).hi i :=
    min'_le _ _ (mem_image_of_mem (fun c : T => (b c).hi i) (mem_univ a))
  obtain ⟨a,_,ha⟩ := mem_image.mp (min'_mem (univ.image (fun a : T => (b a).hi i)) (univ_nonempty.image _))
  change (b a).hi i = lower at ha
  obtain ⟨c,_,hc⟩ := mem_image.mp (max'_mem (univ.image (fun a : T => (b a).lo i)) (univ_nonempty.image _))
  change (b c).lo i = upper i at hc
  have strict : lower < upper i := (lower_le bad).trans_lt hi
  let p := (b a).hi
  let q := splice p i (lower+1)
  have hp : In (b a) p := in_hi _
  have hqbetween : Between p (b c).lo q :=
    between_splice _ _ _ _ (Or.inl ⟨by dsimp [p]; omega,by omega⟩)
  have qval : q i = lower+1 := by simp [q,splice]
  have hq : In (b c) q := by
    rcases joint a c _ _ _ hp (in_lo _) hqbetween with hb | hb
    · have := (hb i).2; omega
    · exact hb
  have adj : upper i = lower+1 := by have := (hq i).1; omega
  have separate (z : Grid d) (za : In (b a) z) (zc : In (b c) z) : False := by
    have := (za i).2; have := (zc i).1; omega
  refine ⟨p,q,⟨a,hp⟩,⟨c,hq⟩,Or.inr ⟨i,?_⟩,?_⟩
  · dsimp [q,p]; rw [ha]
  intro r
  let t := (b r).lo
  let z := splice p i (t i)
  have zp : Between p t z := between_splice _ _ _ _ (by omega)
  have zq : Between q t z := by
    intro j
    by_cases h : j=i
    · subst j; simp only [z,splice,Function.update_self]; omega
    · simp only [q,z,splice,Function.update_of_ne h]; omega
  have hz : In (b r) z := by
    rcases joint a r _ _ _ hp (in_lo _) zp with h|h
    · rcases joint c r _ _ _ hq (in_lo _) zq with h'|h'
      · exact (separate _ h h').elim
      · exact h'
    · exact h
  by_cases low : (b r).lo i ≤ lower
  · left
    intro j
    by_cases h : j=i
    · subst j; change (b r).lo i ≤ (b a).hi i ∧ (b a).hi i ≤ (b r).hi i
      rw [ha]; exact ⟨low,lower_le r⟩
    · simpa only [z,splice,Function.update_of_ne h] using hz j
  · right
    intro j
    by_cases h : j=i
    · subst j
      have := dominates r i
      have := (b r).valid i
      rw [qval]; omega
    · simpa only [z,q,splice,Function.update_of_ne h] using hz j

end BoxTransversal

namespace BoxTransversal
open Finset

theorem frequent_of_pair {α : Type*} [DecidableEq α] (A : Finset (Finset α))
    (closed : ∀ U ∈ A, ∀ V ∈ A, U ∪ V ∈ A) (p q : α)
    (hp : ∃ U ∈ A, p ∈ U) (hq : ∃ U ∈ A, q ∈ U)
    (hits : ∀ U ∈ A, U.Nonempty → p ∈ U ∨ q ∈ U) :
    ∃ v : α, A.card ≤ 2 * (A.filter (fun U => v ∈ U)).card := by
  let P := A.filter (fun U => p ∈ U)
  let Q := A.filter (fun U => q ∈ U)
  obtain ⟨X,hX,hp⟩ := hp
  obtain ⟨Y,hY,hq⟩ := hq
  have both : (P ∩ Q).Nonempty := ⟨X∪Y,mem_inter.mpr
    ⟨mem_filter.mpr ⟨closed X hX Y hY,mem_union_left _ hp⟩,
     mem_filter.mpr ⟨closed X hX Y hY,mem_union_right _ hq⟩⟩⟩
  have sub : A.erase ∅ ⊆ P ∪ Q := by
    intro U h
    obtain ⟨hne,hA⟩ := mem_erase.mp h
    rcases hits U hA (nonempty_iff_ne_empty.mpr hne) with h|h
    · exact mem_union_left _ (mem_filter.mpr ⟨hA,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hA,h⟩)
  have hs := card_le_card sub
  have hpos := card_pos.mpr both
  have he := card_le_card (s := A) (t := insert ∅ (A.erase ∅))
    (fun U hU => by by_cases hz : U=∅ <;> simp [hz,hU])
  have hi := card_insert_le ∅ (A.erase ∅)
  have hu := card_union_add_card_inter P Q
  by_cases h : A.card ≤ 2*P.card
  · exact ⟨p,h⟩
  · exact ⟨q,show A.card ≤ 2*Q.card by omega⟩

theorem frequent {α : Type*} [DecidableEq α] {d : ℕ} (e : α ↪ Grid d)
    (A : Finset (Finset α)) (nontrivial : ∃ X ∈ A, X.Nonempty)
    (closed : ∀ U ∈ A, ∀ V ∈ A, U ∪ V ∈ A)
    (boxes : ∀ X ∈ A, X.Nonempty → ∃ lo hi : Grid d, ∀ z : Grid d,
      (∃ x ∈ X, e x=z) ↔ ∀ j, lo j ≤ z j ∧ z j ≤ hi j) :
    ∃ v : α, A.card ≤ 2 * (A.filter (fun U => v ∈ U)).card := by
  classical
  let T := ↑(A.filter (fun X : Finset α => X.Nonempty))
  have props (t : T) := mem_filter.mp t.property
  obtain ⟨X,hX,hne⟩ := nontrivial
  letI : Nonempty T := ⟨⟨X,mem_filter.mpr ⟨hX,hne⟩⟩⟩
  have avail (t : T) := boxes t.val (props t).1 (props t).2
  choose lo hi hbox using avail
  let b (t : T) : Box d := ⟨lo t,hi t,by
    obtain ⟨w,hw⟩ := (props t).2
    intro j
    obtain ⟨hl,hu⟩ := (hbox t (e w)).mp ⟨w,hw,rfl⟩ j
    exact hl.trans hu⟩
  have eqv (t : T) (z : Grid d) : (∃ x ∈ t.val, e x=z) ↔ In (b t) z := hbox t z
  have joint (a c : T) (x y z : Grid d) (hx : In (b a) x) (hy : In (b c) y)
      (hz : Between x y z) : In (b a) z ∨ In (b c) z := by
    obtain ⟨u,hu,eu⟩ := (eqv a x).mpr hx
    obtain ⟨v,hv,ev⟩ := (eqv c y).mpr hy
    let t : T := ⟨a.val ∪ c.val,mem_filter.mpr
      ⟨closed _ (props a).1 _ (props c).1,⟨u,mem_union_left _ hu⟩⟩⟩
    have tx := (eqv t x).mp ⟨u,mem_union_left _ hu,eu⟩
    have ty := (eqv t y).mp ⟨v,mem_union_right _ hv,ev⟩
    obtain ⟨w,hw,ew⟩ := (eqv t z).mpr (convex tx ty hz)
    rcases mem_union.mp hw with hw|hw
    · exact Or.inl ((eqv a z).mp ⟨w,hw,ew⟩)
    · exact Or.inr ((eqv c z).mp ⟨w,hw,ew⟩)
  obtain ⟨p,q,⟨a,ha⟩,⟨c,hc⟩,_,hit⟩ := transversal b joint
  obtain ⟨u,hu,eu⟩ := (eqv a p).mpr ha
  obtain ⟨v,hv,ev⟩ := (eqv c q).mpr hc
  apply frequent_of_pair A closed u v ⟨a.val,(props a).1,hu⟩ ⟨c.val,(props c).1,hv⟩
  intro R hR hn
  let t : T := ⟨R,mem_filter.mpr ⟨hR,hn⟩⟩
  rcases hit t with h|h
  · obtain ⟨w,hw,ew⟩ := (eqv t p).mpr h
    exact Or.inl (e.injective (ew.trans eu.symm) ▸ hw)
  · obtain ⟨w,hw,ew⟩ := (eqv t q).mpr h
    exact Or.inr (e.injective (ew.trans ev.symm) ▸ hw)

end BoxTransversal

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1_H3_R2.H1 := by
  intro m d A e closed nontrivial boxes
  obtain ⟨X,hX,hne⟩ := nontrivial
  obtain ⟨v,hv⟩ := BoxTransversal.frequent e A ⟨X,hX,Finset.nonempty_iff_ne_empty.mpr hne⟩ closed boxes
  refine ⟨v,?_⟩
  have h : (A.card : ℚ) ≤ 2 * (A.filter (fun U => v ∈ U)).card := by exact_mod_cast hv
  linarith
