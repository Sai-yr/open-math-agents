import OMAReductions.R_UnionClosed_union_closed_R1_H3_R1_H2_R1
import Mathlib

/-!
For a trace family on a four-element member, let s and t count its singleton
and three-element traces, respectively. Unions of singleton traces prove
s ≤ t + 2. The exact incidence excess of an occupied fiber is
4 + 2t − 2s minus 4 if the empty trace occurs. Thus every negative fiber
has the empty trace and more singletons than triples. Its deficit is at
most four. Summing the excesses forces the witnesses in the statement.
-/

namespace FourTrace
open Finset
abbrev Core := Finset (Fin 4)
abbrev Family := Finset Core

def singles (F : Family) : Finset (Fin 4) := univ.filter fun j => {j} ∈ F
def triples (F : Family) : Family := F.filter (fun U => U.card = 3)
def mass (F : Family) : ℕ := ∑ U ∈ F, U.card

theorem union_subset_in {F : Family} (hF : ∀ U ∈ F, ∀ V ∈ F, U ∪ V ∈ F)
    {S : Core} (hne : S.Nonempty) (h : S ⊆ singles F) : S ∈ F := by
  induction S using Finset.induction_on with
  | empty => exact (not_nonempty_empty hne).elim
  | @insert j S hj ih =>
    have one : {j} ∈ F := (mem_filter.mp (h (mem_insert_self j S))).2
    by_cases more : S.Nonempty
    · have mem := ih more (fun _ hx => h (mem_insert_of_mem hx))
      simpa using hF {j} one S mem
    · have es := not_nonempty_iff_eq_empty.mp more
      simpa [es] using one

theorem card_singles (F : Family) :
    (F.filter (fun U => U.card = 1)).card = (singles F).card := by
  have eq : F.filter (fun U => U.card = 1) = (singles F).image (fun j => {j}) := by
    ext U
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨hU,h⟩
      obtain ⟨j,rfl⟩ := card_eq_one.mp h
      exact ⟨j,by simpa [singles] using hU,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨(mem_filter.mp hj).2,card_singleton _⟩
  rw [eq]
  exact card_image_of_injective _ (fun _ _ h => singleton_inj.mp h)

theorem singles_le (F : Family) (closed : ∀ U ∈ F, ∀ V ∈ F, U ∪ V ∈ F) :
    (singles F).card ≤ (triples F).card + 2 := by
  have sub : (singles F).powersetCard 3 ⊆ triples F := by
    intro T hT
    obtain ⟨hs,hc⟩ := mem_powersetCard.mp hT
    exact mem_filter.mpr ⟨union_subset_in closed (card_pos.mp (by omega)) hs,hc⟩
  have h := card_le_card sub
  rw [card_powersetCard] at h
  have n : (singles F).card ≤ 4 := (card_le_univ _)
  have q : ∀ x ∈ range 5, x ≤ x.choose 3 + 2 := by decide
  exact (q _ (mem_range.mpr (by omega))).trans (by omega)

theorem balance (F : Family) (ht : univ ∈ F) :
    4 * F.card + 2 * (triples F).card + 4 =
    2 * mass F + 2 * (singles F).card + (if ∅ ∈ F then 4 else 0) := by
  have point : ∀ U ∈ (univ : Finset Core),
    4 + (if U.card = 3 then 2 else 0) + (if U = univ then 4 else 0) =
    2 * U.card + (if U.card = 1 then 2 else 0) + (if U = ∅ then 4 else 0) := by decide
  have h := Finset.sum_congr (s₁ := F) (s₂ := F) rfl (fun U _ => point U (mem_univ U))
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at h
  have coeff (p : Core → Prop) [DecidablePred p] (n : ℕ) :
      (∑ U ∈ F, if p U then n else 0) = n * (F.filter p).card := by
    rw [← sum_filter]
    simp [Nat.mul_comm]
  rw [coeff _ 2,coeff _ 2, ← mul_sum, card_singles] at h
  simpa [triples,mass,ht,Nat.mul_comm 4 F.card] using h

def deficient (F : Family) : Prop := ∅ ∈ F ∧ (triples F).card < (singles F).card

instance (F : Family) : Decidable (deficient F) := by unfold deficient; infer_instance

theorem local_bound (F : Family) (ht : univ ∈ F)
    (closed : ∀ U ∈ F, ∀ V ∈ F, U ∪ V ∈ F) :
    4 * F.card ≤ 2 * mass F + (if deficient F then 4 else 0) := by
  have b := balance F ht
  have s := singles_le F closed
  by_cases he : (∅ : Core) ∈ F
  · simp only [he, if_true] at b
    by_cases hd : (triples F).card < (singles F).card
    · simp only [deficient, he, hd, and_self, if_true]
      omega
    · simp only [deficient, hd, and_false, if_false]
      omega
  · simp only [he, if_false] at b
    simp only [deficient, he, false_and, if_false]
    omega

def closed (F : Family) : Prop := ∀ U ∈ F, ∀ V ∈ F, U ∪ V ∈ F

end FourTrace

namespace FourTrace

open Finset

variable {α : Type*} [DecidableEq α]

def carrier (e : Fin 4 ↪ α) := (univ : Core).map e

def trace (e : Fin 4 ↪ α) (X : Finset α) : Core := univ.filter (fun i => e i ∈ X)

def outside (e : Fin 4 ↪ α) (X : Finset α) := X \ carrier e

def block (e : Fin 4 ↪ α) (A : Finset (Finset α)) (B : Finset α) :=
  A.filter (fun X => outside e X = B)

def traces (e : Fin 4 ↪ α) (A : Finset (Finset α)) (B : Finset α) : Family :=
  (block e A B).image (trace e)

theorem trace_union (e : Fin 4 ↪ α) (X Y : Finset α) :
    trace e (X ∪ Y) = trace e X ∪ trace e Y := by ext i; simp [trace]

theorem outside_union (e : Fin 4 ↪ α) (X Y : Finset α) :
    outside e (X ∪ Y) = outside e X ∪ outside e Y := by
  ext i
  simp only [outside,mem_sdiff,mem_union]
  tauto

theorem trace_carrier (e : Fin 4 ↪ α) : trace e (carrier e) = univ := by
  ext i
  simp [trace,carrier]

theorem reconstruct (e : Fin 4 ↪ α) (X : Finset α) :
    outside e X ∪ (trace e X).map e = X := by
  ext i
  by_cases hi : i ∈ carrier e
  · obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    simp [outside,trace,carrier]
  · have hn : ∀ j : Fin 4, e j ≠ i := by
      rintro j rfl
      exact hi (by simp [carrier])
    simp [outside,trace,hi,hn]

theorem trace_injOn (e : Fin 4 ↪ α) (A : Finset (Finset α)) (B : Finset α) :
    Set.InjOn (trace e) (block e A B : Set (Finset α)) := by
  intro X hX Y hY eq
  have hx := (mem_filter.mp hX).2
  have hy := (mem_filter.mp hY).2
  rw [← reconstruct e X,← reconstruct e Y,eq,hx,hy]

theorem counts (e : Fin 4 ↪ α) (A : Finset (Finset α)) (B : Finset α) :
    (traces e A B).card = (block e A B).card ∧
    mass (traces e A B) = ∑ X ∈ block e A B, (trace e X).card := by
  exact ⟨card_image_of_injOn (trace_injOn e A B),sum_image (trace_injOn e A B)⟩

theorem closed_traces (e : Fin 4 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (B : Finset α) : closed (traces e A B) := by
  intro U hU V hV
  obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
  obtain ⟨Y,hY,rfl⟩ := mem_image.mp hV
  have hx := mem_filter.mp hX
  have hy := mem_filter.mp hY
  exact mem_image.mpr ⟨X∪Y,mem_filter.mpr ⟨hA X hx.1 Y hy.1,by simp [outside_union,hx.2,hy.2]⟩,
    trace_union e X Y⟩

theorem top_mem (e : Fin 4 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A)
    (B : Finset α) (hB : B ∈ A.image (outside e)) : univ ∈ traces e A B := by
  obtain ⟨X,hX,rfl⟩ := mem_image.mp hB
  refine mem_image.mpr ⟨X∪carrier e,mem_filter.mpr ⟨hA X hX _ hc,?_⟩,?_⟩
  · rw [outside_union]
    simp [outside]
  · simp [trace_union, trace_carrier]

theorem incidences (e : Fin 4 ↪ α) (A : Finset (Finset α)) :
    (∑ X ∈ A, (trace e X).card) =
      ∑ i : Fin 4, (A.filter (fun X => e i ∈ X)).card := by
  simp only [trace,card_filter]
  exact sum_comm

theorem bound (e : Fin 4 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A) :
    4 * A.card ≤
      2 * (∑ i : Fin 4, (A.filter (fun X => e i ∈ X)).card) +
      4 * ((A.image (outside e)).filter (fun B => deficient (traces e A B))).card := by
  let indices := A.image (outside e)
  have point (B : Finset α) (hB : B ∈ indices) :
      4 * (block e A B).card ≤
        2 * (∑ X ∈ block e A B, (trace e X).card) +
          (if deficient (traces e A B) then 4 else 0) := by
    obtain ⟨hc',hm⟩ := counts e A B
    have h := local_bound (traces e A B) (top_mem e A hA hc B hB) (closed_traces e A hA B)
    rwa [hc',hm] at h
  have ht := sum_le_sum point
  have hcounts : ∑ B ∈ indices, (block e A B).card = A.card :=
    (card_eq_sum_card_fiberwise (f := outside e) (s := A) (t := indices)
      (fun X hX => mem_image_of_mem _ hX)).symm
  have hm : ∑ B ∈ indices, ∑ X ∈ block e A B, (trace e X).card =
      ∑ X ∈ A, (trace e X).card :=
    sum_fiberwise_of_maps_to (fun X hX => mem_image_of_mem (outside e) hX) _
  rw [← mul_sum, hcounts, sum_add_distrib, ← mul_sum, hm, incidences] at ht
  have coeff : (∑ B ∈ indices, if deficient (traces e A B) then 4 else 0) =
      4 * (indices.filter (fun B => deficient (traces e A B))).card := by
    rw [← sum_filter]
    simp [Nat.mul_comm]
  rwa [coeff] at ht

end FourTrace

namespace FourTrace
open Finset
variable {α : Type*} [DecidableEq α]

theorem bad_index (e : Fin 4 ↪ α) (A : Finset (Finset α)) {B : Finset α}
    (noSingle : ∀ X ∈ A, X.card ≠ 1) (h : deficient (traces e A B)) :
    B ∈ A ∧ B.Nonempty ∧ Disjoint B (carrier e) := by
  obtain ⟨h₀,more⟩ := h
  obtain ⟨Y,hY,emptyTrace⟩ := mem_image.mp h₀
  obtain ⟨hY,ho⟩ := mem_filter.mp hY
  have eqY := reconstruct e Y
  rw [ho,emptyTrace] at eqY
  simp only [map_empty,union_empty] at eqY
  refine ⟨eqY.symm ▸ hY,?_,by rw [← ho]; exact sdiff_disjoint⟩
  obtain ⟨j,hj⟩ : (singles (traces e A B)).Nonempty := card_pos.mp (by omega)
  have ht := (mem_filter.mp hj).2
  obtain ⟨X,hX,htr⟩ := mem_image.mp ht
  obtain ⟨hx,ho'⟩ := mem_filter.mp hX
  apply nonempty_iff_ne_empty.mpr
  intro he
  have eqX := reconstruct e X
  rw [ho',he,htr] at eqX
  apply noSingle X hx
  rw [← eqX]
  simp

theorem multiplicity (e : Fin 4 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A)
    (noSingle : ∀ X ∈ A, X.card ≠ 1)
    (rare : ∀ i, 2 * (A.filter (fun X => e i ∈ X)).card < A.card) :
    (if A.card % 2 = 0 then 2 else 1) ≤ (A.filter (fun B =>
      B.Nonempty ∧ Disjoint B (carrier e) ∧ deficient (traces e A B))).card := by
  have hs := bound e A hA hc
  rw [Fin.sum_univ_four] at hs
  have hsub : ((A.image (outside e)).filter (fun B => deficient (traces e A B))) ⊆
      A.filter (fun B => B.Nonempty ∧ Disjoint B (carrier e) ∧ deficient (traces e A B)) := by
    intro B hB
    have d := (mem_filter.mp hB).2
    obtain ⟨hb,hn,hd⟩ := bad_index e A noSingle d
    exact mem_filter.mpr ⟨hb,hn,hd,d⟩
  have le := card_le_card hsub
  have r0 := rare 0
  have r1 := rare 1
  have r2 := rare 2
  have r3 := rare 3
  split <;> omega

end FourTrace

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1_H3_R1_H2_R1.H1 := by
  intro m A e unionClosed quad noSingle rare
  exact FourTrace.multiplicity e A unionClosed quad noSingle rare
