import OMAReductions.R_UnionClosed_union_closed_R1_H3_R1
import Mathlib

/-!
Group the members by their complements outside a fixed triple. Each occupied
fiber induces a union-closed family on three coordinates containing the full
triple. Classify its signed incidence excess in the Lean kernel. Summing the
local inequalities over the fibers bounds the total number of incidences of
the three coordinates. Parity then gives the stated number of distinct
witnesses when all three coordinates are below half frequency.
-/

open Finset
namespace TripleTrace

abbrev Core := Finset (Fin 3)
abbrev Family := Finset Core

/-- All subtraces of a proper nonempty subset, together with the full triple. -/
def deficient (F : Family) : Prop :=
  ∃ T ∈ (univ : Finset Core), T.Nonempty ∧ T ≠ univ ∧ F = insert univ T.powerset

instance (F : Family) : Decidable (deficient F) := by unfold deficient; infer_instance

def closed (F : Family) : Prop := ∀ U ∈ F, ∀ V ∈ F, U ∪ V ∈ F

instance (F : Family) : Decidable (closed F) := by unfold closed; infer_instance

def mass (F : Family) : ℕ := ∑ R ∈ F, R.card

/- Exactly the proper one- and two-dimensional cubes with the full triple
adjoined have negative total excess, which is one unit in each such fiber. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem classify : ∀ F ∈ (univ : Finset Family), univ ∈ F → closed F →
    (if deficient F then 2 * mass F + 1 = 3 * F.card else 3 * F.card ≤ 2 * mass F) := by
  decide +kernel

end TripleTrace
namespace TripleTrace

open Finset

variable {α : Type*} [DecidableEq α]

def carrier (e : Fin 3 ↪ α) := (univ : Core).map e

def trace (e : Fin 3 ↪ α) (X : Finset α) : Core := univ.filter (fun i => e i ∈ X)

def outside (e : Fin 3 ↪ α) (X : Finset α) := X \ carrier e

def block (e : Fin 3 ↪ α) (A : Finset (Finset α)) (B : Finset α) :=
  A.filter (fun X => outside e X = B)

def traces (e : Fin 3 ↪ α) (A : Finset (Finset α)) (B : Finset α) : Family :=
  (block e A B).image (trace e)

theorem trace_union (e : Fin 3 ↪ α) (X Y : Finset α) :
    trace e (X ∪ Y) = trace e X ∪ trace e Y := by ext i; simp [trace]

theorem outside_union (e : Fin 3 ↪ α) (X Y : Finset α) :
    outside e (X ∪ Y) = outside e X ∪ outside e Y := by
  ext i
  simp only [outside,mem_sdiff,mem_union]
  tauto

theorem trace_carrier (e : Fin 3 ↪ α) : trace e (carrier e) = univ := by
  ext i
  simp [trace,carrier]

/-- The outside part and the trace recover the original member. -/
theorem reconstruct (e : Fin 3 ↪ α) (X : Finset α) :
    outside e X ∪ (trace e X).map e = X := by
  ext i
  by_cases hi : i ∈ carrier e
  · obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    simp [outside,trace,carrier]
  · have hn : ∀ j : Fin 3, e j ≠ i := by
      rintro j rfl
      exact hi (by simp [carrier])
    simp [outside,trace,hi,hn]

theorem trace_injOn (e : Fin 3 ↪ α) (A : Finset (Finset α)) (B : Finset α) :
    Set.InjOn (trace e) (block e A B : Set (Finset α)) := by
  intro X hX Y hY eq
  have hx := (mem_filter.mp hX).2
  have hy := (mem_filter.mp hY).2
  rw [← reconstruct e X,← reconstruct e Y,eq,hx,hy]

theorem counts (e : Fin 3 ↪ α) (A : Finset (Finset α)) (B : Finset α) :
    (traces e A B).card = (block e A B).card ∧
    mass (traces e A B) = ∑ X ∈ block e A B, (trace e X).card := by
  exact ⟨card_image_of_injOn (trace_injOn e A B),sum_image (trace_injOn e A B)⟩

theorem closed_traces (e : Fin 3 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (B : Finset α) : closed (traces e A B) := by
  intro U hU V hV
  obtain ⟨X,hX,rfl⟩ := mem_image.mp hU
  obtain ⟨Y,hY,rfl⟩ := mem_image.mp hV
  have hx := mem_filter.mp hX
  have hy := mem_filter.mp hY
  exact mem_image.mpr ⟨X∪Y,mem_filter.mpr ⟨hA X hx.1 Y hy.1,by simp [outside_union,hx.2,hy.2]⟩,
    trace_union e X Y⟩

/-- Union with the given triple fills its three coordinates in any occupied fiber. -/
theorem top_mem (e : Fin 3 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A)
    (B : Finset α) (hB : B ∈ A.image (outside e)) : univ ∈ traces e A B := by
  obtain ⟨X,hX,rfl⟩ := mem_image.mp hB
  refine mem_image.mpr ⟨X∪carrier e,mem_filter.mpr ⟨hA X hX _ hc,?_⟩,?_⟩
  · rw [outside_union]
    simp [outside]
  · simp [trace_union, trace_carrier]

theorem incidences (e : Fin 3 ↪ α) (A : Finset (Finset α)) :
    (∑ X ∈ A, (trace e X).card) =
      ∑ i : Fin 3, (A.filter (fun X => e i ∈ X)).card := by
  simp only [trace,card_filter]
  exact sum_comm

/-- Each deficient fiber can account for at most one unit of total incidence deficit. -/
theorem bound (e : Fin 3 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A) :
    3 * A.card ≤
      2 * (∑ i : Fin 3, (A.filter (fun X => e i ∈ X)).card) +
      ((A.image (outside e)).filter (fun B => deficient (traces e A B))).card := by
  let indices := A.image (outside e)
  have point (B : Finset α) (hB : B ∈ indices) :
      3 * (block e A B).card ≤
        2 * (∑ X ∈ block e A B, (trace e X).card) +
          (if deficient (traces e A B) then 1 else 0) := by
    obtain ⟨hc',hm⟩ := counts e A B
    have h := classify (traces e A B) (mem_univ _) (top_mem e A hA hc B hB)
      (closed_traces e A hA B)
    rw [← hc',← hm]
    split at h <;> simp_all
  have ht := sum_le_sum point
  have hcounts : ∑ B ∈ indices, (block e A B).card = A.card :=
    (card_eq_sum_card_fiberwise (f := outside e) (s := A) (t := indices)
      (fun X hX => mem_image_of_mem _ hX)).symm
  have hm : ∑ B ∈ indices, ∑ X ∈ block e A B, (trace e X).card =
      ∑ X ∈ A, (trace e X).card :=
    sum_fiberwise_of_maps_to (fun X hX => mem_image_of_mem (outside e) hX) _
  rw [← mul_sum, hcounts, sum_add_distrib, ← mul_sum, hm, incidences] at ht
  rw [← card_filter] at ht
  exact ht

end TripleTrace

namespace TripleTrace
open Finset
variable {α : Type*} [DecidableEq α]

theorem bad_index (e : Fin 3 ↪ α) (A : Finset (Finset α)) {B : Finset α}
    (h : deficient (traces e A B)) : B ∈ A ∧ Disjoint B (carrier e) := by
  obtain ⟨T,_,_,_,ht⟩ := h
  have emptyRow : (∅ : Core) ∈ traces e A B := by rw [ht]; simp
  obtain ⟨X,hX,htr⟩ := mem_image.mp emptyRow
  obtain ⟨hx,ho⟩ := mem_filter.mp hX
  have hxEq := reconstruct e X
  rw [ho,htr] at hxEq
  simp only [map_empty,union_empty] at hxEq
  refine ⟨hxEq.symm ▸ hx,?_⟩
  rw [← ho]
  exact sdiff_disjoint

theorem multiplicity (e : Fin 3 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A)
    (rare : ∀ i, 2 * (A.filter (fun X => e i ∈ X)).card < A.card) :
    (if A.card % 2 = 0 then 6 else 3) ≤
      (A.filter (fun B => Disjoint B (carrier e) ∧ deficient (traces e A B))).card := by
  have hs := bound e A hA hc
  rw [Fin.sum_univ_three] at hs
  have hsub : ((A.image (outside e)).filter (fun B => deficient (traces e A B))) ⊆
      A.filter (fun B => Disjoint B (carrier e) ∧ deficient (traces e A B)) := by
    intro B hB
    have d := (mem_filter.mp hB).2
    have b := bad_index e A d
    exact mem_filter.mpr ⟨b.1,b.2,d⟩
  have le := card_le_card hsub
  have r0 := rare 0
  have r1 := rare 1
  have r2 := rare 2
  split <;> omega

/-- Few disjoint members suffice to exhibit an abundant element of the given triple. -/
theorem abundant_of_few_disjoint (e : Fin 3 ↪ α) (A : Finset (Finset α))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) (hc : carrier e ∈ A)
    (few : (A.filter (fun B => Disjoint B (carrier e))).card <
      (if A.card % 2 = 0 then 6 else 3)) :
    ∃ i : Fin 3, A.card ≤ 2 * (A.filter (fun X => e i ∈ X)).card := by
  by_contra! rare
  have lower := multiplicity e A hA hc rare
  have sub : A.filter (fun B => Disjoint B (carrier e) ∧ deficient (traces e A B)) ⊆
      A.filter (fun B => Disjoint B (carrier e)) := by
    intro B hB
    obtain ⟨h₁, h₂, _⟩ := mem_filter.mp hB
    exact mem_filter.mpr ⟨h₁, h₂⟩
  exact (Nat.not_lt_of_ge (lower.trans (card_le_card sub))) few

end TripleTrace

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1_H3_R1.H1 := by
  intro m A e unionClosed triple rare
  exact TripleTrace.multiplicity e A unionClosed triple rare
