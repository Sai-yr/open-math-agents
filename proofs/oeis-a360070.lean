import OMAStatements.S_oeis_a360070
import Mathlib.Tactic

open OMA.S_oeis_a360070

namespace EqualPartitionMeans

/-- The number of positive parts is at most their sum, with equality only
when each part is 1. -/
private lemma card_le_sum_and_eq (s : Multiset ℕ) (hs : ∀ x ∈ s, 0 < x) :
    s.card ≤ s.sum ∧ (s.card = s.sum → ∀ x ∈ s, x = 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨hle, heq⟩ := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.card_cons, Multiset.sum_cons, Multiset.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro h x (rfl | hx)
    · omega
    · exact heq (by omega) x hx

end EqualPartitionMeans

open EqualPartitionMeans

theorem OMA.solution : type_of% @OMA.S_oeis_a360070.main := by
  rintro n hn ⟨P, hmeans⟩ hsf
  have hlen : 0 < P.parts.card := by
    apply Multiset.card_pos.mpr
    intro hzero
    have h := P.parts_sum
    simp [hzero] at h
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hlen
  have hdistinct : 0 < P.parts.toFinset.card :=
    Finset.card_pos.mpr ⟨a, Multiset.mem_toFinset.mpr ha⟩
  rw [SameMeans, P.parts_sum, P.parts.toFinset_sum_count_eq] at hmeans
  have cross : n * P.parts.toFinset.card = P.parts.card * P.parts.card := by
    exact_mod_cast (div_eq_div_iff (Nat.cast_ne_zero.mpr hlen.ne')
      (Nat.cast_ne_zero.mpr hdistinct.ne')).mp hmeans
  have hsq : n ∣ P.parts.card ^ 2 :=
    ⟨P.parts.toFinset.card, by simpa only [pow_two] using cross.symm⟩
  have hdiv : n ∣ P.parts.card := (hsf.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hsq
  obtain ⟨hle, honly⟩ := card_le_sum_and_eq P.parts fun _ hx => P.parts_pos hx
  have heq : P.parts.card = n := le_antisymm (hle.trans_eq P.parts_sum) (Nat.le_of_dvd hlen hdiv)
  have hsub : P.parts.toFinset ⊆ {1} := by
    intro x hx
    exact Finset.mem_singleton.mpr (honly (heq.trans P.parts_sum.symm) x (Multiset.mem_toFinset.mp hx))
  have hone : P.parts.toFinset.card ≤ 1 := by simpa using Finset.card_le_card hsub
  rw [heq] at cross
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) cross
  omega
