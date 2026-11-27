import OMAStatements.S_oeis_a318698
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

open Finset OMA.S_oeis_a318698

namespace SharedDigitGreedy

private def universal (v : ℕ) := ∀ d < 10, d ∈ digits v

private lemma suffix (p : ℕ) : ∃ q : ℕ, 0 < q ∧ q%2 = p%2 ∧
    (Nat.digits 10 q).length = 11 ∧ ∀ d < 10, d ∈ Nat.digits 10 q := by
  by_cases h : p%2 = 0
  · refine ⟨12345678900, by decide, by omega, by decide, ?_⟩
    intro d hd
    interval_cases d <;> decide
  · refine ⟨12345678901, by decide, by omega, by decide, ?_⟩
    intro d hd
    interval_cases d <;> decide

private lemma universal_above (p M : ℕ) : ∃ u > M, u%2 = p%2 ∧ universal u := by
  obtain ⟨q,hq,hp,hlen,hall⟩ := suffix p
  let u := q+10^11*(M+1)
  have hu : M < u := by dsimp [u]; omega
  refine ⟨u,hu,by dsimp [u]; omega,?_⟩
  intro d hd
  rw [digits, if_neg (by omega : u ≠ 0)]
  have hx := Nat.digits_append_digits (b := 10) (m := M+1) (n := q) (by decide)
  rw [hlen] at hx
  change d ∈ Nat.digits 10 (q+10^11*(M+1))
  exact hx ▸ List.mem_append_left _ (hall d hd)

private lemma shares_universal (n : ℕ) {u : ℕ} (hu : universal u) : shares n u := by
  by_cases h : n=0
  · exact ⟨0,by simp [digits,h],hu 0 (by decide)⟩
  · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (Nat.digits_ne_nil_iff_ne_zero.mpr h :
      Nat.digits 10 n ≠ [])
    exact ⟨d,by simpa [digits,h] using hd,hu d (Nat.digits_lt_base (by decide) hd)⟩

private lemma available (seen : Finset ℕ) (v p : ℕ) : ∃ x, eligible seen v p x := by
  obtain ⟨u,hu,hp,hall⟩ := universal_above p (seen.sup id)
  exact ⟨u,fun he => (hu.not_ge (Finset.le_sup (f := id) he)),hp,shares_universal v hall⟩

private lemma next_eligible (seen : Finset ℕ) (v p : ℕ) :
    eligible seen v p (next seen v p) := by
  classical
  simpa [next, dif_pos (available seen v p)] using Nat.find_spec (available seen v p)

private lemma next_le {seen : Finset ℕ} {v p x : ℕ} (h : eligible seen v p x) :
    next seen v p ≤ x := by
  classical
  simpa [next, dif_pos (available seen v p)] using Nat.find_min' (available seen v p) h

private lemma history (s n : ℕ) : (state s n).2 = (range (n+1)).image (a s) := by
  induction n with
  | zero => simp [state,range_add_one,a]
  | succ n ih =>
    rw [range_add_one, image_insert, ← ih]
    rfl

private lemma advance (s n : ℕ) :
    a s (n+1) = next (state s n).2 (a s n) (n+1+s) := rfl

private theorem permutation (s : ℕ) : Function.Bijective (a s) := by
  have fresh (n : ℕ) : a s (n+1) ∉ (range (n+1)).image (a s) := by
    rw [← history, advance]
    exact (next_eligible ..).1
  have neq (i j : ℕ) (hij : i < j) : a s i ≠ a s j := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    intro he
    exact fresh n (mem_image.mpr ⟨i,mem_range.mpr hij,he⟩)
  have inj : Function.Injective (a s) := by
    intro i j h
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact (neq i j hlt h).elim
    · exact heq
    · exact (neq j i hgt h.symm).elim
  have parity (n : ℕ) : a s n %2 = (n+s)%2 := by
    cases n with
    | zero => simp [a,state]
    | succ n => rw [advance]; exact (next_eligible ..).2.1
  have escapes (B : ℕ) : ∃ N, ∀ j ≥ N, B < a s j := by
    have hf : ((a s) ⁻¹' Set.Iic B).Finite := (Set.finite_Iic B).preimage inj.injOn
    obtain ⟨M,hM⟩ := hf.bddAbove
    refine ⟨M+1,?_⟩
    intro j hj
    by_contra! h
    have := hM (show j ∈ (a s) ⁻¹' Set.Iic B from h)
    omega
  have unused {m : ℕ} (h : m ∉ Set.range (a s)) (i : ℕ) : m ∉ (state s i).2 := by
    rw [history]
    rintro hm
    obtain ⟨j,_,hj⟩ := mem_image.mp hm
    exact h ⟨j,hj⟩
  have appears {u : ℕ} (hU : universal u) : u ∈ Set.range (a s) := by
    by_contra h
    obtain ⟨N,hN⟩ := escapes u
    let i := 2*N+u+s+1
    have he : eligible (state s i).2 (a s i) (i+1+s) u :=
      ⟨unused h i,by dsimp [i]; omega,shares_universal _ hU⟩
    have hle := next_le he
    rw [← advance] at hle
    exact (hN (i+1) (by dsimp [i]; omega)).not_ge hle
  refine ⟨inj,?_⟩
  intro m
  change m ∈ Set.range (a s)
  by_contra h
  obtain ⟨N,hN⟩ := escapes m
  obtain ⟨u,hu,hp,hU⟩ := universal_above (m+1) ((state s N).2.sup id)
  obtain ⟨i,hi⟩ := appears hU
  have hNi : N < i := by
    by_contra! hle
    have mem : u ∈ (state s N).2 := by
      rw [history]
      exact mem_image.mpr ⟨i,mem_range.mpr (by omega),hi⟩
    exact hu.not_ge (le_sup (f := id) mem)
  have hip := parity i
  have shared := shares_universal m hU
  obtain ⟨d,hm,hu'⟩ := shared
  have he : eligible (state s i).2 (a s i) (i+1+s) m :=
    ⟨unused h i,by omega,⟨d,hi ▸ hu',hm⟩⟩
  have hle := next_le he
  rw [← advance] at hle
  exact (hN (i+1) (by omega)).not_ge hle

end SharedDigitGreedy

theorem OMA.solution : type_of% @OMA.S_oeis_a318698.main :=
  ⟨SharedDigitGreedy.permutation 0, SharedDigitGreedy.permutation 1⟩
