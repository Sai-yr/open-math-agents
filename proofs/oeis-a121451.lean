import OMAStatements.S_oeis_a121451
import Mathlib.Tactic

open OMA.S_oeis_a121451

namespace RestrictedPartitionProducts

private def formula (n : ℕ) : ℕ :=
  if n = 1 ∨ n = 3 then 0 else
    if n % 2 = 0 then 2 ^ (n / 2) else 5 * 2 ^ ((n - 5) / 2)

/-- Replace each allowed part by twos and fives without reducing its product. -/
private lemma replace_part {x : ℕ} (hx : x % 3 = 2) :
    ∃ u v : ℕ, x = 2 * u + 5 * v ∧ x ≤ 2 ^ u * 5 ^ v := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' x
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨j + 1, 0, by omega, ?_⟩
    have h : j < 2 ^ j := Nat.lt_two_pow_self
    simp only [pow_zero, mul_one, pow_succ]
    omega
  · refine ⟨k - 2, 1, by omega, ?_⟩
    have h : k - 2 < 2 ^ (k - 2) := Nat.lt_two_pow_self
    simp only [pow_one]
    omega

private lemma replace_parts (s : Multiset ℕ) (hs : ∀ x ∈ s, x % 3 = 2) :
    ∃ u v : ℕ, s.sum = 2 * u + 5 * v ∧ s.prod ≤ 2 ^ u * 5 ^ v := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, 0, by simp, by simp⟩
  | cons x s ih =>
    obtain ⟨u, v, hxs, hxp⟩ := replace_part (hs x (Multiset.mem_cons_self x s))
    obtain ⟨w, z, hss, hsp⟩ := ih (fun a ha => hs a (Multiset.mem_cons_of_mem ha))
    refine ⟨u + w, v + z, ?_, ?_⟩
    · simp only [Multiset.sum_cons, hxs, hss]
      omega
    · simpa only [Multiset.prod_cons, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using Nat.mul_le_mul hxp hsp

private lemma canonical (u r : ℕ) (hr : r ≤ 1) :
    formula (2 * u + 5 * r) = 2 ^ u * 5 ^ r := by
  interval_cases r
  · simp [formula, show 2 * u ≠ 1 by omega, show 2 * u ≠ 3 by omega]
  · simp [formula, Nat.mul_comm]

/-- Every pair of fives can be traded for five twos, which have product 32. -/
private lemma pairs_of_fives (u v : ℕ) : 2 ^ u * 5 ^ v ≤ formula (2 * u + 5 * v) := by
  let k := v / 2
  let r := v % 2
  have hv : v = 2 * k + r := by dsimp [k, r]; omega
  have hs : 2 * u + 5 * v = 2 * (u + 5 * k) + 5 * r := by omega
  rw [hs, canonical _ _ (by dsimp [r]; omega)]
  calc
    2 ^ u * 5 ^ v = 2 ^ u * ((5 ^ 2) ^ k * 5 ^ r) := by conv_lhs => rw [hv, pow_add, pow_mul]
    _ ≤ 2 ^ u * ((2 ^ 5) ^ k * 5 ^ r) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) k))
    _ = 2 ^ (u + 5 * k) * 5 ^ r := by rw [pow_add, pow_mul]; ring

private lemma upper (n : ℕ) : a n ≤ formula n := by
  apply Finset.sup_le
  intro P _
  split_ifs with hp
  · obtain ⟨u, v, hs, hb⟩ := replace_parts P.parts hp
    exact (hb.trans (pairs_of_fives u v)).trans_eq (congrArg formula (hs.symm.trans P.parts_sum))
  · exact Nat.zero_le _

private lemma witness (u v : ℕ) : 2 ^ u * 5 ^ v ≤ a (2 * u + 5 * v) := by
  let s := Multiset.replicate u 2 + Multiset.replicate v 5
  have parts {x : ℕ} (hx : x ∈ s) : x = 2 ∨ x = 5 :=
    (Multiset.mem_add.mp hx).imp Multiset.eq_of_mem_replicate Multiset.eq_of_mem_replicate
  let P : (2 * u + 5 * v).Partition := {
    parts := s
    parts_pos := fun hx => by rcases parts hx with rfl | rfl <;> decide
    parts_sum := by simp [s, Nat.mul_comm] }
  have hp : ∀ x ∈ P.parts, x % 3 = 2 := by
    intro x hx
    rcases parts hx with rfl | rfl <;> decide
  have h := Finset.le_sup (f := fun Q : (2 * u + 5 * v).Partition =>
    if ∀ x ∈ Q.parts, x % 3 = 2 then Q.parts.prod else 0) (Finset.mem_univ P)
  rw [if_pos hp] at h
  simpa [P, s, a] using h

end RestrictedPartitionProducts

open RestrictedPartitionProducts

theorem OMA.solution : type_of% @OMA.S_oeis_a121451.main := by
  intro n _
  change a n = formula n
  refine le_antisymm (upper n) ?_
  by_cases he : n = 1 ∨ n = 3
  · simp [formula, he]
  obtain ⟨k, heven | hodd⟩ := Nat.even_or_odd' n
  · rw [show n = 2 * k + 5 * 0 by omega, canonical _ _ (by decide)]
    exact witness _ _
  · rw [show n = 2 * (k - 2) + 5 * 1 by omega, canonical _ _ (by decide)]
    exact witness _ _
