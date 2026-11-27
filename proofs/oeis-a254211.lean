import OMAStatements.S_oeis_a254211
import Mathlib.Tactic

open OMA.S_oeis_a254211

namespace CompositePaths

/-- Each recorded divisor is proper and divides the translation length 210. -/
private def safe (n : ℕ) : Prop :=
  (2 < n ∧ 2 ∣ n) ∨ (3 < n ∧ 3 ∣ n) ∨ (5 < n ∧ 5 ∣ n) ∨ (7 < n ∧ 7 ∣ n)

private instance decSafe (n : ℕ) : Decidable (safe n) := by unfold safe; infer_instance

private instance decSums (P : ℕ → Prop) [DecidablePred P] (b : ℕ) (xs : List ℕ) :
    Decidable (sumsSatisfy P b xs) :=
  match xs with
  | [] => isTrue trivial
  | d::ys => by
    letI := decSums P (b+d) ys
    exact inferInstanceAs (Decidable (P (b+d) ∧ sumsSatisfy P (b+d) ys))

private instance decSteps (b : ℕ) (xs : List ℕ) : Decidable (validSteps b xs) :=
  match xs with
  | [] => isTrue trivial
  | d::ys => by
    letI := decSteps d ys
    exact inferInstanceAs (Decidable (1 ≤ d ∧ d ≤ 3 ∧ d ≠ b ∧ validSteps d ys))

private lemma not_prime {n : ℕ} (h : safe n) : ¬n.Prime := by
  rcases h with ⟨h, hd⟩ | ⟨h, hd⟩ | ⟨h, hd⟩ | ⟨h, hd⟩
  all_goals exact Nat.not_prime_of_dvd_of_lt hd (by decide) h

private lemma safe_add {n : ℕ} (h : safe n) (j : ℕ) : safe (n+210*j) := by
  unfold safe at *
  omega

private lemma valid_after_translation {b : ℕ} {xs : List ℕ} (j : ℕ) (h : sumsSatisfy safe b xs) :
    sumsSatisfy (fun n => ¬n.Prime) (b+210*j) xs := by
  induction xs generalizing b with
  | nil => trivial
  | cons d xs ih =>
    change _ ∧ _
    have hs := safe_add h.1 j
    rw [show b+210*j+d = b+d+210*j by omega]
    exact ⟨not_prime hs, ih h.2⟩

private lemma sums_append (P : ℕ → Prop) (b : ℕ) (xs ys : List ℕ) :
    sumsSatisfy P b (xs++ys) ↔ sumsSatisfy P b xs ∧ sumsSatisfy P (b+xs.sum) ys := by
  induction xs generalizing b with
  | nil => simp [sumsSatisfy]
  | cons d xs ih => simp [sumsSatisfy, ih, Nat.add_assoc, and_assoc]

private def blocks (c : List ℕ) : ℕ → List ℕ
  | 0 => []
  | j+1 => c ++ blocks c j

private lemma blocks_snoc (c : List ℕ) (j : ℕ) : blocks c j ++ c = c ++ blocks c j := by
  induction j with
  | zero => simp [blocks]
  | succ j ih => simp only [blocks, List.append_assoc, ih]

private lemma reverse_blocks (c : List ℕ) (j : ℕ) : (blocks c j).reverse = blocks c.reverse j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [blocks, List.reverse_append, ih, blocks_snoc]; rfl

private lemma sum_blocks (c : List ℕ) (j : ℕ) : (blocks c j).sum = c.sum*j := by
  induction j with
  | zero => simp [blocks]
  | succ j ih => simp [blocks, ih, Nat.mul_succ, Nat.add_comm]

private lemma length_blocks (c : List ℕ) (j : ℕ) : (blocks c j).length = c.length*j := by
  induction j with
  | zero => simp [blocks]
  | succ j ih => simp [blocks, ih, Nat.mul_succ, Nat.add_comm]

private def forward : List ℕ := [3,1,2]
private def backward : List ℕ := [2,1,3]
private def initial : List ℕ := [1,3,2]

/-- A path from sum 6 to sum 120. Its large partial sums have proper divisors
among 2,3,5,7, and the suffix sums avoid primes as well. -/
private def tail : List ℕ := [
  3,1,2,3,1,2,3,1,2,1,2,3,2,1,2,1,2,1,3,2,1,3,2,1,3,2,1,3,2,
  1,2,1,2,1,3,2,1,3,2,1,3,2,1,3,2,1,2,1,2,1,3,2,1,3,2,1,3,2,3,1]

private lemma tail_sum : tail.sum = 114 := by decide

set_option maxRecDepth 2400 in
private lemma tail_safe : sumsSatisfy safe 6 tail := by decide

set_option maxRecDepth 2400 in
private lemma tail_reverse_ok : sumsSatisfy (fun n => ¬n.Prime) 0 tail.reverse := by decide

private lemma initial_ok : sumsSatisfy (fun n => ¬n.Prime) 0 initial := by decide

private lemma last_safe : sumsSatisfy safe 114 initial.reverse := by decide

set_option maxRecDepth 2400 in
private lemma steps_ok (j : ℕ) : validSteps 2 (blocks forward j ++ tail) := by
  induction j with
  | zero => decide
  | succ j ih => simpa [blocks, forward, validSteps] using ih

private lemma cycle_ok {c : List ℕ} (hc : c = forward ∨ c = backward) (m j : ℕ) (hm : 0 < m) :
    sumsSatisfy (fun n => ¬n.Prime) (6*m) (blocks c j) := by
  induction j generalizing m with
  | zero => trivial
  | succ j ih =>
    rw [blocks, sums_append]
    constructor
    · rcases hc with rfl | rfl
      all_goals
        simp only [forward, backward, sumsSatisfy, and_true]
        repeat' apply And.intro
        all_goals apply not_prime; unfold safe; omega
    · have hs : c.sum = 6 := by rcases hc with rfl | rfl <;> decide
      rw [hs, show 6*m+6 = 6*(m+1) by ring]
      exact ih (m+1) (by omega)

private def word (j : ℕ) := initial ++ (blocks forward (35*j) ++ tail)

private lemma word_ok (j : ℕ) : valid (word j) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [word, initial, validSteps] using steps_ok (35*j)
  · rw [word, sums_append]
    refine ⟨initial_ok, ?_⟩
    change sumsSatisfy _ 6 (blocks forward (35*j) ++ tail)
    rw [sums_append, sum_blocks]
    refine ⟨cycle_ok (Or.inl rfl) 1 (35*j) (by decide), ?_⟩
    have hs : forward.sum = 6 := rfl
    rw [hs, show 6+6*(35*j) = 6+210*j by ring]
    exact valid_after_translation j tail_safe
  · rw [word, List.reverse_append, List.reverse_append, reverse_blocks, List.append_assoc,
      sums_append, List.sum_reverse, tail_sum]
    refine ⟨tail_reverse_ok, ?_⟩
    change sumsSatisfy _ 114 (blocks backward (35*j) ++ initial.reverse)
    rw [sums_append, sum_blocks]
    refine ⟨cycle_ok (Or.inr rfl) 19 (35*j) (by decide), ?_⟩
    have hs : backward.sum = 6 := rfl
    rw [hs, show 114+6*(35*j) = 114+210*j by ring]
    exact valid_after_translation j last_safe

end CompositePaths

theorem OMA.solution : type_of% @OMA.S_oeis_a254211.main := by
  intro B
  refine ⟨CompositePaths.word (B+1), ?_, CompositePaths.word_ok _⟩
  simp only [CompositePaths.word, List.length_append, CompositePaths.length_blocks]
  have h : CompositePaths.forward.length = 3 := rfl
  rw [h]
  omega
