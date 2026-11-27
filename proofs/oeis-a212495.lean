import OMAStatements.S_oeis_a212495
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open OMA.S_oeis_a212495

namespace BaseElevenCounts

private instance decEvenDigits : DecidablePred evenDigits := fun n =>
  inferInstanceAs (Decidable (∀ d ∈ Nat.digits 11 n, Even d))
private instance decOddDigits : DecidablePred oddDigits := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ ∀ d ∈ Nat.digits 11 n, Odd d))

private lemma even_last (q r : ℕ) (h : r < 11) :
    evenDigits (11*q+r) ↔ evenDigits q ∧ Even r := by
  by_cases hz : r = 0 ∧ q = 0
  · rcases hz with ⟨rfl, rfl⟩
    simp [evenDigits]
  · have hne : r ≠ 0 ∨ q ≠ 0 := by omega
    rw [Nat.add_comm (11*q) r]
    simp [evenDigits, Nat.digits_add 11 (by decide) r q h hne, and_comm]

private lemma odd_last (q r : ℕ) (h : r < 11) :
    oddDigits (11*q+r) ↔ (q = 0 ∨ oddDigits q) ∧ Odd r := by
  by_cases hz : r = 0 ∧ q = 0
  · rcases hz with ⟨rfl, rfl⟩
    simp [oddDigits]
  · have hne : r ≠ 0 ∨ q ≠ 0 := by omega
    have hpos : 0 < r+11*q := by omega
    rw [Nat.add_comm (11*q) r]
    rw [oddDigits, Nat.digits_add 11 (by decide) r q h hne]
    simp only [hpos, true_and, List.forall_mem_cons]
    by_cases hq : q = 0
    · subst q
      simp [oddDigits]
    · simp [hq, oddDigits, Nat.pos_of_ne_zero hq, and_comm]

private lemma same_count {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] (N : ℕ)
    (h : ∀ r < N, P r ↔ Q r) : Nat.count P N = Nat.count Q N := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun _ hr => h _ (Finset.mem_range.mp hr))

private lemma even_block (q : ℕ) :
    Nat.count (fun r => evenDigits (11*q+r)) 11 = if evenDigits q then 6 else 0 := by
  by_cases hq : evenDigits q
  · rw [if_pos hq]
    exact (same_count (Q := Even) 11 (fun r hr => by simp [even_last q r hr, hq])).trans (by decide)
  · rw [if_neg hq]
    exact (same_count (Q := fun _ => False) 11 (fun r hr => by simp [even_last q r hr, hq])).trans
      (by decide)

private lemma odd_block (q : ℕ) :
    Nat.count (fun r => oddDigits (11*q+r)) 11 = if q = 0 ∨ oddDigits q then 5 else 0 := by
  by_cases hq : q = 0 ∨ oddDigits q
  · rw [if_pos hq]
    exact (same_count (Q := Odd) 11 (fun r hr => by simp [odd_last q r hr, hq])).trans (by decide)
  · rw [if_neg hq]
    exact (same_count (Q := fun _ => False) 11 (fun r hr => by simp [odd_last q r hr, hq])).trans
      (by decide)

private lemma even_scale (q : ℕ) : Nat.count evenDigits (11*q) = 6*Nat.count evenDigits q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Nat.count_add, even_block, ih, Nat.count_succ]
    by_cases h : evenDigits q <;> simp [h, Nat.mul_add]

private lemma odd_scale (q : ℕ) :
    Nat.count oddDigits (11*q) = 5*Nat.count oddDigits q + if q = 0 then 0 else 5 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Nat.count_add, odd_block, ih, Nat.count_succ]
    by_cases hz : q = 0
    · subst q
      simp [oddDigits]
    · by_cases h : oddDigits q <;> simp [hz, h, Nat.mul_add, Nat.add_assoc]

private lemma even_count (d : ℕ) : Nat.count evenDigits (11^d) = 6^d := by
  induction d with
  | zero => decide
  | succ d ih => rw [pow_succ', even_scale, ih, pow_succ']

private lemma odd_count (d : ℕ) : 4*Nat.count oddDigits (11^d)+5 = 5^(d+1) := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [pow_succ' 11 d, odd_scale, if_neg (by positivity), pow_succ 5 (d+1), ← ih]
    ring

private lemma odd_infinite : (Set.ofPred oddDigits).Infinite := by
  intro hf
  let c := hf.toFinset.card
  have hbound : Nat.count oddDigits (11^(4*c+6)) ≤ c := Nat.count_le_card hf _
  have heq := odd_count (4*c+6)
  have hlow : 4*c+7 < 5^(4*c+7) := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_left (by decide : 2 ≤ 5) _)
  have hbad : 4*c+7 < 4*c+5 := hlow.trans_le (heq.symm.le.trans (by omega))
  omega

private lemma power_comparison {d : ℕ} (hd : 11 ≤ d) : 5^(d+2) ≤ 4*6^d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d h ih =>
    rw [pow_succ 5 (d+2), pow_succ 6 d]
    omega

private lemma eventual {i : ℕ} (hi : 6^11 ≤ i) : Nat.nth evenDigits i < Nat.nth oddDigits i := by
  let d := Nat.log 6 i
  have hd : 11 ≤ d := Nat.le_log_of_pow_le (by decide) hi
  have hlo : 6^d ≤ i := Nat.pow_log_le_self _ (by omega)
  have hhi : i < 6^(d+1) := Nat.lt_pow_succ_log_self (by decide) i
  have hleft : Nat.nth evenDigits i < 11^(d+1) :=
    Nat.nth_lt_of_lt_count (by rw [even_count]; exact hhi)
  have hco := odd_count (d+1)
  have hcomp := power_comparison hd
  have hc : 4*Nat.count oddDigits (11^(d+1))+5 ≤ 4*i :=
    hco.le.trans (hcomp.trans (Nat.mul_le_mul_left 4 hlo))
  have hright : Nat.count oddDigits (11^(d+1)) ≤ i := by omega
  exact hleft.trans_le ((Nat.le_nth_count odd_infinite _).trans ((Nat.nth_monotone odd_infinite) hright))

end BaseElevenCounts

theorem OMA.solution : type_of% @OMA.S_oeis_a212495.main := by
  apply (Set.finite_Iio (6^11 : ℕ)).subset
  intro i hi
  change Nat.nth oddDigits i < Nat.nth evenDigits i at hi
  change i < 6^11
  by_contra! h
  exact (BaseElevenCounts.eventual h).not_gt hi
