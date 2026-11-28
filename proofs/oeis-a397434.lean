import OMAStatements.S_oeis_a397434

/-!
# When two consecutive majorities have equally many monomials

Pair subsets that differ by one distinguished variable. Contributions
from such pairs have even sum except at the threshold boundary.
The coefficient of degree d+1 for threshold k+1 is thus C(d,k) mod 2.
Pascal's identity lets us compare successive rows term by term; an odd
threshold enforces inclusion of the relevant degree supports, and an even
threshold supplies an explicit strictly increasing degree.
-/

namespace A397434Proof
open Finset OMA.S_oeis_a397434

private def bit (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => d.choose k % 2

private theorem degrees {α : Type*} (k : ℕ) (s : Finset α) :
    coefficient (k+1) s = bit k s.card := by
  classical
  induction s using Finset.induction with
  | empty => simp only [coefficient,powerset_empty,sum_singleton,card_empty,Nat.not_add_one_le_zero,if_false,bit,Nat.zero_mod]
  | insert x s hx _ =>
    unfold coefficient
    rw [sum_powerset_insert hx,card_insert_of_notMem hx]
    have hextra : (∑ u ∈ s.powerset, if k+1 ≤ (insert x u).card then (1:ℕ) else 0) =
        (∑ u ∈ s.powerset, if k+1 ≤ u.card then (1:ℕ) else 0) + s.card.choose k := by
      have hg : (∑ u ∈ s.powerset, if u.card=k then (1:ℕ) else 0) = s.card.choose k := by
        rw [sum_boole,←powersetCard_eq_filter,card_powersetCard]
        rfl
      rw [←hg,←sum_add_distrib]
      apply sum_congr rfl; intro u hu
      rw [card_insert_of_notMem (notMem_mono (mem_powerset.mp hu) hx)]
      split_ifs <;> omega
    rw [hextra,bit]
    omega

private def table (n k : ℕ) := ∑ d ∈ range (n+1), n.choose d * bit k d

private theorem table_eq (n k : ℕ) (ht : (n+1)/2=k+1) : monomials n = table n k := by
  unfold monomials
  rw [ht]
  simp_rw [degrees]
  rw [sum_powerset]
  simp_rw [sum_powersetCard]
  simp [table]

end A397434Proof

namespace A397434Proof
open Finset OMA.S_oeis_a397434

private theorem next_row (n k : ℕ) : table (n+1) k =
    ∑ d ∈ range (n+1), n.choose d*(bit k d+bit k (d+1)) := by
  let f := fun d => n.choose d * bit k d
  have e1 := sum_range_succ' f (n+1)
  have e2 := sum_range_succ f (n+1)
  have shift : (∑ d ∈ range (n+1), n.choose (d+1)*bit k (d+1)) =
      ∑ d ∈ range (n+1), n.choose d*bit k d := by
    simpa [f,bit] using e1.symm.trans e2
  unfold table
  rw [sum_range_succ']
  simp only [show bit k 0=0 by rfl, mul_zero,add_zero]
  simp_rw [Nat.choose_succ_succ,add_mul,mul_add]
  rw [sum_add_distrib,sum_add_distrib,shift,add_comm]

private theorem table_increases (n k : ℕ) (hk : k ≤ n) : table n k < table (n+1) k := by
  rw [next_row,table]
  apply sum_lt_sum
  · intro d _; gcongr; omega
  · refine ⟨k,mem_range.mpr (by omega),?_⟩
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.choose_pos hk)
    simp [bit]

private theorem bit_step (k d : ℕ) :
    bit (k+1) (d+1) = (bit (k+1) d+bit k d)%2 := by
  cases d with
  | zero => simp [bit]
  | succ d =>
    simp only [bit,Nat.choose_succ_succ,Nat.add_mod_mod,Nat.mod_add_mod]
    rw [Nat.add_comm]

private theorem bit_less (k d : ℕ) :
    bit k d ≤ bit (k+1) d+bit (k+1) (d+1) := by
  rw [bit_step]
  have h1 : bit k d < 2 := by cases d <;> simp [bit,Nat.mod_lt _ (by decide : 0<2)]
  omega

private theorem bit_same (k d : ℕ) (hk : (k+1)%2=1) :
    bit k d = bit (k+1) d+bit (k+1) (d+1) := by
  rw [bit_step]
  cases d with
  | zero => simp [bit]
  | succ d =>
    have h := congrArg (· % 2) (Nat.choose_succ_right_eq d k)
    rw [Nat.mul_mod (d.choose (k+1)) (k+1),hk,mul_one,Nat.mod_mod,
      Nat.mul_mod (d.choose k) (d-k)] at h
    simp only [bit]
    by_cases hh : d.choose k % 2=0
    · simp [hh] at h ⊢; omega
    · omega

private theorem table_tie (k : ℕ) (hk : (k+1)%2=1) : table (2*(k+1)) k=table (2*(k+1)+1) (k+1) := by
  rw [next_row,table]
  exact sum_congr rfl (fun d _=>congrArg _ (bit_same k d hk))

private theorem table_strict (k : ℕ) (hk : (k+1)%2=0) : table (2*(k+1)) k < table (2*(k+1)+1) (k+1) := by
  rw [next_row,table]
  apply sum_lt_sum
  · intro d _; exact Nat.mul_le_mul_left _ (bit_less k d)
  · refine ⟨k+2,mem_range.mpr (by omega),?_⟩
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.choose_pos (by omega))
    have hc : (k+1).choose k = k+1 := Nat.choose_succ_self_right k
    change (k+1).choose k % 2 < (k+1).choose (k+1)%2 + (k+2).choose (k+1)%2
    rw [hc,hk,Nat.choose_self]; omega

private theorem solved : ∀ n : ℕ, 1 ≤ n → (monomials n = monomials (n+1) ↔ n % 4 = 2) := by
  intro n hn
  by_cases h : n%2=1
  · obtain ⟨k,rfl⟩ : ∃ k,n=2*k+1 := ⟨n/2,by omega⟩
    rw [table_eq _ k (by omega),table_eq _ k (by omega)]
    have ht := table_increases (2*k+1) k (by omega)
    exact ⟨fun e=>False.elim (ht.ne e),fun e=>by omega⟩
  · obtain ⟨k,rfl⟩ : ∃ k,n=2*(k+1) := ⟨n/2-1,by omega⟩
    rw [table_eq _ k (by omega),table_eq _ (k+1) (by omega)]
    by_cases ho : (k+1)%2=1
    · exact ⟨fun _=>by omega,fun _=>table_tie k ho⟩
    · have ht := table_strict k (by omega)
      exact ⟨fun e=>False.elim (ht.ne e),fun e=>by omega⟩

end A397434Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a397434.main :=
  A397434Proof.solved
