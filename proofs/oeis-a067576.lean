import OMAStatements.S_oeis_a067576

namespace OMA.S_oeis_a067576

private abbrev wt (x : ℕ) := x.bitIndices.length
private def ones : ℕ → ℕ
  | 0 => 0
  | k+1 => 2*ones k+1
private abbrev rank (i x : ℕ) := Nat.count (fun y => wt y=i) x

private theorem even_wt (x : ℕ) : wt (2*x)=wt x := by simp [wt]
private theorem odd_wt (x : ℕ) : wt (2*x+1)=wt x+1 := by simp [wt]
private theorem ones_wt (i : ℕ) : wt (ones i)=i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [ones,odd_wt,ih]

-- The smallest integer of weight i is the string of i ones.
private theorem below (i : ℕ) : ∀ x < ones i, wt x < i := by
  induction i with
  | zero => simp [ones]
  | succ i ih =>
    intro x hx
    rw [ones] at hx
    obtain ⟨m,he|he⟩ := x.even_or_odd'
    · subst x
      rw [even_wt]
      by_cases hm : m=ones i
      · rw [hm,ones_wt]
        omega
      · have := ih m (by omega)
        omega
    · subst x
      rw [odd_wt]
      have := ih m (by omega)
      omega

private theorem empty_rank (i x : ℕ) (hx : x ≤ ones i) : rank i x=0 := by
  rw [rank,Nat.count_eq_card_filter_range,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro y hy
  have hh := below i y (lt_of_lt_of_le (Finset.mem_range.mp hy) hx)
  omega

-- Separate the even and odd integers less than 2x by removing their
-- last bit. Adding a trailing one increases the weight by one.
private theorem pair_rank (i x : ℕ) : rank (i+1) (2*x)=rank (i+1) x+rank i x := by
  induction x with
  | zero => simp [rank]
  | succ x ih =>
    rw [show 2*(x+1)=2*x+1+1 by omega]
    simp only [rank,Nat.count_succ,even_wt,odd_wt,Nat.add_right_cancel_iff] at *
    omega

-- The first even number of weight i has exactly i predecessors in
-- its row. This is the last entry needed to start all column tails.
private theorem diag (i : ℕ) : rank i (2*ones i)=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pair_rank,empty_rank _ _ le_rfl,zero_add,ones]
    change Nat.count (fun x => wt x=i) (2*ones i+1)=i+1
    rw [Nat.count_succ,if_pos (by change wt (2*ones i)=i; rw [even_wt,ones_wt])]
    exact congrArg (·+1) ih

private theorem shifted (i x : ℕ) (hx : x < ones (i+1)) :
    rank (i+1) (2*x+1)=rank i x := by
  change Nat.count (fun y => wt y=i+1) (2*x+1)=_
  rw [Nat.count_succ,if_neg (by change wt (2*x)≠i+1; rw [even_wt]; exact (below _ _ hx).ne)]
  change rank (i+1) (2*x)+0=_
  rw [pair_rank,empty_rank _ _ hx.le,zero_add,add_zero]

private theorem available (j i : ℕ) (h : j ≤ i) :
    ∃ x ≤ 2*ones i, wt x=i ∧ rank i x=j := by
  induction i,h using Nat.le_induction with
  | base => exact ⟨2*ones j,le_rfl,(even_wt _).trans (ones_wt _),diag _⟩
  | succ i _ ih =>
    obtain ⟨x,hx,hw,hr⟩ := ih
    refine ⟨2*x+1,by rw [ones]; omega,(odd_wt x).trans (by rw [hw]),?_⟩
    exact (shifted i x (by rw [ones]; omega)).trans hr

private theorem at_rank {x i j : ℕ} (hw : wt x=i) (hr : rank i x=j) : entry i (j+1)=x := by
  unfold entry
  simp only [Nat.add_sub_cancel]
  rw [← hr]
  exact Nat.nth_count hw

private theorem double_entry {i j : ℕ} (h : j ≤ i) :
    entry (i+1) (j+1)+1=2*(entry i (j+1)+1) := by
  obtain ⟨x,hx,hw,hr⟩ := available j i h
  have hw' : wt (2*x+1)=i+1 := by rw [odd_wt,hw]
  have hr' : rank (i+1) (2*x+1)=j := (shifted i x (by rw [ones]; omega)).trans hr
  rw [at_rank hw hr,at_rank hw' hr']
  omega

end OMA.S_oeis_a067576

open OMA.S_oeis_a067576 in
theorem OMA.solution : type_of% @OMA.S_oeis_a067576.main := by
  intro j
  constructor
  · exact ⟨by omega,fun i hi => double_entry (by omega)⟩
  · rintro r ⟨hr,h⟩
    by_contra! hbad
    have hj : 0 < j := by omega
    have hstep := h (j-1) (by omega)
    rw [show j-1+1=j by omega,at_rank ((even_wt _).trans (ones_wt j)) (diag j)] at hstep
    omega
