import OMAStatements.S_oeis_a209861

namespace OMA.S_oeis_a209861

private def chunk (b : Bool) : List Bool := if b then [false] else [false,true]
private def suffixCode (w : List Bool) := w.flatMap chunk ++ [false]
private def flip (w : List Bool) := w.map Bool.not

-- Every one bit prepends one bit to the header, and every bit appends
-- its prescribed chunk at the other end. The chunks keep input order.
private theorem folded (w s : List Bool) : w.foldl putBit s =
    List.replicate (w.count true) true ++ (s ++ w.flatMap chunk) := by
  induction w generalizing s with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp [ih,putBit,chunk,List.append_assoc]
    · simp [ih,putBit,chunk,List.replicate_succ',List.append_assoc]

private theorem shape (w : List Bool) : treeCode w =
    true::(List.replicate (w.count true) true ++ suffixCode w) := by
  simp [treeCode,suffixCode,folded,List.append_assoc]

private theorem front (w : List Bool) : ∃ z, suffixCode w=false::z := by
  cases w with
  | nil => exact ⟨[],rfl⟩
  | cons b w => cases b <;> exact ⟨_,rfl⟩

private theorem suffix_order (u v : List Bool) (hl : u.length=v.length) :
    suffixCode u < suffixCode v ↔ v < u := by
  induction u generalizing v with
  | nil => have hv : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm); simp [hv]
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      have h := ih v (by simpa using hl)
      cases a <;> cases b
      · change (false::true::suffixCode u < false::true::suffixCode v) ↔
          (false::v < false::u)
        simpa using h
      · obtain ⟨t,he⟩ := front v
        change (false::true::suffixCode u < false::suffixCode v) ↔ (true::v < false::u)
        rw [he]
        simp [List.cons_lt_cons_iff]
      · obtain ⟨t,he⟩ := front u
        change (false::suffixCode u < false::true::suffixCode v) ↔ (false::v < true::u)
        rw [he]
        simp [List.cons_lt_cons_iff]
      · change (false::suffixCode u < false::suffixCode v) ↔ (true::v < true::u)
        simpa using h

private theorem header_order (a b : ℕ) (s t : List Bool) :
    (List.replicate a true ++ false::s < List.replicate b true ++ false::t) ↔
      a<b ∨ (a=b ∧ s<t) := by
  induction a generalizing b with
  | zero =>
    cases b <;> simp [List.replicate_succ,List.cons_lt_cons_iff]
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ,List.cons_lt_cons_iff]
    | succ b => simpa [List.replicate_succ] using ih b

private theorem compare_codes (u v : List Bool) (hl : u.length=v.length) :
    treeCode u < treeCode v ↔ u.count true < v.count true ∨
      (u.count true=v.count true ∧ v<u) := by
  obtain ⟨s,hs⟩ := front u
  obtain ⟨t,ht⟩ := front v
  have h := suffix_order u v hl
  rw [hs,ht,List.cons_lt_cons_self] at h
  rw [shape,shape,hs,ht,List.cons_lt_cons_self,header_order,h]

private theorem flip_weight (w : List Bool) : (flip w).count true+w.count true=w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [flip] at * <;> omega

private theorem flip_order (u v : List Bool) (hl : u.length=v.length) : flip u < flip v ↔ v<u := by
  induction u generalizing v with
  | nil => have hv : v=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm); simp [hv]
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      have h := ih v (by simpa using hl)
      cases a <;> cases b <;> simp [flip,List.cons_lt_cons_iff] at * <;> tauto

private theorem reverses (u v : List Bool) (hl : u.length=v.length) :
    treeCode (flip u) < treeCode (flip v) ↔ treeCode v < treeCode u := by
  rw [compare_codes _ _ (by simpa [flip] using hl),compare_codes _ _ hl.symm,flip_order _ _ hl.symm]
  have hu := flip_weight u
  have hv := flip_weight v
  constructor <;> rintro (h | ⟨h,hw⟩)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega,hw⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega,hw⟩

private theorem code_inj {u v : List Bool} (hl : u.length=v.length) (hc : treeCode u=treeCode v) : u=v := by
  have h₁ : ¬ treeCode u < treeCode v := by rw [hc]; exact lt_irrefl _
  have h₂ : ¬ treeCode v < treeCode u := by rw [hc]; exact lt_irrefl _
  rw [compare_codes _ _ hl] at h₁
  rw [compare_codes _ _ hl.symm] at h₂
  by_contra he
  have hw₁ : u.count true ≤ v.count true := le_of_not_gt (fun h => h₂ (Or.inl h))
  have hw₂ : v.count true ≤ u.count true := le_of_not_gt (fun h => h₁ (Or.inl h))
  have hew := hw₁.antisymm hw₂
  rcases lt_or_gt_of_ne he with h | h
  · exact h₂ (Or.inr ⟨hew.symm,h⟩)
  · exact h₁ (Or.inr ⟨hew,h⟩)

private def negBits {k : ℕ} (f : Fin k → Bool) := fun i => !(f i)

private theorem ofFn_neg {k : ℕ} (f : Fin k → Bool) : List.ofFn (negBits f)=flip (List.ofFn f) := by
  rw [flip,List.map_ofFn]
  rfl

private theorem rank_pair {k : ℕ} (f : Fin k → Bool) : rowRank f + rowRank (negBits f) = 2^k-1 := by
  classical
  let C (u : Fin k → Bool) := treeCode (List.ofFn u)
  let above := Finset.univ.filter (fun u => C f < C u)
  let below := Finset.univ.filter (fun u => C u < C f)
  have flip2 (u : Fin k → Bool) : negBits (negBits u)=u := by funext i; simp [negBits]
  have equiv (u v : Fin k → Bool) : C (negBits u) < C (negBits v) ↔ C v < C u := by
    simp only [C,ofFn_neg]
    exact reverses _ _ (by simp)
  have hg : rowRank (negBits f)=above.card := by
    unfold rowRank
    apply Finset.card_bij (fun u _ => negBits u)
    · intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(equiv (negBits u) f).mp (by simpa [flip2] using hu)⟩
    · intro u _ v _ h
      simpa [flip2] using congrArg negBits h
    · intro u hu
      refine ⟨negBits u,?_,flip2 u⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(equiv u f).mpr (Finset.mem_filter.mp hu).2⟩
  have hd : Disjoint below above := Finset.disjoint_left.mpr (fun _ h1 h2 =>
    ((Finset.mem_filter.mp h1).2).asymm (Finset.mem_filter.mp h2).2)
  have hu : below ∪ above = Finset.univ.erase f := by
    ext u
    simp only [below,above,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_erase,and_true]
    constructor
    · rintro (h|h) rfl <;> exact (lt_irrefl _) h
    · intro h
      apply lt_or_gt_of_ne
      intro he
      apply h
      exact List.ofFn_injective (code_inj (by simp) he)
  change below.card+rowRank (negBits f)=_
  rw [hg,← Finset.card_union_of_disjoint hd,hu,Finset.card_erase_of_mem (Finset.mem_univ f)]
  simp

end OMA.S_oeis_a209861

open OMA.S_oeis_a209861 in
theorem OMA.solution : type_of% @OMA.S_oeis_a209861.main := by
  intro k x
  have hf : bits (reversed x)=negBits (bits x) := by
    funext i
    simp [bits,reversed,negBits,Nat.testBit_two_pow_sub_succ x.isLt,i.isLt]
  unfold output
  rw [hf,pow_succ]
  have hr := rank_pair (bits x)
  have hp : 0 < 2^k := by positivity
  omega
