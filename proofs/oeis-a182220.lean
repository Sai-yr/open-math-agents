import OMAStatements.S_oeis_a182220
/-!
# Extremal extensional digraphs

Every out-neighborhood is a subset of the nonsources, so extensionality
bounds the number of vertices by two raised to the number of nonsources.
For sharpness, direct an edge from i to each position set in the binary
expansion of i. The exact tree-height interval follows by constructing
a tree of every admissible size at each height.
-/
namespace A182220Proof
open OMA.S_oeis_a182220 Finset
open scoped Classical

private theorem width_le (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem width_eq (n : ℕ) (hn : n≠0) : n.size = n.log2+1 := by
  have hi : n.size ≤ n.log2+1 := Nat.size_le.mpr ((Nat.log2_lt hn).mp (by omega))
  have lo : n.log2 < n.size := Nat.lt_size.mpr ((Nat.le_log2 hn).mp le_rfl)
  omega

private theorem closed_form (n : ℕ) :
    n+1-n.size = if n=0 then 1 else n-n.log2 := by
  split_ifs with hn
  · subst n; rfl
  · rw [width_eq n hn]; omega

private theorem bound (n : ℕ) (D : OMA.S_oeis_a182220.Digraph (n+1)) (hd : Function.Injective D) :
    sourceCount D ≤ n+1-n.size := by
  classical
  let T := univ.biUnion D
  have sub : univ.image D ⊆ T.powerset := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact mem_powerset.mpr (fun x hx => mem_biUnion.mpr ⟨i,mem_univ _,hx⟩)
  have count := card_le_card sub
  rw [card_image_of_injective _ hd,card_univ,Fintype.card_fin,card_powerset] at count
  have hw : n.size ≤ T.card := Nat.size_le.mpr (by omega)
  have sub' : T ⊆ univ := subset_univ _
  unfold sourceCount
  change (univ \ T).card ≤ _
  rw [card_sdiff_of_subset sub',card_univ,Fintype.card_fin]
  omega

private def bitGraph (n : ℕ) : OMA.S_oeis_a182220.Digraph (n+1) := fun i=>univ.filter (fun j=>i.val.testBit j.val)

private theorem bit_le {i j : ℕ} (h : i.testBit j=true) : 2^j ≤ i := by
  by_contra! hlt
  rw [Nat.testBit_lt_two_pow hlt] at h
  contradiction

private theorem bit_injective (n : ℕ) : Function.Injective (bitGraph n) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<n+1
  · let j : Fin (n+1) := ⟨k,hk⟩
    have hh : j∈bitGraph n x ↔ j∈bitGraph n y := by rw [h]
    simpa [bitGraph,j] using hh
  · have hk' : k<2^k := Nat.lt_two_pow_self
    rw [Nat.testBit_lt_two_pow (x:=x.val) (i:=k) (by have := x.isLt; omega),
      Nat.testBit_lt_two_pow (x:=y.val) (i:=k) (by have := y.isLt; omega)]

private theorem bit_acyclic (n : ℕ) : acyclic (bitGraph n) := by
  have edge {i j : Fin (n+1)} (h : j∈bitGraph n i) : j.val < i.val := by
    have ht := bit_le (mem_filter.mp h).2
    have := Nat.lt_two_pow_self (n:=j.val)
    omega
  have path {i j : Fin (n+1)} (h : Relation.TransGen (fun x y => y ∈ bitGraph n x) i j) :
      j.val < i.val := by
    induction h with
    | single he => exact edge he
    | tail _ he ih => exact (edge he).trans ih
  intro v hv
  exact (Nat.lt_irrefl _ (path hv))

private theorem bit_targets (n : ℕ) : univ.biUnion (bitGraph n) =
    univ.filter (fun j : Fin (n+1)=>j.val<n.size) := by
  ext j
  simp only [mem_biUnion,mem_univ,true_and,mem_filter,bitGraph]
  constructor
  · rintro ⟨i,hi⟩
    exact Nat.lt_size.mpr ((bit_le hi).trans (Nat.le_of_lt_succ i.isLt))
  · intro hj
    have h := Nat.lt_size.mp hj
    refine ⟨⟨2^j.val,by omega⟩,?_⟩
    simp

private theorem bit_attains (n : ℕ) : sourceCount (bitGraph n) = n+1-n.size := by
  rw [sourceCount,bit_targets,card_sdiff_of_subset (filter_subset _ _),card_univ,Fintype.card_fin]
  have H : (univ.filter (fun j : Fin (n+1) => j.val<n.size)).card = n.size := by
    let b : Fin (n+1) := ⟨n.size,by have := width_le n; omega⟩
    have hi : univ.filter (fun j : Fin (n+1) => j.val<n.size) = Iio b := by
      ext j; simp only [mem_filter,mem_univ,true_and,mem_Iio]; rfl
    rw [hi]; simp [b]
  rw [H]

private theorem graph_max (n : ℕ) : IsGreatest (attainable (n+1)) (n+1-n.size) := by
  constructor
  · exact ⟨bitGraph n,bit_injective n,bit_acyclic n,bit_attains n⟩
  · rintro k ⟨D,hi,_,rfl⟩
    exact bound n D hi


private theorem capacity (t : BinaryTree Unit) : t.numNodes < 2^t.height := by
  induction t with
  | nil => decide
  | node _ l r il ir =>
    have hl := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (le_max_left l.height r.height)
    have hr := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) (le_max_right l.height r.height)
    simp only [BinaryTree.numNodes,BinaryTree.height,pow_succ]
    omega

private theorem build_tree (h n : ℕ) (lo : h≤n) (hi : n<2^h) :
    ∃ t : BinaryTree Unit, t.numNodes=n ∧ t.height=h := by
  induction h using Nat.strong_induction_on generalizing n with
  | h h ih =>
    cases h with
    | zero =>
      have hn : n=0 := by simpa using hi
      exact ⟨.nil,hn.symm,rfl⟩
    | succ h =>
      let a := min (2^h-1) (n-1)
      let b := n-1-a
      have hp : h<2^h := Nat.lt_two_pow_self
      have hcap : n<2^h*2 := by simpa [pow_succ] using hi
      have hlow : h≤a := by dsimp [a]; omega
      have has : a<2^h := by dsimp [a]; omega
      have hbs : b<2^h := by dsimp [b,a]; omega
      obtain ⟨l,hln,hlh⟩ := ih h (by omega) a hlow has
      have hb : b.size≤h := Nat.size_le.mpr hbs
      obtain ⟨r,hrn,hrh⟩ := ih b.size (by omega) b
        (Nat.size_le.mpr Nat.lt_two_pow_self) (Nat.lt_size_self b)
      refine ⟨.node () l r,?_,?_⟩
      · simp only [BinaryTree.numNodes,hln,hrn]; dsimp [b,a]; omega
      · simp only [BinaryTree.height,hlh,hrh,max_eq_left hb]

private theorem heights_interval (n : ℕ) (hn : 0<n) :
    treeHeights n = Set.Icc n.log2 (n-1) := by
  ext h
  constructor
  · rintro ⟨t,ht,hh⟩
    have hx := capacity t
    have hm := t.height_le_numNodes
    rw [ht,hh] at hx hm
    have hlog := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr hx
    exact ⟨by omega,by omega⟩
  · rintro ⟨ha,hb⟩
    obtain ⟨t,ht,hh⟩ := build_tree (h+1) n (by omega)
      ((Nat.log2_lt (Nat.ne_of_gt hn)).mp (by omega))
    exact ⟨t,ht,hh⟩

private theorem heights_count (n : ℕ) (hn : 0<n) :
    (treeHeights n).ncard = n-n.log2 := by
  rw [heights_interval n hn,←Finset.coe_Icc,Set.ncard_coe_finset,Nat.card_Icc]
  omega

private theorem nonpowers (n : ℕ) :
    {k : ℕ | k≤n ∧ ¬ ∃ e : ℕ, k=2^e}.ncard = n+1-n.size := by
  classical
  let powers := (range n.size).image (fun k : ℕ=>2^k)
  have sub : powers ⊆ range (n+1) := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.lt_size.mp (mem_range.mp he)))
  have equal : {k : ℕ | k≤n ∧ ¬ ∃ e : ℕ, k=2^e} =
      (↑(range (n+1) \ powers) : Set ℕ) := by
    ext k
    simp only [coe_sdiff,Set.mem_sdiff,mem_coe,mem_range,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hk,he⟩
      refine ⟨by omega,?_⟩
      rintro hp
      obtain ⟨e,_,rfl⟩ := mem_image.mp hp
      exact he ⟨e,rfl⟩
    · rintro ⟨hk,hp⟩
      refine ⟨by omega,?_⟩
      rintro ⟨e,rfl⟩
      exact hp (mem_image.mpr ⟨e,mem_range.mpr (Nat.lt_size.mpr (by omega)),rfl⟩)
  rw [equal,Set.ncard_coe_finset,card_sdiff_of_subset sub,card_range]
  have hc : powers.card = n.size := by
    dsimp [powers]
    rw [card_image_of_injective,card_range]
    intro a b hab
    exact Nat.pow_right_injective (by decide : 2≤2) hab
  rw [hc]


private theorem floor_sign_count (n : ℕ) (hn : 0<n) :
    (∑ i ∈ Icc 1 (n+1), if 0 < n / 2^i then 1 else 0) = n.log2 := by
  have hlog : n.log2≤n := by
    have h := Nat.lt_two_pow_self (n:=n)
    have := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr h
    omega
  have he : (Icc 1 (n+1)).filter (fun i=>0<n/2^i) = Icc 1 n.log2 := by
    ext i
    simp only [mem_filter,mem_Icc]
    have hh : 0<n/2^i ↔ i≤n.log2 := by
      rw [Nat.le_log2 (Nat.ne_of_gt hn)]
      simp only [Nat.div_pos_iff, Nat.two_pow_pos, true_and]
    rw [hh]
    omega
  rw [←sum_filter,he]
  simp

private theorem width_sum (n : ℕ) :
    (∑ i ∈ range (n+1), i.size) = (∑ i ∈ range (n+1), i.log2)+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : n+1≠0 := by omega
    have hl : (n+1).size = (n+1).log2+1 := by
      have hi : (n+1).size ≤ (n+1).log2+1 :=
        Nat.size_le.mpr ((Nat.log2_lt hpos).mp (by omega))
      have lo : (n+1).log2 < (n+1).size := Nat.lt_size.mpr ((Nat.le_log2 hpos).mp le_rfl)
      omega
    rw [sum_range_succ (fun i : ℕ=>i.size),sum_range_succ (fun i : ℕ=>i.log2),ih,hl]
    omega

private theorem width_sum_diff (n : ℕ) (hn : 0<n) :
    (∑ i ∈ range n, i.size) + 1 - (∑ i ∈ range (n+1), i.log2) = n-n.log2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [width_sum, sum_range_succ (fun i : ℕ=>i.log2) (m+1)]
  simp only [Nat.succ_eq_add_one]
  omega

private theorem size_increment (n : ℕ) :
    (n+1).size = if ∃ e : ℕ, n+1=2^e then n.size+1 else n.size := by
  classical
  have hm : n.size ≤ (n+1).size := Nat.size_le_size (Nat.le_succ n)
  have hu : (n+1).size ≤ n.size+1 := by
    apply Nat.size_le.mpr
    have := Nat.lt_size_self n
    rw [pow_succ]; omega
  by_cases h : ∃ e : ℕ, n+1=2^e
  · rw [if_pos h]
    obtain ⟨e,he⟩ := h
    have h' : (n+1).size=e+1 := by rw [he,Nat.size_pow]
    have hn : n.size≤e := Nat.size_le.mpr (by omega)
    omega
  · rw [if_neg h]
    by_contra hne
    have H : n.size < (n+1).size := by omega
    have lo := Nat.lt_size.mp H
    have hi := Nat.lt_size_self n
    exact h ⟨n.size,by omega⟩

private theorem repeated (n : ℕ) :
    (n+1-n.size=n+2-(n+1).size) ↔ ∃ e : ℕ, n+1=2^e := by
  classical
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  rw [size_increment]
  split_ifs <;> simp_all
  omega


end A182220Proof

open A182220Proof OMA.S_oeis_a182220 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182220.main := by
  intro n
  dsimp only
  rw [←closed_form n]
  refine ⟨graph_max n, nonpowers n, ?_, ?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro hn
      rw [floor_sign_count n hn,closed_form,if_neg (Nat.ne_of_gt hn)]
    · intro hn
      rw [width_sum_diff n hn,closed_form,if_neg (Nat.ne_of_gt hn)]
    · have hnext : n+2-(n+1).size = (n+1)-(n+1).log2 := by
        exact (closed_form (n+1)).trans (if_neg (by omega))
      rw [←hnext]
      exact repeated n
  · intro hn
    rw [closed_form,if_neg (Nat.ne_of_gt hn)]
    exact ⟨heights_interval n hn,heights_count n hn⟩
