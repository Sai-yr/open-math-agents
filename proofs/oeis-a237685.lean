import OMAStatements.S_oeis_a237685
import Mathlib.Tactic

open OMA.S_oeis_a237685

namespace PartitionDepth

private lemma sum_merge (p : Multiset ℕ) : (mergeParts p).sum = p.sum := by
  simpa [mergeParts,Finset.sum,nsmul_eq_mul] using (Finset.sum_multiset_count p).symm

private lemma sum_iter (p : Multiset ℕ) (i : ℕ) : (mergeParts^[i] p).sum = p.sum := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [Function.iterate_succ_apply',sum_merge] using ih

-- A repeated value in the new partition cannot come solely from singleton
-- groups: each such group retains its value, and its old value is unique.
private lemma repeat_step {p : Multiset ℕ} {c : ℕ}
    (h : ∀ y, 1 < p.count y → c≤y) (x : ℕ) (hx : 1 < (mergeParts p).count x) : 2*c≤x := by
  by_contra! small
  let t := p.dedup.filter (fun y => x = p.count y*y)
  have sub : t ≤ ({x} : Multiset ℕ) := by
    apply (Multiset.le_iff_subset ((p.nodup_dedup).filter _)).mpr
    intro y hy
    obtain ⟨hym,he⟩ := Multiset.mem_filter.mp hy
    have pos := Multiset.count_pos.mpr (Multiset.mem_dedup.mp hym)
    have single : p.count y=1 := by
      by_contra hn
      have twice : 2≤p.count y := by omega
      have := Nat.mul_le_mul twice (h y twice)
      omega
    simpa [single] using he.symm
  have hc := Multiset.card_le_card sub
  have hx' : 1 < t.card := by simpa only [t,mergeParts,Multiset.count_map] using hx
  simpa using (show (2 : ℕ) ≤ ({x} : Multiset ℕ).card by omega)

private lemma repeat_bound {p : Multiset ℕ} (hp : ∀ x ∈ p, 0<x) (i x : ℕ)
    (hx : 1<(mergeParts^[i] p).count x) : 2^i≤x := by
  induction i generalizing x with
  | zero =>
    change 1<p.count x at hx
    have pos := hp x (Multiset.count_pos.mp (by omega))
    simpa only [pow_zero] using (show 1≤x by omega)
  | succ i ih =>
    rw [Function.iterate_succ_apply'] at hx
    simpa [pow_succ,mul_comm] using repeat_step ih x hx

private lemma lower {n d : ℕ} (hn : 0<n) (p : Nat.Partition n) (hd : hasDepth p.parts d) :
    2^d≤n := by
  cases d with
  | zero => simpa only [pow_zero] using (show 1≤n by omega)
  | succ i =>
    let t := mergeParts^[i] p.parts
    have hdup : ¬t.Nodup := hd.2 i (Nat.lt_succ_self i)
    rw [Multiset.nodup_iff_count_le_one] at hdup
    push Not at hdup
    obtain ⟨x,hx⟩ := hdup
    have large := repeat_bound (p:=p.parts) (fun _ h => p.parts_pos h) i x hx
    have hm : t.count x*x ∈ mergeParts t :=
      Multiset.mem_map.mpr ⟨x,Multiset.mem_dedup.mpr (Multiset.count_pos.mp (by omega)),rfl⟩
    have bound := Multiset.le_sum_of_mem hm
    rw [sum_merge] at bound
    have total : t.sum=n := (sum_iter p.parts i).trans p.parts_sum
    rw [total] at bound
    simpa [pow_succ,mul_comm] using (Nat.mul_le_mul hx large).trans bound

private def tail (a : ℕ) : ℕ → Multiset ℕ
  | 0 => 0
  | i+1 => a ::ₘ tail (2*a) i

private def ladder (a d : ℕ) := a ::ₘ tail a d

private lemma tail_ge (a i x : ℕ) (hx : x ∈ tail a i) : a ≤ x := by
  induction i generalizing a with
  | zero => simp [tail] at hx
  | succ i ih =>
    rcases Multiset.mem_cons.mp hx with rfl|hx
    · rfl
    · have := ih (2*a) hx
      omega

private lemma tail_nodup {a : ℕ} (ha : 0<a) (d : ℕ) : (tail a d).Nodup := by
  induction d generalizing a with
  | zero => simp [tail]
  | succ i ih =>
    apply Multiset.nodup_cons.mpr
    exact ⟨fun h => by have := tail_ge (2*a) i a h; omega, ih (by omega)⟩

private lemma merge_two (a : ℕ) (q : Multiset ℕ) (hq : q.Nodup) (ha : a ∉ q) :
    mergeParts (a ::ₘ a ::ₘ q) = (2*a) ::ₘ q := by
  simp only [mergeParts,Multiset.dedup_cons_of_mem (Multiset.mem_cons_self _ _),
    Multiset.dedup_cons_of_notMem ha,hq.dedup,Multiset.map_cons]
  congr 1
  · simp [Multiset.count_cons_self,Multiset.count_eq_zero_of_notMem ha]
  · conv_rhs => rw [← Multiset.map_id q]
    apply Multiset.map_congr rfl
    intro y hy
    have hya : y≠a := fun h => ha (h ▸ hy)
    simp [Multiset.count_cons_of_ne hya,Multiset.nodup_iff_count_eq_one.mp hq y hy]

private lemma step_ladder {a : ℕ} (ha : 0<a) (d : ℕ) : mergeParts (ladder a (d+1)) = ladder (2*a) d := by
  apply merge_two
  · exact tail_nodup (by omega) _
  · intro h
    have := tail_ge (2*a) d a h
    omega

private lemma ladder_sum {a : ℕ} (ha : 0<a) (d : ℕ) : (ladder a d).sum = a*2^d := by
  induction d generalizing a with
  | zero => simp [ladder,tail]
  | succ d ih =>
    rw [← sum_merge,step_ladder ha,ih (by omega),pow_succ]
    ring

private lemma ladder_depth {a : ℕ} (ha : 0<a) (d : ℕ) : hasDepth (ladder a d) d := by
  induction d generalizing a with
  | zero => simp [hasDepth,ladder,tail]
  | succ d ih =>
    have ih' := ih (a:=2*a) (by omega)
    constructor
    · simpa [Function.iterate_succ_apply,step_ladder ha] using ih'.1
    · intro i hi
      cases i with
      | zero => simp [ladder,tail]
      | succ i =>
        simpa [Function.iterate_succ_apply,step_ladder ha] using ih'.2 i (by omega)

end PartitionDepth

theorem OMA.solution : type_of% @OMA.S_oeis_a237685.main := by
  intro d
  constructor
  · refine ⟨by positivity,?_⟩
    let p : Nat.Partition (2^d) := {
      parts := PartitionDepth.ladder 1 d
      parts_pos := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with rfl|h
        · decide
        · exact PartitionDepth.tail_ge 1 d x h
      parts_sum := by simpa using PartitionDepth.ladder_sum (a:=1) (by decide) d }
    exact ⟨p,PartitionDepth.ladder_depth (by decide : 0<1) d⟩
  · rintro n ⟨hn,p,hp⟩
    exact PartitionDepth.lower hn p hp
