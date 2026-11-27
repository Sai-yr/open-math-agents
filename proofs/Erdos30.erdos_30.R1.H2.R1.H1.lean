import OMAReductions.R_Erdos30_erdos_30_R1_H2_R1
import Mathlib

/-!
# Changing marks of a modular Sidon ruler inside one period

The score inequality below counts the modular representations x+c=a+b that
survive in the integer interval. The score is evaluated on the original ruler,
so it gives an obstruction to inserting even one new mark after deletions.
-/
namespace SidonEdits
open Finset

def splitWeight (m x a : ℤ) : ℤ := if a<x then x-2*a else 2*a-x-m

def endWeight (m c : ℤ) : ℤ := max 0 (m-4*min c (m-c))

private theorem weightLow {m x a : ℤ} (_hx : 0≤x) (_hmx : x < m) (ha : 0≤a) (hma : a < m) :
    -m ≤ splitWeight m x a := by
  unfold splitWeight
  split <;> omega

private theorem localBound {m x a b c : ℤ} (_hx : 0≤x) (hx' : x < m)
    (ha : 0≤a) (ha' : a < m) (hb : 0≤b) (hb' : b < m) (hc : 0≤c) (hc' : c < m)
    (cong : a+b=x+c ∨ a+b+m=x+c ∨ a+b=x+c+m) :
    m ≤ 2*splitWeight m x a + 2*splitWeight m x b + endWeight m c +
      (if a+b=x+c then 4*m else 0) := by
  unfold splitWeight endWeight
  rcases cong with h|h|h <;> split_ifs <;> omega

private theorem fiberWeight {J D : Type*} [Fintype J] [Fintype D] [DecidableEq D]
    (f : J → D) (n : ℕ) (cap : ∀ d, (univ.filter (fun j => f j=d)).card ≤ n)
    (w : D → ℤ) (positive : ∀ d, 0≤w d) : ∑ j, w (f j) ≤ n * ∑ d, w d := by
  classical
  rw [← sum_fiberwise univ f (fun j => w (f j)),mul_sum]
  apply sum_le_sum
  intro d _
  calc
    _ = ∑ _j ∈ univ.filter (fun j => f j=d), w d := by
      apply sum_congr rfl
      intro j hj
      rw [(mem_filter.mp hj).2]
    _ = ((univ.filter (fun j => f j=d)).card : ℤ) * w d := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast cap d) (positive d)

private theorem injectionWeight {J D : Type*} [Fintype J] [Fintype D] (f : J ↪ D)
    (w : D → ℤ) (positive : ∀ d, 0≤w d) : ∑ j, w (f j) ≤ ∑ d, w d := by
  classical
  rw [← sum_map univ f w]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun d _ _ => positive d)

private theorem valCong {m : ℕ} [NeZero m] {a b x c : ZMod m} (h : a+b=x+c) :
    (a.val : ℤ)+b.val=x.val+c.val ∨ (a.val : ℤ)+b.val+m=x.val+c.val ∨
    (a.val : ℤ)+b.val=x.val+c.val+m := by
  have eq := congrArg ZMod.val h
  by_cases l : a.val+b.val < m <;> by_cases r : x.val+c.val < m
  · rw [ZMod.val_add_of_lt l,ZMod.val_add_of_lt r] at eq
    omega
  · rw [ZMod.val_add_of_lt l,ZMod.val_add_of_le (by omega)] at eq
    omega
  · rw [ZMod.val_add_of_le (by omega),ZMod.val_add_of_lt r] at eq
    omega
  · rw [ZMod.val_add_of_le (by omega),ZMod.val_add_of_le (by omega)] at eq
    omega

/-- One entry per represented anchor. The involution exchanges the two
summands in the modular representation, and its third coordinate has fibers
of size at most two. -/
private theorem sumBound {m : ℕ} [NeZero m] {D J : Type} [Fintype D] [Fintype J]
    [DecidableEq D] (v : D ↪ ZMod m) (anchor : J ↪ D) (mate : Equiv.Perm J) (third : J → D)
    (twice : ∀ d, (univ.filter (fun j => third j=d)).card ≤ 2)
    (x : ZMod m) (outside : ∀ d, v d ≠ x)
    (cong : ∀ j, v (anchor j) + v (anchor (mate j)) = x+v (third j))
    (A : Finset ℕ) (sidon : IsSidon (A : Set ℕ)) (present : x.val ∈ A) :
    let p (d : D) := splitWeight m x.val (v d).val
    let g (d : D) := endWeight m (v d).val
    let miss (d : D) : ℤ := if (v d).val ∈ A then 0 else 1
    (m : ℤ)*Fintype.card D ≤ 4*(∑ d, p d) + 2*(∑ d, g d) +
      16*m*(∑ d, miss d) + 5*m*((Fintype.card D : ℤ)-Fintype.card J) := by
  classical
  intro p g miss
  have valne (d : D) : (v d).val ≠ x.val := fun h => outside d (ZMod.val_injective m h)
  have mpos : (0 : ℤ) < m := by exact_mod_cast NeZero.pos m
  have vx : (x.val : ℤ) < m := by exact_mod_cast ZMod.val_lt x
  have vd (d : D) : ((v d).val : ℤ) < m := by exact_mod_cast ZMod.val_lt (v d)
  have nonneg (d : D) : 0 ≤ miss d := by dsimp [miss]; split <;> omega
  have localIneq (j : J) :
      (m : ℤ) ≤ 2*p (anchor j) + 2*p (anchor (mate j)) + g (third j) +
        4*m*(miss (anchor j) + miss (anchor (mate j)) + miss (third j)) := by
    let a := anchor j
    let b := anchor (mate j)
    let c := third j
    change (m : ℤ) ≤ 2*p a + 2*p b + g c + 4*m*(miss a+miss b+miss c)
    have bound := localBound (Nat.cast_nonneg x.val) vx (Nat.cast_nonneg (v a).val)
      (vd a) (Nat.cast_nonneg (v b).val) (vd b) (Nat.cast_nonneg (v c).val) (vd c)
      (valCong (cong j))
    change (m : ℤ) ≤ 2*p a + 2*p b + g c +
        (if ((v a).val : ℤ)+(v b).val=x.val+(v c).val then 4*(m : ℤ) else 0) at bound
    apply bound.trans
    apply add_le_add_right
    split_ifs with eq
    · have conflict : ¬((v a).val∈A ∧ (v b).val∈A ∧ (v c).val∈A) := by
        rintro ⟨ha,hb,hc⟩
        have hsum : (v a).val+(v b).val=x.val+(v c).val := by exact_mod_cast eq
        obtain h|h := sidon _ ha _ present _ hb _ hc hsum
        · exact valne a h.1
        · exact valne b h.2
      have hit : 1 ≤ miss a + miss b + miss c := by
        dsimp [miss]; split <;> split <;> split <;> simp_all
      nlinarith
    · exact mul_nonneg (by positivity) (by linarith [nonneg a,nonneg b,nonneg c])
  have s := sum_le_sum (s := univ) (fun j _ => localIneq j)
  simp only [sum_const,card_univ,nsmul_eq_mul,sum_add_distrib,← mul_sum] at s
  rw [Equiv.sum_comp mate (fun j => p (anchor j)),Equiv.sum_comp mate (fun j => miss (anchor j))] at s
  have loss := injectionWeight anchor miss nonneg
  have lossC := fiberWeight third 2 twice miss nonneg
  have massC := fiberWeight third 2 twice g (fun _ => le_max_left _ _)
  have mass := injectionWeight anchor (fun d => p d+m) (by
    intro d; have := weightLow (Nat.cast_nonneg x.val) vx (Nat.cast_nonneg (v d).val) (vd d)
    dsimp [p]; omega)
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at mass
  norm_num at lossC massC
  nlinarith [mul_le_mul_of_nonneg_left loss mpos.le,mul_le_mul_of_nonneg_left lossC mpos.le]


/-- Anchors producing a modular representation of the proposed new mark. -/
noncomputable def represented {m : ℕ} (D : Finset (ZMod m)) (x : ZMod m) : Finset (ZMod m) := by
  classical
  exact D.filter fun a => ∃ b ∈ D, ∃ c ∈ D, a+b=x+c

/-- A deterministic obstruction to adding a mark in the integer interval.
The last term counts absent modular differences. It vanishes for perfect
difference sets. All sums on the right use only the original ruler. -/
theorem finiteEstimate {m : ℕ} [NeZero m] (D : Finset (ZMod m)) (modSidon : IsSidon (D : Set (ZMod m)))
    (A : Finset ℕ) (sidon : IsSidon (A : Set ℕ)) (x : ZMod m) (outside : x ∉ D)
    (present : x.val ∈ A) :
    (m : ℤ)*D.card ≤ 4*(∑ d ∈ D, splitWeight m x.val d.val) +
      2*(∑ d ∈ D, endWeight m d.val) +
      16*m*((D.filter (fun d => d.val ∉ A)).card : ℤ) +
      5*m*((D.card : ℤ)-(represented D x).card) := by
  classical
  let S := represented D x
  have memS {a : ZMod m} : a ∈ S ↔ a ∈ D ∧ ∃ b ∈ D, ∃ c ∈ D, a+b=x+c := by
    simp only [S,represented,mem_filter]
  let a : S ↪ D := ⟨fun j => ⟨j.val,(memS.mp j.property).1⟩,
    fun j k h => Subtype.ext (congrArg (fun z : D => z.val) h)⟩
  have witness (j : S) : ∃ b : D, ∃ c : D, j.val+b.val=x+c.val := by
    obtain ⟨b,hb,c,hc,h⟩ := (memS.mp j.property).2
    exact ⟨⟨b,hb⟩,⟨c,hc⟩,h⟩
  choose b c h using witness
  have bmem (j : S) : (b j).val ∈ S :=
    memS.mpr ⟨(b j).property,j.val,(a j).property,(c j).val,(c j).property,by rw [add_comm,h]⟩
  let swap (j : S) : S := ⟨(b j).val,bmem j⟩
  have inv : Function.Involutive swap := by
    intro j
    have h₁ := h j
    have h₂ := h (swap j)
    change (b j).val+(b (swap j)).val=x+(c (swap j)).val at h₂
    have eq : (b (swap j)).val+(c j).val=j.val+(c (swap j)).val := by
      linear_combination h₂-h₁
    rcases modSidon _ (b (swap j)).property _ (a j).property _ (c j).property
        _ (c (swap j)).property eq with he|he
    · exact Subtype.ext he.1
    · have bad : (b j).val=x := by rw [he.1] at h₂; exact add_right_cancel h₂
      exact (outside (bad ▸ (b j).property)).elim
  let mate := inv.toPerm swap
  have cap (d : D) : (univ.filter (fun j => c j=d)).card ≤ 2 := by
    let F := univ.filter (fun j => c j=d)
    change F.card ≤ 2
    by_cases ex : F.Nonempty
    · obtain ⟨i,hi⟩ := ex
      apply (card_le_card (t := {i,swap i}) ?_).trans card_le_two
      intro j hj
      have vc (t : S) (ht : t∈F) : (c t).val=d.val :=
        congrArg Subtype.val ((mem_filter.mp ht).2)
      have eq : j.val+(b j).val=i.val+(b i).val := by rw [h j,h i,vc j hj,vc i hi]
      rcases modSidon _ (a j).property _ (a i).property _ (b j).property _ (b i).property eq with he|he
      · simp [show j=i from Subtype.ext he.1]
      · have e : j=swap i := Subtype.ext he.1
        simp [e]
    · simp [Finset.not_nonempty_iff_eq_empty.mp ex]
  let v : D ↪ ZMod m := ⟨Subtype.val,Subtype.val_injective⟩
  have bound := sumBound v a mate c cap x
    (fun d h' => outside (h' ▸ d.property)) h A sidon present
  dsimp only at bound
  have toSum (f : ZMod m → ℤ) : (∑ d : D, f (v d)) = ∑ d ∈ D, f d :=
    (sum_subtype D (fun _ => Iff.rfl) f).symm
  have loss : (∑ d : D, if (v d).val ∈ A then (0 : ℤ) else 1) =
      ((D.filter (fun d => d.val ∉ A)).card : ℤ) := by
    rw [toSum (fun z => if z.val ∈ A then 0 else 1)]
    simpa only [ite_not] using (sum_boole (R := ℤ) (fun d : ZMod m => d.val ∉ A) D)
  rw [toSum (fun d => splitWeight m x.val d.val),toSum (fun d => endWeight m d.val),loss] at bound
  simpa only [Fintype.card_coe,S] using bound

end SidonEdits


theorem OMA.solution : OMA.R_Erdos30_erdos_30_R1_H2_R1.H1 := by
  classical
  intro m _ D A x hD full hA hout hin p g
  have total : SidonEdits.represented D x=D := by
    ext a
    simp only [SidonEdits.represented,Finset.mem_filter,and_iff_left_iff_imp]
    intro ha
    obtain ⟨b,hb,c,hc,eq⟩ := full (x-a) (sub_ne_zero.mpr (fun e => hout (e ▸ ha)))
    exact ⟨b,hb,c,hc,by linear_combination eq⟩
  have h := SidonEdits.finiteEstimate D hD A hA x hout hin
  rw [total,sub_self,mul_zero,add_zero] at h
  have pp (d : ZMod m) : p d = SidonEdits.splitWeight m x.val d.val := by
    dsimp only [p,SidonEdits.splitWeight]
    by_cases lt : d.val<x.val
    · rw [if_pos lt,if_pos (by exact_mod_cast lt)]
    · rw [if_neg lt,if_neg (by exact_mod_cast lt)]
  simp only [pp] 
  change (m : ℤ)*D.card ≤ 16*m*((D.filter (fun d => d.val∉A)).card : ℤ) +
    4*(∑ d ∈ D, SidonEdits.splitWeight m x.val d.val) + 2*(∑ d ∈ D, SidonEdits.endWeight m d.val)
  linarith
