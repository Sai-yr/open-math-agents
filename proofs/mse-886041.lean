import OMAStatements.S_mse_886041
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

open Finset OMA.S_mse_886041

namespace DivisorTable

private lemma count (k m : ℕ) (hk : 0<k) (hm : 0<m)
    (common : ∀ d, 1≤d → d≤k → d ∣ m) : divisorSum k m = (table k m).card := by
  let pairs := (range m).sigma (fun r => range (beta (r+1) k))
  have hcard : pairs.card = divisorSum k m := by simp [pairs,divisorSum,card_sigma]
  rw [← hcard]
  apply card_bij (fun z _ => z.1 + z.2*m + 1)
  · rintro ⟨r,q⟩ hz
    obtain ⟨hr,hq⟩ := mem_sigma.mp hz
    simp only [mem_range] at hr hq
    let d := beta (r+1) k
    have hd : 0<d := Nat.le_findGreatest (P:=fun t => t ∣ r+1) hk (one_dvd _)
    have hdk : d≤k := Nat.findGreatest_le k
    have hdr : d ∣ r+1 := Nat.findGreatest_spec (P:=fun t => t ∣ r+1) hk (one_dvd _)
    have hdm := common d hd hdk
    have hdv : d ∣ r+q*m+1 := by
      rw [show r+q*m+1 = (r+1)+q*m by ring]
      exact dvd_add hdr (hdm.mul_left q)
    obtain ⟨j,hj⟩ := hdv
    have bound : r+q*m+1 ≤ d*m := calc
      _ ≤ (q+1)*m := by rw [Nat.add_mul]; omega
      _ ≤ d*m := Nat.mul_le_mul_right m (show q+1≤d from hq)
    have hjm : j≤m := Nat.le_of_mul_le_mul_left (hj ▸ bound) hd
    have hjp : 0 < j := by
      by_contra! h
      have hj0 : j=0 := by omega
      simp [hj0] at hj
    apply mem_image.mpr
    exact ⟨(d,j),mem_product.mpr ⟨mem_Icc.mpr ⟨hd,hdk⟩,mem_Icc.mpr ⟨hjp,hjm⟩⟩,hj.symm⟩
  · rintro ⟨r,q⟩ hz ⟨r',q'⟩ hz' heq
    have hr := mem_range.mp (mem_sigma.mp hz).1
    have hr' := mem_range.mp (mem_sigma.mp hz').1
    change r+q*m+1 = r'+q'*m+1 at heq
    have h := Nat.add_right_cancel heq
    have hmod := congrArg (· % m) h
    simp [Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hr'] at hmod
    subst r'
    have hqq := Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel h)
    subst q'; rfl
  · intro x hx
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp hx
    obtain ⟨hi,hj⟩ := mem_product.mp hij
    obtain ⟨hi₁,hi₂⟩ := mem_Icc.mp hi
    obtain ⟨hj₁,hj₂⟩ := mem_Icc.mp hj
    let r := (i*j-1)%m
    let q := (i*j-1)/m
    have hr : r<m := Nat.mod_lt _ hm
    have hx : r+q*m+1=i*j := by
      have h := Nat.mod_add_div (i*j-1) m
      have hpos : 0 < i*j := Nat.mul_pos hi₁ hj₁
      dsimp [r,q]
      rw [Nat.mul_comm ((i*j-1)/m)]
      omega
    have hd : i ∣ r+1 := by
      apply (Nat.dvd_add_iff_left ((common i hi₁ hi₂).mul_left q)).mpr
      rw [show r+1+q*m=i*j by omega]
      exact dvd_mul_right _ _
    have hb : i≤beta (r+1) k := Nat.le_findGreatest hi₂ hd
    have bound : i*j ≤ i*m := Nat.mul_le_mul_left i hj₂
    have hq : q < i := by
      by_contra! h
      have := Nat.mul_le_mul_right m h
      omega
    exact ⟨⟨r,q⟩,mem_sigma.mpr ⟨mem_range.mpr hr,mem_range.mpr (hq.trans_le hb)⟩,hx⟩

end DivisorTable

theorem OMA.solution : type_of% @OMA.S_mse_886041.main := by
  intro k hk
  constructor
  · exact DivisorTable.count k _ hk k.factorial_pos (fun _ h₁ h₂ => Nat.dvd_factorial h₁ h₂)
  · apply DivisorTable.count k _ hk
    · apply Nat.pos_of_ne_zero
      apply Finset.lcm_ne_zero_iff.mpr
      intro d hd
      have h := (mem_Icc.mp hd).1
      change d ≠ 0
      omega
    · intro d h₁ h₂
      exact dvd_lcm (f:=id) (mem_Icc.mpr ⟨h₁,h₂⟩)
