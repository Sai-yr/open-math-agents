import OMAStatements.S_oeis_a373308
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

open OMA.S_oeis_a373308 Polynomial

namespace ThueMorseCube

private def coeffZ (P : Polynomial ℤ) (i : ℤ) := if i < 0 then 0 else P.coeff i.toNat
private noncomputable def A (i : ℤ) := coeffZ (truncation (i.toNat+1)) i

private lemma A_nat (n : ℕ) : A n = a n := by simp [A,coeffZ,a]
private lemma A_neg {i : ℤ} (hi : i<0) : A i=0 := by simp [A,coeffZ,hi]

private lemma shift (P : Polynomial ℤ) (k : ℕ) (i : ℤ) :
    coeffZ (P*X^k) i = coeffZ P (i-k) := by
  unfold coeffZ
  rw [coeff_mul_X_pow']
  split_ifs <;> first | rfl | (congr 1; omega)

private lemma multiply (P : Polynomial ℤ) (k : ℕ) (i : ℤ) :
    coeffZ (P*(1-X^k)^3) i = coeffZ P i - 3*coeffZ P (i-k) +
      3*coeffZ P (i-2*k) - coeffZ P (i-3*k) := by
  have E : P*(1-X^k)^3 = P - C (3:ℤ)*(P*X^k) + C (3:ℤ)*(P*X^(2*k)) - P*X^(3*k) := by
    simp only [Nat.mul_comm 2 k,Nat.mul_comm 3 k,pow_mul,map_ofNat]
    ring
  rw [E,← shift P k i,show (2:ℤ)*k = ((2*k:ℕ):ℤ) by push_cast; rfl,
    show (3:ℤ)*k = ((3*k:ℕ):ℤ) by push_cast; rfl,← shift P (2*k) i,← shift P (3*k) i]
  by_cases h : i<0 <;> simp [coeffZ,h]

private lemma stable {i : ℤ} (d : ℕ) (h : i.toNat+1 ≤ d) : coeffZ (truncation d) i = A i := by
  induction d,h using Nat.le_induction with
  | base => rfl
  | succ d h ih =>
    have hb : i < (2^d : ℕ) := by have := Nat.lt_two_pow_self (n:=d); omega
    rw [show truncation (d+1) = truncation d * (1-X^(2^d))^3 by simp [truncation,Finset.prod_range_succ],multiply]
    have hz (j : ℤ) (hj : j<0) : coeffZ (truncation d) j = 0 := by simp [coeffZ,hj]
    have hpos : (0:ℤ) ≤ ↑(2^d:ℕ) := by positivity
    rw [hz (i-↑(2^d:ℕ)) (by omega),hz (i-2*↑(2^d:ℕ)) (by omega),hz (i-3*↑(2^d:ℕ)) (by omega),ih]
    ring

private lemma expand_stage (d : ℕ) : truncation (d+1) = expand ℤ 2 (truncation d)*(1-X)^3 := by
  simp [truncation,Finset.prod_range_succ', map_prod,map_sub,expand_X,map_pow,pow_succ',pow_mul]

private lemma even_coeff (P : Polynomial ℤ) (i : ℤ) : coeffZ (expand ℤ 2 P) (2*i)=coeffZ P i := by
  by_cases hi : 0 ≤ i
  · obtain ⟨i,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    simp [coeffZ,show ¬ 2*(i:ℤ)<0 by omega,show ¬(i:ℤ)<0 by omega, Int.toNat_mul,coeff_expand_mul']
  · have h : 2*i<0 := by omega
    simp [coeffZ,h,show i<0 by omega]

private lemma odd_coeff (P : Polynomial ℤ) (i : ℤ) : coeffZ (expand ℤ 2 P) (2*i+1)=0 := by
  by_cases hi : 0 ≤ i
  · obtain ⟨i,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have e : (2*(i:ℤ)+1).toNat=2*i+1 := by omega
    simp [coeffZ,e,show ¬2*(i:ℤ)+1<0 by omega, coeff_expand (by decide : 0<2),show ¬2 ∣ 2*i+1 by omega]
  · simp [coeffZ,show 2*i+1<0 by omega]

private lemma recs (i : ℤ) : A (2*i)=A i+3*A (i-1) ∧ A (2*i+1)= -3*A i-A (i-1) := by
  let d := 2*i.toNat+3
  have h (j : ℤ) (hj : j.toNat+1 ≤ d) : coeffZ (truncation d) j=A j := stable d hj
  have he := stable (i:=2*i) (d+1) (by dsimp [d]; omega)
  have ho := stable (i:=2*i+1) (d+1) (by dsimp [d]; omega)
  have m := multiply (expand ℤ 2 (truncation d)) 1
  simp only [pow_one] at m
  rw [expand_stage,m] at he ho
  norm_num only [Nat.cast_one,mul_one] at he ho
  rw [show 2*i-1=2*(i-1)+1 by ring,show 2*i-2=2*(i-1) by ring,
    show 2*i-3=2*(i-2)+1 by ring,even_coeff,odd_coeff,even_coeff,odd_coeff] at he
  rw [show 2*i+1-1=2*i by ring,show 2*i+1-2=2*(i-1)+1 by ring,
    show 2*i+1-3=2*(i-1) by ring,odd_coeff,even_coeff,odd_coeff,even_coeff] at ho
  rw [h i (by dsimp [d]; omega),h (i-1) (by dsimp [d]; omega)] at he ho
  constructor <;> linarith

private lemma A_zero : A 0=1 := by
  have he := multiply (1:Polynomial ℤ) 1 0
  simpa [A,coeffZ,truncation] using he

private lemma thue_even (k : ℕ) : thue (2*k) = thue k := by
  by_cases h : k=0
  · simp [h]
  · have he := Nat.digits_add 2 (by decide) 0 k (by decide) (Or.inr h)
    simp only [Nat.zero_add] at he
    simp [thue,he]

private lemma thue_odd (k : ℕ) : thue (2*k+1) = -thue k := by
  have he := Nat.digits_add 2 (by decide) 1 k (by decide) (Or.inl (by decide))
  rw [Nat.add_comm] at he
  unfold thue
  rw [he]
  simp [pow_add]

private def modBlock (x s : ℤ) := A (x-2)%3=0 ∧ A (x-1)%3=0 ∧ A x%3=s%3 ∧ A (x+1)%3=0 ∧ A (x+2)%3=0

private lemma mod_step {x s : ℤ} (h : modBlock x s) : modBlock (2*x) s ∧ modBlock (2*x+3) (-s) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := h
  obtain ⟨a,b⟩ := recs (x-1)
  obtain ⟨c,d⟩ := recs x
  obtain ⟨e,f⟩ := recs (x+1)
  obtain ⟨g,j⟩ := recs (x+2)
  unfold modBlock
  ring_nf at *
  omega

private def parityBlock (x : ℤ) := A (x-2)%2=0 ∧ A (x-1)%2=0 ∧ A x%2=1 ∧ A (x+1)%2=1 ∧
  A (x+2)%2=0 ∧ A (x+3)%2=0

private lemma parity_step {x : ℤ} (h : parityBlock x) : parityBlock (2*x) ∧ parityBlock (2*x+4) := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := h
  obtain ⟨a,b⟩ := recs (x-1)
  obtain ⟨c,d⟩ := recs x
  obtain ⟨e,f⟩ := recs (x+1)
  obtain ⟨g,j⟩ := recs (x+2)
  obtain ⟨l,m⟩ := recs (x+3)
  unfold parityBlock
  ring_nf at *
  omega

private lemma blocks (n : ℕ) : modBlock (3*(n:ℤ)) (thue n) ∧ parityBlock (4*(n:ℤ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      have a := recs 0
      have b := recs 1
      have hn₁ := A_neg (i := -1) (by decide)
      have hn₂ := A_neg (i := -2) (by decide)
      norm_num [A_zero,thue,modBlock,parityBlock] at *
      omega
    obtain ⟨hm,hp⟩ := ih (n/2) (by omega)
    obtain ⟨me,mo⟩ := mod_step hm
    obtain ⟨pe,po⟩ := parity_step hp
    generalize hk : n/2 = k at *
    rcases (by omega : n=2*k ∨ n=2*k+1) with h | h
    · rw [h,thue_even]
      push_cast
      simpa only [mul_left_comm] using And.intro me pe
    · rw [h,thue_odd]
      push_cast
      rw [show 3*(2*(k:ℤ)+1)=2*(3*k)+3 by ring, show 4*(2*(k:ℤ)+1)=2*(4*k)+4 by ring]
      exact ⟨mo,po⟩

private lemma zero_recs (k : ℤ) : A (4*k-1)=8*A (k-1) ∧ A (4*k+2)=8*A (k-1) := by
  obtain ⟨a,b⟩ := recs (k-1)
  obtain ⟨c,d⟩ := recs k
  obtain ⟨_,f⟩ := recs (2*k-1)
  obtain ⟨g,_⟩ := recs (2*k+1)
  ring_nf at *
  constructor <;> linarith

private def allowed (b : ℕ) := ∀ t ∈ Nat.digits 4 b, t ≤ 1

private lemma append_digit (b r : ℕ) (hr : r<4) : allowed (4*b+r) ↔ allowed b ∧ r≤1 := by
  by_cases hz : r=0 ∧ b=0
  · obtain ⟨rfl,rfl⟩ := hz
    simp [allowed]
  · rw [Nat.add_comm (4*b) r]
    simp [allowed,Nat.digits_add 4 (by decide) r b hr (by omega),and_comm]

private lemma zero_digit (k r : ℕ) (hr : r<4) :
    zeroIndex (4*k+r) ↔ zeroIndex k ∧ (r=0 ∨ r=3) := by
  constructor
  · rintro ⟨b,hb,hd⟩
    let t := b/4
    let z := b%4
    have hz : z<4 := Nat.mod_lt _ (by decide)
    have he : b=4*t+z := by dsimp [t,z]; omega
    change allowed b at hd
    rw [he,append_digit t z hz] at hd
    obtain ⟨hgood,hzsmall⟩ := hd
    rcases (by omega : z=0 ∨ z=1) with h | h
    · exact ⟨⟨t,by omega,hgood⟩, Or.inl (by omega)⟩
    · exact ⟨⟨t,by omega,hgood⟩, Or.inr (by omega)⟩
  · rintro ⟨⟨b,rfl,hb⟩,rfl|rfl⟩
    · exact ⟨4*b+0,by omega,(append_digit b 0 (by decide)).mpr ⟨hb,by decide⟩⟩
    · exact ⟨4*b+1,by omega,(append_digit b 1 (by decide)).mpr ⟨hb,by decide⟩⟩

private lemma zero_iff (m : ℕ) : A ((m:ℤ)-1)=0 ↔ zeroIndex m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m=0
    · subst m
      have hz : zeroIndex 0 := ⟨0,rfl,by simp⟩
      norm_num [A_neg,hz]
    have hi := ih (m/4) (by omega)
    generalize hk : m/4 = k at *
    have hp := (blocks k).2
    obtain ⟨_,_,hp₀,hp₁,_,_⟩ := hp
    obtain ⟨h₀,h₃⟩ := zero_recs k
    have he : m=4*k+(m%4) := by omega
    generalize hr : m%4=r at *
    have hl : r<4 := by omega
    rw [he,zero_digit k r hl]
    interval_cases r <;> push_cast <;> norm_num <;> ring_nf at * <;> first | omega | (rw [← hi]; omega)

end ThueMorseCube

theorem OMA.solution : type_of% @OMA.S_oeis_a373308.main := by
  constructor
  · intro n
    obtain ⟨_,_,h,h₁,h₂⟩ := (ThueMorseCube.blocks n).1
    rw [← ThueMorseCube.A_nat,← ThueMorseCube.A_nat,← ThueMorseCube.A_nat]
    push_cast
    exact ⟨h,Int.dvd_of_emod_eq_zero h₁,Int.dvd_of_emod_eq_zero h₂⟩
  · intro n
    simpa [ThueMorseCube.A_nat] using ThueMorseCube.zero_iff (n+1)
