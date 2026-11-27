import OMAStatements.S_oeis_a143772
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

open OMA.S_oeis_a143772

namespace DivisorPairSums

private lemma value_dvd {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : value n ∣ d + n/d :=
  Finset.gcd_dvd (Nat.mem_divisors.mpr ⟨hd,hn⟩)

private lemma necessary {n : ℕ} (hn : 1 < n) : Even (value n) ∨ value n=1 ∨ value n=3 := by
  have hn0 : n ≠ 0 := by omega
  by_cases he : 2 ∣ n
  · have h₁ : value n ∣ 1+n := by simpa using value_dvd hn0 (one_dvd n)
    have h₂ := value_dvd hn0 he
    have h₃ := Nat.dvd_sub (h₂.trans (dvd_mul_left _ 2)) h₁
    have hhalf := Nat.mul_div_cancel' he
    rw [show 2*(2+n/2)-(1+n)=3 by omega] at h₃
    exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h₃)
  · apply Or.inl
    apply even_iff_two_dvd.mpr
    apply Finset.dvd_gcd_iff.mpr
    intro d hd
    obtain ⟨hdn,_⟩ := Nat.mem_divisors.mp hd
    have hodd₁ : ¬ 2 ∣ d := fun h => he (h.trans hdn)
    have hodd₂ : ¬ 2 ∣ n/d := fun h => he (h.trans (Nat.div_dvd_of_dvd hdn))
    omega

private lemma semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    value (p*q) = Nat.gcd (1+p*q) (p+q) := by
  have hn : p*q ≠ 0 := mul_ne_zero hp.ne_zero hq.ne_zero
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · simpa using value_dvd hn (one_dvd (p*q))
    · simpa [Nat.mul_div_cancel_left _ hp.pos] using value_dvd hn (dvd_mul_right p q)
  · apply Finset.dvd_gcd_iff.mpr
    intro d hd
    obtain ⟨x,y,hx,hy,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.mem_divisors.mp hd).1
    rcases (Nat.dvd_prime hp).mp hx with hx | hx <;>
      rcases (Nat.dvd_prime hq).mp hy with hy | hy <;> subst x <;> subst y
    · simpa using Nat.gcd_dvd_left (1+p*q) (p+q)
    · simpa [Nat.mul_div_cancel _ hq.pos, Nat.add_comm] using Nat.gcd_dvd_right (1+p*q) (p+q)
    · simpa [Nat.mul_div_cancel_left _ hp.pos] using Nat.gcd_dvd_right (1+p*q) (p+q)
    · simpa [Nat.div_self (Nat.pos_of_ne_zero hn), Nat.add_comm] using Nat.gcd_dvd_left (1+p*q) (p+q)

private lemma remove_product {p q : ℕ} (hp : 1 < p) :
    Nat.gcd (1+p*q) (p+q) = Nat.gcd (p^2-1) (p+q) := by
  have hs : 1 ≤ p^2 := Nat.one_le_pow _ _ (by omega)
  have h₁ : p*(p+q)-(1+p*q)=p^2-1 := by rw [Nat.mul_add,← sq]; omega
  have h₂ : p*(p+q)-(p^2-1)=1+p*q := by rw [Nat.mul_add,← sq]; omega
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    rw [← h₁]
    exact Nat.dvd_sub ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) (Nat.gcd_dvd_left _ _)
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    rw [← h₂]
    exact Nat.dvd_sub ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)) (Nat.gcd_dvd_left _ _)

private lemma realize_even {g : ℕ} (hg : 0 < g) (heven : Even g) :
    ∃ m : ℕ, 1 < m ∧ ¬ m.Prime ∧ value m=g := by
  have hg2 : 2 ≤ g := by obtain ⟨t,ht⟩ := heven; omega
  let C := g^2-1
  let u := C-g
  have hbound : 2*g ≤ g^2 := by simpa [pow_two,Nat.mul_comm] using Nat.mul_le_mul_left g hg2
  have hgC : g ≤ C := by dsimp [C]; omega
  have hCpos : 0 < C := hg.trans_le hgC
  have hu : u+g=C := Nat.sub_add_cancel hgC
  have hCs : C+1=g^2 := by dsimp [C]; omega
  have hCg : C.Coprime g := by
    apply Nat.coprime_of_dvd
    intro a ha hdC hdg
    have hD := Nat.dvd_sub (hdg.trans (dvd_pow_self g (by decide : 2 ≠ 0))) hdC
    rw [show g^2-C=1 by omega] at hD
    exact ha.not_dvd_one hD
  have hug : u.Coprime g := (Nat.coprime_sub_self_left hgC).mpr hCg
  have huC : u.Coprime C := (Nat.coprime_self_sub_left hgC).mpr hCg.symm
  obtain ⟨p,hpg,hp,hres⟩ := Nat.forall_exists_prime_gt_and_modEq (g+2)
    (mul_ne_zero hg.ne' hCpos.ne') (hug.mul_right huC)
  have hgu : g ∣ u+1 := by
    have h : u+1=g*(g-1) := by rw [Nat.mul_sub,Nat.mul_one,← sq]; omega
    exact h ▸ dvd_mul_right _ _
  have hgp : g ∣ p+1 := ((hres.add_right 1).dvd_iff (dvd_mul_right g C)).mpr hgu
  have hCp : C ∣ p+g := ((hres.add_right g).dvd_iff (dvd_mul_left C g)).mpr (hu ▸ dvd_rfl)
  let M := p^2-1
  have hp2 : 2 ≤ p := hp.two_le
  have hbp : 2*p ≤ p^2 := by simpa [pow_two,Nat.mul_comm] using Nat.mul_le_mul_left p hp2
  have hpM : p ≤ M := by dsimp [M]; omega
  have hMpos : 0 < M := hp.pos.trans_le hpM
  have hgM : g ∣ M := by
    have ha : M=(p+1)*(p-1) := by
      dsimp [M]
      have hk := Nat.sub_add_cancel (by omega : 1 ≤ p)
      have hsq : 1 ≤ p^2 := by omega
      have hminus := Nat.sub_add_cancel hsq
      nlinarith
    exact ha ▸ hgp.trans (dvd_mul_right _ _)
  let r := M+g-p
  have hr : r+p=M+g := Nat.sub_add_cancel (by omega)
  have hrM : r.Coprime M := by
    apply Nat.coprime_of_dvd
    intro a ha hdr hdM
    have em : p ≡ g [MOD a] := by
      calc p ≡ r+p [MOD a] := by simpa using ((Nat.modEq_zero_iff_dvd.mpr hdr).add_right p).symm
           _ = M+g := hr
           _ ≡ g [MOD a] := by simpa using (Nat.modEq_zero_iff_dvd.mpr hdM).add_right g
    have es : 1 ≡ p^2 [MOD a] := (Nat.modEq_iff_dvd' (by omega : 1 ≤ p^2)).mpr hdM
    have haC : a ∣ C := (Nat.modEq_iff_dvd' (by omega : 1 ≤ g^2)).mp (es.trans (em.pow 2))
    have hpag := haC.trans hCp
    have hgg := ((em.add_right g).dvd_iff (dvd_refl a)).mp hpag
    rw [← two_mul] at hgg
    have hang : ¬ a ∣ g := fun hag => (Nat.not_coprime_of_dvd_of_dvd ha.one_lt haC hag) hCg
    have ha2 : a ∣ 2 := (ha.dvd_mul.mp hgg).resolve_right hang
    exact hang (ha2.trans (even_iff_two_dvd.mp heven))
  obtain ⟨q,hqgt,hq,hqres⟩ := Nat.forall_exists_prime_gt_and_modEq p hMpos.ne' hrM
  have hsum : p+q ≡ g [MOD M] := by
    calc p+q = q+p := Nat.add_comm ..
         _ ≡ r+p [MOD M] := hqres.add_right p
         _ = M+g := hr
         _ ≡ g [MOD M] := by simp [Nat.ModEq]
  refine ⟨p*q, by nlinarith [hp.one_lt,hq.one_lt], Nat.not_prime_mul hp.ne_one hq.ne_one, ?_⟩
  rw [semiprime hp hq,remove_product hp.one_lt,Nat.gcd_comm]
  exact hsum.gcd_eq.trans (Nat.gcd_eq_left hgM)

end DivisorPairSums

theorem OMA.solution : type_of% @OMA.S_oeis_a143772.main := by
  intro g hg
  constructor
  · rintro ⟨m,hm,_,rfl⟩
    exact DivisorPairSums.necessary hm
  · rintro (he | rfl | rfl)
    · exact DivisorPairSums.realize_even hg he
    · exact ⟨4, by decide, by decide, by decide⟩
    · exact ⟨8, by decide, by decide, by decide⟩
