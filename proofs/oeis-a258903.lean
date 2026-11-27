import OMAStatements.S_oeis_a258903
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open OMA.S_oeis_a258903

namespace WeightedDivisorSum

private theorem power_period (a M : ℕ) : ∀ L : ℕ, M.totient ∣ L → 0 < M →
    ∃ N : ℕ, ∀ n ≥ N, a^(n+L) ≡ a^n [MOD M] := by
  induction M using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => intro L _ _; exact ⟨0,fun _ _ => by simp [Nat.ModEq,Nat.mod_one]⟩
  | prime_pow p j hp _ =>
    intro L hL _
    by_cases hd : p ∣ a
    · refine ⟨j,fun n hn => ?_⟩
      have vanish (t : ℕ) (ht : j ≤ t) : a^t ≡ 0 [MOD p^j] :=
        Nat.modEq_zero_iff_dvd.mpr ((pow_dvd_pow_of_dvd hd j).trans (pow_dvd_pow a ht))
      exact (vanish _ (by omega)).trans (vanish n hn).symm
    · obtain ⟨c,rfl⟩ := hL
      have cop : a.Coprime (p^j) := ((hp.coprime_iff_not_dvd.mpr hd).symm).pow_right _
      have eq := (Nat.ModEq.pow_totient cop).pow c
      refine ⟨0,fun n _ => ?_⟩
      simpa only [pow_add,pow_mul,one_pow,mul_one] using eq.mul_left (a^n)
  | coprime b c hb hc hbc ihb ihc =>
    intro L hL _
    obtain ⟨B,hB⟩ := ihb L ((Nat.totient_dvd_of_dvd (dvd_mul_right b c)).trans hL) (by omega)
    obtain ⟨C,hC⟩ := ihc L ((Nat.totient_dvd_of_dvd (dvd_mul_left c b)).trans hL) (by omega)
    exact ⟨max B C,fun n hn => (Nat.modEq_and_modEq_iff_modEq_mul hbc).mp
      ⟨hB n (by omega),hC n (by omega)⟩⟩

private theorem middle {M n d e : ℕ} (hM : 0 < M) (hn : 2*M+4 ≤ n)
    (hd : 2 ≤ d) (he : 2 ≤ e) (hde : d*e=n) (u v : ℕ) :
    term u v n (d,e) ≡ 0 [MOD M] := by
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le he
  have hfit : M + (d+e) ≤ n := by nlinarith [Nat.zero_le (i*j)]
  have denom := Nat.factorial_mul_factorial_dvd_factorial_add d e
  have big : M*(d.factorial*e.factorial) ∣ n.factorial :=
    (Nat.mul_dvd_mul (Nat.dvd_factorial hM (le_refl M)) denom).trans
      ((Nat.factorial_mul_factorial_dvd_factorial_add M (d+e)).trans
        (Nat.factorial_dvd_factorial hfit))
  have den : d.factorial*e.factorial ∣ n.factorial :=
    (dvd_mul_left _ M).trans big
  unfold term
  simp only [Nat.mul_div_assoc _ den]
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right ((Nat.dvd_div_iff_mul_dvd den).mpr (by simpa only [Nat.mul_comm M] using big)) _)

private theorem boundary (u v M n : ℕ) (hM : 0 < M) (hn : 2*M+4 ≤ n) :
    seq u v n ≡ u*v^n + u^n*v [MOD M] := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  let S := n.divisorsAntidiagonal
  have h1 : (1,n) ∈ S := by simp [S,Nat.mem_divisorsAntidiagonal,hn0]
  have h2 : (n,1) ∈ S.erase (1,n) := by simp [S,Nat.mem_divisorsAntidiagonal,hn0,hn1]
  have hrest : (∑ x ∈ (S.erase (1,n)).erase (n,1), term u v n x) ≡ 0 [MOD M] := by
    apply Nat.ModEq.sum_zero
    rintro ⟨d,e⟩ h
    simp only [Finset.mem_erase,Nat.mem_divisorsAntidiagonal,S] at h
    obtain ⟨h₂,h₁,hde,_⟩ := h
    have hd : 2 ≤ d := by
      by_contra! h
      interval_cases d <;> simp_all
    have he : 2 ≤ e := by
      by_contra! h
      interval_cases e <;> simp_all
    exact middle hM hn hd he hde u v
  have f1 : term u v n (1,n) = u*v^n := by simp [term, Nat.factorial_pos]
  have f2 : term u v n (n,1) = u^n*v := by simp [term, Nat.factorial_pos]
  unfold seq
  rw [if_neg hn0]
  change (∑ x ∈ S, _) ≡ _ [MOD M]
  rw [← Finset.add_sum_erase _ _ h1,← Finset.add_sum_erase _ _ h2,f1,f2]
  simpa using (hrest.add_left (u^n*v)).add_left (u*v^n)

theorem eventual_period (u v M : ℕ) (hM : 0 < M) : ∃ N : ℕ, ∀ n ≥ N,
    seq u v (n+M.totient) ≡ seq u v n [MOD M] := by
  obtain ⟨A,hA⟩ := power_period u M _ (dvd_refl _) hM
  obtain ⟨B,hB⟩ := power_period v M _ (dvd_refl _) hM
  refine ⟨max (2*M+4) (max A B),?_⟩
  intro n hn
  exact (boundary u v M _ hM (by omega)).trans <|
    (((hB n (by omega)).mul_left u).add ((hA n (by omega)).mul_right v)).trans
      (boundary u v M n hM (by omega)).symm

end WeightedDivisorSum

theorem OMA.solution : type_of% @OMA.S_oeis_a258903.main :=
  WeightedDivisorSum.eventual_period 2 3
