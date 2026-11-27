import OMAStatements.S_oeis_a336838
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

open OMA.S_oeis_a336838

namespace PrimeShiftedMeans

private def geom (x k : ℕ) := ∑ j ∈ Finset.range k, x^j

private lemma geom_add (x a b : ℕ) : geom x (a+b) = geom x a + x^a * geom x b := by
  simp [geom,Finset.sum_range_add,pow_add,Finset.mul_sum]

private lemma geom_mul (x a b : ℕ) : geom x (a*b) = geom x a * geom (x^a) b := by
  induction b with
  | zero => simp [geom]
  | succ b ih =>
    rw [Nat.mul_succ,geom_add,ih]
    simp only [geom,Finset.sum_range_succ,pow_mul]
    ring

private lemma geom_congr {p x : ℕ} (h : x ≡ 1 [MOD p]) (k : ℕ) : geom x k ≡ k [MOD p] := by
  induction k with
  | zero => simp [geom,Nat.ModEq]
  | succ k ih =>
    have hh := h.pow k
    simp only [one_pow] at hh
    simpa only [geom,Finset.sum_range_succ] using ih.add hh

private lemma geom_mean (b x : ℕ) (hx : x ≡ 1 [MOD b]) (k : ℕ) :
    ∃ y d : ℕ, 0 < d ∧ b.Coprime d ∧ k*y = d*geom x k := by
  induction k using induction_on_primes with
  | zero => exact ⟨0,1,by decide,by simp,by simp [geom]⟩
  | one => exact ⟨1,1,by decide,by simp,by simp [geom]⟩
  | prime_mul p t hp ih =>
    obtain ⟨y,d,hd,hcd,hy⟩ := ih
    rw [Nat.mul_comm p t,geom_mul]
    by_cases hpb : p ∣ b
    · have hz := (hx.of_dvd hpb).pow t
      simp only [one_pow] at hz
      have hdiv := ((geom_congr hz p).dvd_iff (dvd_refl p)).mpr (dvd_refl p)
      obtain ⟨j,hj⟩ := hdiv
      refine ⟨y*j,d,hd,hcd,?_⟩
      rw [hj]
      calc t*p*(y*j) = (t*y)*(p*j) := by ring
           _ = _ := by rw [hy]; ring
    · refine ⟨y*geom (x^t) p,d*p,Nat.mul_pos hd hp.pos,hcd.mul_right (hp.coprime_iff_not_dvd.mpr hpb).symm,?_⟩
      calc t*p*(y*geom (x^t) p) = (t*y)*(p*geom (x^t) p) := by ring
           _ = _ := by rw [hy]; ring

private lemma reduced {v : ℚ} {b d y : ℕ} (hc : b.Coprime d) (he : v*d=(b:ℚ)*y) :
    b ∣ v.num.natAbs := by
  have hv := (div_eq_iff (Nat.cast_ne_zero.mpr v.den_ne_zero)).mp v.num_div_den
  have hh : (v.num:ℚ)*d = ((b:ℚ)*y)*v.den := by rw [hv,← he]; ring
  have hi : v.num*(d:ℤ) = ((b*y:ℕ):ℤ)*v.den := by exact_mod_cast hh
  have hn := congrArg Int.natAbs hi
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn
  apply hc.dvd_of_dvd_mul_right
  rw [hn]
  exact (dvd_mul_right b y).trans (dvd_mul_right _ _)

end PrimeShiftedMeans

open PrimeShiftedMeans

theorem OMA.solution : type_of% @OMA.S_oeis_a336838.main := by
  intro p q e hp hq hpq _ he
  obtain ⟨j,he⟩ := he
  let k := j+1
  let b := (q+1)/2
  have hk : 0<k := by dsimp [k]; omega
  have he' : e+1=2*k := by dsimp [k]; omega
  have hqodd := hq.odd_of_ne_two (by have := hp.two_le; omega)
  have hbb : q+1=2*b := by obtain ⟨s,hs⟩ := hqodd; dsimp [b]; omega
  have hq1 := hq.one_lt
  have hx : q^2 ≡ 1 [MOD b] := by
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 q hq.pos)).mpr
    have hmul : q^2-1=(q+1)*(q-1) := by
      have h₁ := Nat.sub_add_cancel (by omega : 1 ≤ q)
      have h₂ := Nat.sub_add_cancel (Nat.one_le_pow 2 q hq.pos)
      nlinarith
    rw [hmul,hbb]
    exact (dvd_mul_left b 2).trans (dvd_mul_right _ _)
  obtain ⟨y,d,hd,hc,hy⟩ := geom_mean b (q^2) hx k
  apply reduced (y:=y) hc
  have hsum : (∑ t ∈ (q^e).divisors, t) = (2*b)*geom (q^2) k := by
    rw [Nat.sum_divisors_prime_pow (f:=fun t => t) hq,he']
    change geom q (2*k) = _
    rw [geom_mul]
    have h : geom q 2=q+1 := by simp [geom,Finset.sum_range_succ,Nat.add_comm]
    rw [h,hbb]
  have hcard : (q^e).divisors.card = 2*k := by simp [Nat.divisors_prime_pow hq,he']
  rw [divisorMean,hsum,hcard]
  push_cast
  have hyr : (k:ℚ)*y=d*geom (q^2) k := by exact_mod_cast hy
  have hkr : (k:ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  linear_combination -(b:ℚ)*hyr
