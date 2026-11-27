import OMAStatements.S_oeis_a361281
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

open Finset PowerSeries OMA.S_oeis_a361281

namespace ScaledExponential

-- A factor of constant term 1 and zero derivative disappears after taking
-- any derivative and then its constant coefficient.
private lemma insensitive {R : Type*} [CommRing R] (F Q : PowerSeries R)
    (hc : constantCoeff Q = 1) (hd : derivative R Q = 0) (n j : ℕ) :
    (n.descFactorial j : R) * coeff j (F*Q) = (n.descFactorial j : R) * coeff j F := by
  have hi (i : ℕ) : (derivative R)^[i] (F*Q) = (derivative R)^[i] F * Q := by
    induction i with
    | zero => rfl
    | succ i ih => simp [Function.iterate_succ_apply', ih, Derivation.leibniz, hd, smul_eq_mul, mul_comm]
  have he := congrArg (constantCoeff (R:=R)) (hi j)
  rw [map_mul, hc, mul_one, constantCoeff_iterate_derivative, constantCoeff_iterate_derivative] at he
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  linear_combination (n.choose j : R) * he

private lemma period (k t n : ℕ) (F G : PowerSeries (ZMod k)) (hG : constantCoeff G=1) :
    scaledCoeff F G (n+k*t) = scaledCoeff F G n := by
  let s := k*t
  have hs : (s : ZMod k) = 0 := by simp [s]
  have hd (j : ℕ) : ((n+s).descFactorial j : ZMod k) = (n.descFactorial j : ZMod k) := by
    rw [← descPochhammer_eval_eq_descFactorial (ZMod k), ← descPochhammer_eval_eq_descFactorial (ZMod k)]
    simp [hs]
  have term (j : ℕ) :
      ((n+s).descFactorial j : ZMod k) * coeff j (F*G^((n+s)*(n+s-j))) =
        (n.descFactorial j : ZMod k) * coeff j (F*G^(n*(n-j))) := by
    rw [hd]
    by_cases hj : j ≤ n
    · let w := n+(n-j)+s
      have ex : (n+s)*(n+s-j) = n*(n-j) + s*w := by
        have sub : n+s-j = n-j+s := by omega
        rw [sub]
        dsimp [w]
        ring
      rw [ex,pow_add,← mul_assoc]
      apply insensitive
      · simp [hG]
      · have hz : (s*w : PowerSeries (ZMod k)) = 0 := by
          have h := congrArg (C (R:=ZMod k)) hs
          simpa using congrArg (fun x : PowerSeries (ZMod k) => x * w) h
        rw [derivative_pow,Nat.cast_mul,hz,zero_mul,zero_mul]
    · simp [Nat.descFactorial_of_lt (lt_of_not_ge hj)]
  unfold scaledCoeff
  change (∑ j ∈ range (n+s+1), _) = _
  calc
    _ = ∑ j ∈ range (n+s+1), (n.descFactorial j : ZMod k) * coeff j (F*G^(n*(n-j))) :=
      sum_congr rfl fun j _ => term j
    _ = _ := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j _ hj
      simp only [mem_range,not_lt] at hj
      simp [Nat.descFactorial_of_lt (show n<j by omega)]

private lemma map_scaled {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (F G : PowerSeries R) (n : ℕ) :
    f (scaledCoeff F G n) = scaledCoeff (map f F) (map f G) n := by
  simp only [scaledCoeff,map_sum,map_mul,map_natCast]
  apply sum_congr rfl
  intro j _
  rw [← coeff_map,map_mul,map_pow]

private lemma coeff_special (m j : ℕ) :
    coeff j ((1+(X : PowerSeries ℤ))^m) = (m.choose j : ℤ) := by
  simpa only [Polynomial.coe_pow,Polynomial.coe_add,Polynomial.coe_one,Polynomial.coe_X,
    Polynomial.coeff_coe] using
      (show coeff j ((((1+Polynomial.X)^m : Polynomial ℤ) : PowerSeries ℤ)) = _ from
        (Polynomial.coeff_coe _ _).trans (Polynomial.coeff_one_add_X_pow ℤ m j))

private lemma special (n : ℕ) : scaledCoeff 1 (1+(X : PowerSeries ℤ)) n = (a n : ℤ) := by
  simp [scaledCoeff,a,coeff_special]

end ScaledExponential

theorem OMA.solution : type_of% @OMA.S_oeis_a361281.main := by
  have general (F G : PowerSeries ℤ) (hG : constantCoeff G = 1) (n k t : ℕ) :
      ((scaledCoeff F G (n+k*t) : ℤ) : ZMod k) = ((scaledCoeff F G n : ℤ) : ZMod k) := by
    change Int.castRingHom (ZMod k) _ = Int.castRingHom (ZMod k) _
    rw [ScaledExponential.map_scaled,ScaledExponential.map_scaled]
    apply ScaledExponential.period
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hG, map_one]
  have specific (n k t : ℕ) : (a (n+k*t) : ZMod k) = (a n : ZMod k) := by
    simpa [ScaledExponential.special] using
      general 1 (1+(X : PowerSeries ℤ)) (by simp) n k t
  refine ⟨fun F G h n k => by simpa using general F G h n k 1,
    fun n k => by simpa using specific n k 1, ?_, ?_⟩
  · intro n
    have periodic := specific (n%4) 4 (n/4)
    rw [Nat.mod_add_div] at periodic
    have initial : ∀ i : Fin 4, (a i : ZMod 4) = 1 := by decide
    exact periodic.trans (initial ⟨n%4,Nat.mod_lt _ (by decide)⟩)
  · intro n
    have periodic := specific 2 5 n
    rw [Nat.add_comm] at periodic
    exact periodic.trans (by decide : (a 2 : ZMod 5) = 0)
