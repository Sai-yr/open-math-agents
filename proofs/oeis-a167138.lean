import OMAStatements.S_oeis_a167138
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Tactic

open OMA.S_oeis_a167138 PowerSeries

namespace LogarithmicMoments

private noncomputable def T (f : ℕ → ℂ) (n : ℕ) : ℂ := coeff n (transform f)
private def shift (f : ℕ → ℂ) (i : ℕ) := f (i+1)

private lemma constant (f : ℕ → ℂ) : T f 0 = f 0 := by
  unfold T transform
  rw [coeff_subst' HasSubst.log, finsum_eq_single _ 0]
  · simp [egf]
  · intro i hi
    rw [coeff_zero_eq_constantCoeff_apply,map_pow,constantCoeff_log,zero_pow hi]
    simp

private lemma deriv_egf (f : ℕ → ℂ) : derivative ℂ (egf f) = egf (shift f) := by
  ext n
  rw [coeff_derivative]
  simp [egf,shift,Nat.factorial_succ]
  field_simp

private lemma log_inv : (1+X)*(derivative ℂ (log ℂ))=1 := by
  rw [deriv_log,add_mul,one_mul]
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ n => simp [coeff_succ_X_mul,pow_succ]

private lemma recurrence (f : ℕ → ℂ) (n : ℕ) :
    T f (n+1)*((n:ℂ)+1) = T (shift f) n - n*T f n := by
  have hh : (1+X)*(derivative ℂ (transform f)) = transform (shift f) := by
    unfold transform
    rw [derivative_subst HasSubst.log,deriv_egf,mul_left_comm (1+X),log_inv,mul_one]
  rw [add_mul,one_mul] at hh
  have he := congrArg (coeff n) hh
  simp only [map_add,coeff_derivative] at he
  cases n with
  | zero => simpa [T,coeff_zero_eq_constantCoeff_apply] using he
  | succ n =>
    rw [coeff_succ_X_mul,coeff_derivative] at he
    change T f (n+1+1)*((↑(n+1):ℂ)+1) + T f (n+1)*(n+1)=T (shift f) (n+1) at he
    push_cast at he ⊢
    linear_combination he

private lemma linear (f g : ℕ → ℂ) (c : ℂ) (n : ℕ) :
    T (fun i => c*f i+g i) n = c*T f n+T g n := by
  have he : egf (fun i => c*f i+g i)=c • egf f + egf g := by
    ext j
    simp [egf,add_div]
    ring
  simp [T,transform,he,subst_add HasSubst.log,subst_smul HasSubst.log,smul_eq_mul]

private lemma zero (n : ℕ) : T (fun _ => 0) n=0 := by
  have h := linear (fun _=>0) (fun _=>0) 1 n
  simp only [one_mul,zero_add] at h
  linear_combination -h

private lemma geometric (j n : ℕ) : T (fun i => (j:ℂ)^i) n = j.choose n := by
  induction n with
  | zero => simp [constant]
  | succ n ih =>
    have he := recurrence (fun i => (j:ℂ)^i) n
    have hsh : T (shift (fun i => (j:ℂ)^i)) n = (j:ℂ)*T (fun i=>(j:ℂ)^i) n := by
      change T (fun i => (j:ℂ)^(i+1)) n = _
      simpa [pow_succ',zero] using linear (fun i => (j:ℂ)^i) (fun _=>0) j n
    rw [hsh,ih] at he
    apply mul_right_cancel₀ (show ((n:ℂ)+1) ≠ 0 by exact_mod_cast n.succ_ne_zero)
    rw [he]
    by_cases hn : n ≤ j
    · have hc := congrArg (fun t : ℕ => (t:ℂ)) (Nat.choose_succ_right_eq j n)
      push_cast [Nat.cast_sub hn] at hc
      linear_combination -hc
    · simp [Nat.choose_eq_zero_of_lt (by omega : j<n),Nat.choose_eq_zero_of_lt (by omega : j<n+1)]

private lemma triangular (n : ℕ) (f g : ℕ → ℂ) (h : ∀ i<n, f i=g i) :
    (n.factorial:ℂ)*(T f n-T g n)=f n-g n := by
  induction n generalizing f g with
  | zero => simp [constant]
  | succ n ih =>
    have h₁ := ih f g (fun i hi => h i (by omega))
    rw [h n (by omega),sub_self,mul_eq_zero] at h₁
    have hfg : T f n=T g n := sub_eq_zero.mp (h₁.resolve_left (Nat.cast_ne_zero.mpr n.factorial_ne_zero))
    have hs := ih (shift f) (shift g) (fun i hi => h (i+1) (by omega))
    simp only [shift] at hs
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hf := recurrence f n
    have hg := recurrence g n
    rw [← hfg] at hg
    linear_combination (n.factorial:ℂ)*(hf-hg)+hs

private abbrev Weights := MonoidAlgebra ℤ ℕ

private noncomputable def momentAt (i : ℕ) : Weights →ₐ[ℤ] ℂ :=
  MonoidAlgebra.lift ℤ ℂ ℕ ((powMonoidHom i).comp (Nat.castRingHom ℂ).toMonoidHom)

private noncomputable def moment (w : Weights) (i : ℕ) := momentAt i w

private lemma adjust (w : Weights) (j : ℕ) (z : ℤ) (n : ℕ) :
    T (moment (MonoidAlgebra.single j z+w)) n = (z:ℂ)*j.choose n+T (moment w) n := by
  have he : moment (MonoidAlgebra.single j z+w) = fun i => (z:ℂ)*(j:ℂ)^i+moment w i := by
    funext i
    simp [moment,momentAt,MonoidAlgebra.lift_single]
  rw [he,linear,geometric]

private lemma weight_integral (w : Weights) (n : ℕ) : ∃ z : ℤ, T (moment w) n=z := by
  induction w using MonoidAlgebra.induction with
  | zero =>
    have h : moment 0 = (fun _ => 0) := by funext i; simp [moment]
    exact ⟨0,by rw [h,zero]; simp⟩
  | single_add j r w _ _ ih =>
    obtain ⟨z,hz⟩ := ih
    exact ⟨r*j.choose n+z,by rw [adjust,hz]; push_cast; rfl⟩

private lemma interpolate (f : ℕ → ℂ) (hint : integralSeries (transform f)) (lo count : ℕ) :
    ∃ w : Weights, ∀ i, lo ≤ i → i < lo+count → T (moment w) i = T f i := by
  induction count generalizing lo with
  | zero => exact ⟨0,fun i h₁ h₂ => by omega⟩
  | succ count ih =>
    obtain ⟨w,hw⟩ := ih (lo+1)
    obtain ⟨z,hz⟩ := hint lo
    change T f lo=z at hz
    obtain ⟨v,hv⟩ := weight_integral w lo
    refine ⟨MonoidAlgebra.single lo (z-v)+w,?_⟩
    intro i hlo hhi
    rw [adjust]
    rcases eq_or_lt_of_le hlo with rfl | hlt
    · simp [hv,hz]
    · simp [Nat.choose_eq_zero_of_lt hlt,hw i (by omega) (by omega)]

private lemma recover {f g : ℕ → ℂ} {N : ℕ} (h : ∀ i ≤ N, T f i=T g i) (i : ℕ) (hi : i ≤ N) : f i=g i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hh := triangular i f g fun j hj => ih j hj (by omega)
    rw [h i hi,sub_self,mul_zero] at hh
    exact sub_eq_zero.mp hh.symm

end LogarithmicMoments

open LogarithmicMoments

theorem OMA.solution : type_of% @OMA.S_oeis_a167138.main := by
  intro f hint m _ n
  obtain ⟨w,hw⟩ := interpolate f hint 0 (n+1)
  have hfit (i : ℕ) (hi : i≤n) : moment w i = f i := recover (N:=n) (fun j hj => hw j (by omega) (by omega)) i hi
  have hp (i : ℕ) (hi : i≤n) : moment (w^m) i = f i ^ m := by
    have h₁ := hfit i hi
    simpa only [moment,map_pow] using congrArg (fun z : ℂ => z^m) h₁
  obtain ⟨z,hz⟩ := weight_integral (w^m) n
  refine ⟨z,?_⟩
  change T (fun i => f i^m) n=z
  have hh := triangular n (moment (w^m)) (fun i => f i^m) fun j hj => hp j hj.le
  rw [hp n le_rfl,sub_self,mul_eq_zero] at hh
  exact (sub_eq_zero.mp (hh.resolve_left (Nat.cast_ne_zero.mpr n.factorial_ne_zero))).symm.trans hz
