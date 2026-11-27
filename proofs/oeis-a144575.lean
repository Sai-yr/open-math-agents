import OMAStatements.S_oeis_a144575
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

open Filter Topology
open scoped ContDiff
namespace RadicalExponential

private def Q (l x : ℝ) := 1-2*x-l*x^2
private def T (l x : ℝ) := 1+l*x
private noncomputable def F (l x : ℝ) := Real.exp (1-Real.sqrt (Q l x))
private noncomputable def H (l x : ℝ) := F l x / Real.sqrt (Q l x)
private noncomputable abbrev A (l : ℝ) (n : ℕ) := iteratedDeriv n (F l)
private noncomputable abbrev B (l : ℝ) (n : ℕ) := iteratedDeriv n (H l)

private theorem ht (l x : ℝ) : HasDerivAt (T l) l x := by
  unfold T
  simpa only [mul_one] using! ((hasDerivAt_id x).const_mul l).const_add 1

private theorem hq (l x : ℝ) : HasDerivAt (Q l) (-2*T l x) x := by
  unfold Q T
  convert! ((((hasDerivAt_id x).const_mul 2).const_sub 1).sub
    (((hasDerivAt_id x).pow 2).const_mul l)) using 1
  simp only [id_eq]
  ring

private theorem nearby {l x : ℝ} (hx : 0 < Q l x) : ∀ᶠ y in 𝓝 x, 0 < Q l y :=
  (hq l x).continuousAt.eventually (Ioi_mem_nhds hx)

private theorem smoothF {l x : ℝ} (hx : 0 < Q l x) : ContDiffAt ℝ ∞ (F l) x := by
  have s : ContDiffAt ℝ ∞ (fun y => Real.sqrt (Q l y)) x :=
    (by unfold Q; fun_prop : ContDiffAt ℝ ∞ (Q l) x).sqrt hx.ne'
  exact (contDiffAt_const.sub s).exp

private theorem smoothH {l x : ℝ} (hx : 0 < Q l x) : ContDiffAt ℝ ∞ (H l) x := by
  apply (smoothF hx).div
  · exact (by unfold Q; fun_prop : ContDiffAt ℝ ∞ (Q l) x).sqrt hx.ne'
  · exact (Real.sqrt_pos.mpr hx).ne'

private theorem jet {f : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n+1) f x) x := by
  have sm (k : ℕ) : ContDiffAt ℝ ∞ (iteratedDeriv k f) x := by
    induction k with
    | zero => simpa using h
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.derivWithin (by simp)
  rw [iteratedDeriv_succ]
  exact ((sm n).differentiableAt (by simp)).hasDerivAt

private theorem base {l x : ℝ} (hx : 0 < Q l x) :
    A l 1 x = T l x * H l x ∧ Q l x * B l 1 x = T l x * (F l x + H l x) := by
  have s := (hq l x).sqrt hx.ne'
  have f := (s.const_sub 1).exp
  have h := f.div s (Real.sqrt_pos.mpr hx).ne'
  have hs := Real.sq_sqrt hx.le
  have hn := (Real.sqrt_pos.mpr hx).ne'
  have df : deriv (F l) x = _ := f.deriv
  have dh : deriv (H l) x = _ := h.deriv
  simp only [A,B,iteratedDeriv_one,df,dh,H,F]
  generalize Real.exp (1-Real.sqrt (Q l x)) = e
  generalize hz : Real.sqrt (Q l x) = z at hs hn ⊢
  rw [← hs]
  constructor <;> field_simp
  ring

private theorem compare {f g : ℝ → ℝ} {x a b : ℝ} (eq : f =ᶠ[𝓝 x] g)
    (ha : HasDerivAt f a x) (hb : HasDerivAt g b x) : a=b :=
  (ha.congr_of_eventuallyEq eq.symm).unique hb

private theorem jetsA {l : ℝ} (n : ℕ) : ∀ x : ℝ, 0 < Q l x →
    A l (n+2) x = T l x * B l (n+1) x + l*((n:ℝ)+1)* B l n x := by
  induction n with
  | zero =>
    intro x hx
    have eq := (nearby hx).mono (fun y hy => (base hy).1)
    have h := compare eq (jet (smoothF hx) 1) ((ht l x).mul (jet (smoothH hx) 0))
    simpa [A,B,add_comm,mul_comm] using h
  | succ n ih =>
    intro x hx
    have h := compare ((nearby hx).mono ih) (jet (smoothF hx) (n+2))
      (((ht l x).mul (jet (smoothH hx) (n+1))).add
        ((jet (smoothH hx) n).const_mul (l*((n:ℝ)+1))))
    push_cast
    linear_combination h

private theorem jetsB {l : ℝ} (n : ℕ) : ∀ x : ℝ, 0 < Q l x →
    Q l x * B l (n+2) x = (2*(n:ℝ)+3)*T l x*B l (n+1) x +
      l*((n:ℝ)+1)^2*B l n x + T l x*A l (n+1) x + l*((n:ℝ)+1)*A l n x := by
  induction n with
  | zero =>
    intro x hx
    have eq := (nearby hx).mono (fun y hy => (base hy).2)
    have h := compare eq ((hq l x).mul (jet (smoothH hx) 1))
      ((ht l x).mul ((jet (smoothF hx) 0).add (jet (smoothH hx) 0)))
    simp only [iteratedDeriv_zero] at *
    push_cast
    linear_combination h
  | succ n ih =>
    intro x hx
    have dB := jet (smoothH hx)
    have dA := jet (smoothF hx)
    have h := compare ((nearby hx).mono ih) ((hq l x).mul (dB (n+2)))
      ((((((ht l x).const_mul (2*(n:ℝ)+3)).mul (dB (n+1))).add
          ((dB n).const_mul (l*((n:ℝ)+1)^2))).add ((ht l x).mul (dA (n+1)))).add
          ((dA n).const_mul (l*((n:ℝ)+1))))
    push_cast
    linear_combination h

theorem recurrence (l : ℝ) (n : ℕ) : A l (n+4) 0 - (2*(n:ℝ)+5)*A l (n+3) 0 -
    (l*(n:ℝ)^2+4*l*n+3*l+1)*A l (n+2) 0 - l*(2*(n:ℝ)+5)*A l (n+1) 0 -
    l^2*((n:ℝ)+3)*(n+1)*A l n 0 = 0 := by
  have J (m : ℕ) := jetsA (l:=l) m 0 (by simp [Q])
  have K (m : ℕ) := jetsB (l:=l) m 0 (by simp [Q])
  simp only [Q,T,mul_zero,zero_pow (by decide : 2≠0),sub_zero,add_zero,one_mul,mul_one] at J K
  rw [J (n+2),J (n+1),J n,K (n+1),K n,J n]
  push_cast
  ring

end RadicalExponential

theorem OMA.solution : type_of% @OMA.S_oeis_a144575.main := by
  intro n
  have h := RadicalExponential.recurrence 3 n
  have coeff (m : ℕ) : RadicalExponential.A 3 m 0 = OMA.S_oeis_a144575.a m := rfl
  simp_rw [coeff] at h
  linear_combination h
