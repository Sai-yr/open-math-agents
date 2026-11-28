import OMAStatements.S_oeis_a386829

/-!
# A second-order recurrence for Manyama's binomial sum

Expanding the nth power of 3x+2x² and integrating each monomial
identifies the binomial sum with a multiple of the nth integral moment.
Integrating the derivative of (3+4x)(3x+2x²)^(n+1) relates successive
moments. The central binomial recurrence then eliminates the boundary
term between two consecutive instances.
-/

namespace A386829Proof
open OMA.S_oeis_a386829 Finset MeasureTheory

private noncomputable def moment (n : ℕ) := ∫ x : ℝ in 0..1, (3*x+2*x^2)^n

private theorem binomial_term (n k : ℕ) (hk : k ≤ n) :
    ((2*n-k+1)*((2*n+1).choose k)*(2*n-k).choose (n-k)) =
      (2*n+1)*n.centralBinom*n.choose k := by
  have h1 := Nat.choose_mul_succ_eq (2*n-k) (n-k)
  have e : 2*n-k+1 = 2*n+1-k := by omega
  rw [show 2*n-k+1-(n-k)=n+1 by omega,e] at h1
  have h2 := Nat.choose_mul (n:=2*n+1) hk
  have h3 := Nat.choose_mul_succ_eq (2*n) n
  rw [show 2*n+1-n=n+1 by omega] at h3
  unfold Nat.centralBinom
  calc
    _ = (2*n+1).choose k * ((2*n-k).choose (n-k) * (2*n+1-k)) := by rw [←e]; ring
    _ = ((2*n+1).choose k * (2*n+1-k).choose (n-k))*(n+1) := by rw [h1]; ring
    _ = ((2*n+1).choose n*(n+1))*n.choose k := by rw [←h2]; ring
    _ = _ := by rw [←h3]; ring

private def weight (n k : ℕ) : ℝ := 3^k*2^(n-k)*n.choose k

private theorem moment_expansion (n : ℕ) : moment n =
    ∑ k ∈ range (n+1), weight n k / ((2*n-k:ℕ)+1:ℝ) := by
  have expn (x : ℝ) : (3*x+2*x^2)^n =
      ∑ k ∈ range (n+1), weight n k*x^(2*n-k) := by
    rw [add_pow]
    apply sum_congr rfl; intro k hk
    have he : k+2*(n-k)=2*n-k := by have := mem_range.mp hk; omega
    unfold weight
    rw [mul_pow,mul_pow,←pow_mul,←he,pow_add]; ring
  unfold moment
  simp_rw [expn]
  rw [intervalIntegral.integral_finsetSum (f:=fun k x=>weight n k*x^(2*n-k))
        (by intro k hk; apply Continuous.intervalIntegrable; fun_prop)]
  apply sum_congr rfl; intro k _
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp only [one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero]
  ring

private theorem scaled (n : ℕ) : (a n:ℝ) = (2*(n:ℝ)+1)*(n.centralBinom:ℝ)*moment n := by
  rw [moment_expansion,mul_sum,a]
  push_cast
  apply sum_congr rfl; intro k hk
  have h := binomial_term n k (by have := mem_range.mp hk; omega)
  have h' : (((2*n-k:ℕ):ℝ)+1)*((2*n+1).choose k:ℝ)*((2*n-k).choose (n-k):ℝ) =
      (2*(n:ℝ)+1)*(n.centralBinom:ℝ)*(n.choose k:ℝ) := by exact_mod_cast h
  have hp : (0:ℝ) < ((2*n-k:ℕ):ℝ)+1 := by positivity
  unfold weight
  rw [←mul_div_assoc,eq_div_iff hp.ne']
  linear_combination (3:ℝ)^k*(2:ℝ)^(n-k)*h'

end A386829Proof

namespace A386829Proof
open OMA.S_oeis_a386829 Finset MeasureTheory

private theorem moment_step (n : ℕ) :
    4*(2*(n:ℝ)+3)*moment (n+1)+9*((n:ℝ)+1)*moment n=7*5^(n+1) := by
  let f := fun x : ℝ => 3*x+2*x^2
  let g := fun x : ℝ => (3+4*x)*(f x)^(n+1)
  let u := fun x : ℝ => 4*(2*(n:ℝ)+3)*(f x)^(n+1)
  let v := fun x : ℝ => 9*((n:ℝ)+1)*(f x)^n
  have hf (x : ℝ) : HasDerivAt f (3+4*x) x := by
    have h := ((hasDerivAt_id x).const_mul 3).add (((hasDerivAt_id x).pow 2).const_mul 2)
    convert! h using 1
    simp
    ring
  have hd (x : ℝ) : HasDerivAt g (u x+v x) x := by
    have h₁ := ((hasDerivAt_id x).const_mul 4).const_add 3
    have h₂ := (hf x).pow (n+1)
    convert! h₁.mul h₂ using 1
    dsimp [f,u,v]; push_cast; rw [pow_succ]; ring
  have hu : Continuous u := by dsimp [u,f]; fun_prop
  have hv : Continuous v := by dsimp [v,f]; fun_prop
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1)
    (fun x _=>hd x) ((hu.add hv).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hu.intervalIntegrable _ _) (hv.intervalIntegrable _ _)] at hft
  change (∫ x : ℝ in 0..1, 4*(2*(n:ℝ)+3)*(f x)^(n+1)) +
    (∫ x : ℝ in 0..1, 9*((n:ℝ)+1)*(f x)^n) = g 1-g 0 at hft
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hft
  change 4*(2*(n:ℝ)+3)*moment (n+1)+9*((n:ℝ)+1)*moment n=g 1-g 0 at hft
  norm_num [g,f] at hft ⊢
  exact hft

private theorem central_step (n : ℕ) :
    ((n:ℝ)+1)*((n+1).centralBinom:ℝ)=2*(2*(n:ℝ)+1)*(n.centralBinom:ℝ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

private theorem step (n : ℕ) : 4*(a (n+1):ℝ)+18*(a n:ℝ) =
    7*5^(n+1)*((n+1).centralBinom:ℝ) := by
  rw [scaled,scaled]
  push_cast
  linear_combination ((n+1).centralBinom:ℝ)*moment_step n - 9*moment n*central_step n

private theorem solved : ∀ n : ℕ, 2 ≤ n →
    2*(n:ℤ)*(a n:ℤ) + (-31*(n:ℤ)+20)*(a (n-1):ℤ) +
    90*(-2*(n:ℤ)+1)*(a (n-2):ℤ) = 0 := by
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2,by omega⟩
  rw [show m+2-1=m+1 by omega,show m+2-2=m by omega]
  have h : 2*((m:ℝ)+2)*(a (m+2):ℝ)+(-31*((m:ℝ)+2)+20)*(a (m+1):ℝ) +
      90*(-2*((m:ℝ)+2)+1)*(a m:ℝ)=0 := by
    have h₁ := step (m+1)
    have h₂ := step m
    have h₃ := central_step (m+1)
    push_cast at h₃
    rw [pow_succ (5:ℝ) (m+1)] at h₁
    linear_combination ((m:ℝ)+2)/2*h₁ - 5*(2*(m:ℝ)+3)*h₂ + (35/2)*5^(m+1)*h₃
  exact_mod_cast h

end A386829Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386829.main :=
  A386829Proof.solved
