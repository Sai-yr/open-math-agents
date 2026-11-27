import OMAStatements.S_oeis_a036284
/-!
# Both factor conjectures for Fibonacci bit columns

At level n ≥ 2, shifting the Fibonacci index by half of the column length
changes bit n by the parity of the unshifted Fibonacci number. This parity
has period three. Its block polynomial is X+X², which supplies the extra
factor X+1 after the geometric sum has supplied the power of X³+1.
-/
namespace A036284Proof
open OMA.S_oeis_a036284 Finset Polynomial

private theorem addition (s : ℕ) : ∃ a b : ℕ, ∀ k : ℕ,
    Nat.fib (k+3*2^(s+1)) =
      (1+2^(s+2)*(2*a+1))*Nat.fib k+(2^(s+3)*b)*Nat.fib (k+1) := by
  induction s with
  | zero =>
    refine ⟨0,1,fun k=>?_⟩
    change Nat.fib (k+6)=5*Nat.fib k+8*Nat.fib (k+1)
    rw [Nat.fib_add_two (n:=k+4),Nat.fib_add_two (n:=k+3),Nat.fib_add_two (n:=k+2),
      Nat.fib_add_two (n:=k+1),Nat.fib_add_two (n:=k)]
    ring
  | succ s ih =>
    obtain ⟨a,b,H⟩ := ih
    let A := 1+2^(s+2)*(2*a+1)
    let B := 2^(s+3)*b
    let M := 3*2^(s+1)
    change ∀ k, Nat.fib (k+M)=A*Nat.fib k+B*Nat.fib (k+1) at H
    refine ⟨a+2^s*(2*a+1)^2+2^(s+2)*b^2,A*b+2^(s+2)*b^2,fun k=>?_⟩
    have he : k+3*2^(s+1+1)=(k+M)+M := by dsimp [M]; rw [pow_succ (2:ℕ) (s+1)]; ring
    rw [he,H (k+M),H k,show k+M+1=(k+1)+M by omega,H (k+1),Nat.fib_add_two]
    dsimp only [A,B]
    simp only [pow_succ]; ring

private theorem shifted_bit (s k : ℕ) :
    digit (s+2) (k+3*2^(s+1))=digit (s+2) k+(Nat.fib k:ZMod 2) := by
  obtain ⟨a,b,H⟩ := addition s
  have he : Nat.fib (k+3*2^(s+1)) =
      Nat.fib k+2^(s+2)*((2*a+1)*Nat.fib k+2*b*Nat.fib (k+1)) := by
    rw [H,pow_succ (2:ℕ) (s+2)]; ring
  rw [digit,he,Nat.add_mul_div_left _ _ (by positivity),digit]
  simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    show (2:ZMod 2)=0 by decide,zero_mul,zero_add,one_mul,add_zero]

private theorem parity_shift (k : ℕ) : (Nat.fib (k+3):ZMod 2)=(Nat.fib k:ZMod 2) := by
  rw [Nat.fib_add_two (n:=k+1),Nat.fib_add_two (n:=k)]
  push_cast
  have h : (2:ZMod 2)=0 := by decide
  linear_combination (Nat.fib (k+1):ZMod 2)*h

private theorem parity_all (m j : ℕ) : (Nat.fib (3*m+j):ZMod 2)=(Nat.fib j:ZMod 2) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show 3*(m+1)+j=(3*m+j)+3 by ring,parity_shift,ih]




private theorem frob (Y : R) (h : ℕ) : (Y+1)^(2^h)=1+Y^(2^h) := by
  simpa [add_comm] using add_pow_char_pow Y 1 2 h

private theorem geom (Y : R) (h : ℕ) :
    (∑ k ∈ range (2^h),Y^k)=(Y+1)^(2^h-1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    let q := 2^h
    have hq : 0<q := by dsimp [q]; positivity
    rw [pow_succ,Nat.mul_two,sum_range_add]
    simp_rw [pow_add]; rw [←mul_sum,ih]
    change (Y+1)^(q-1)+Y^q*(Y+1)^(q-1)=(Y+1)^(q+q-1)
    rw [←one_add_mul,←frob Y h,←pow_add]; congr 1; omega

private theorem parity_poly (m : ℕ) :
    (∑ k ∈ range (3*m),C (Nat.fib k:ZMod 2)*(X:R)^k) =
      (X+X^2)*∑ t ∈ range m,(X^3:R)^t := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ (n:=m)]
    simp_rw [parity_all,pow_add]
    have block : (∑ x ∈ range 3,C (Nat.fib x:ZMod 2)*(X^(3*m)*(X:R)^x)) =
        (X+X^2)*X^(3*m) := by
      simp [sum_range_succ,Nat.fib_add_two]; ring
    rw [block,←pow_mul]; ring

private noncomputable def initial (n d : ℕ) : R := ∑ k ∈ range d,C (digit n k)*X^k

private theorem divides_prefix (n d : ℕ) : (X:R) ∣ initial n d := by
  apply dvd_sum
  intro k _
  cases k with
  | zero => simp [digit]
  | succ k => exact ⟨C (digit n (k+1))*X^k,by rw [pow_succ]; ring⟩

private theorem factor_large (s : ℕ) : ∃ q : R, column (s+2) =
    factor (s+2)*(X*(X+1)*q) := by
  let m := 2^(s+1)
  let M := 3*m
  let D : R := X^3+1
  let B := initial (s+2) M
  have hm : 0< m := by dsimp [m]; positivity
  have hM : 3*2^(s+2)=M+M := by dsimp [M,m]; rw [pow_succ (2:ℕ) (s+1)]; ring
  have hP : column (s+2)=B+X^M*(B+(X+X^2)*D^(m-1)) := by
    rw [column,hM,sum_range_add]
    have he (k : ℕ) : C (digit (s+2) (M+k))*(X:R)^(M+k)=
        X^M*(C (digit (s+2) k)*X^k+C (Nat.fib k:ZMod 2)*X^k) := by
      rw [show M+k=k+3*2^(s+1) by dsimp [M,m]; omega,shifted_bit,map_add,pow_add]
      ring
    simp_rw [he]
    rw [←mul_sum,sum_add_distrib,show (∑ k ∈ range M,C (Nat.fib k:ZMod 2)*(X:R)^k)=
      (X+X^2)*D^(m-1) by rw [parity_poly m,geom _ (s+1)]]
    rfl
  obtain ⟨b,hb⟩ := divides_prefix (s+2) M
  change B=X*b at hb
  have hD : (1+(X:R)^M)=D^m := by
    dsimp only [M,m,D]; rw [frob,←pow_mul]
  have hD' : D^m = D^(m-1)*D := by rw [←pow_succ,show m-1+1=m by omega]
  have hcube : D=(X+1)*(X^2-X+1) := by dsimp [D]; ring
  refine ⟨(X^2-X+1)*b+X^M,?_⟩
  rw [OMA.S_oeis_a036284.factor,show s+2-1=s+1 by omega]
  change column (s+2)=D^(m-1)*(X*(X+1)*_)
  rw [hP]
  calc B+X^M*(B+(X+X^2)*D^(m-1)) = (1+X^M)*B+(X+X^2)*D^(m-1)*X^M := by ring
       _ = _ := by rw [hD,hD',hb,hcube]; ring

private theorem factor_one : ∃ q : R, column 1 = factor 1*(X*(X+1)*q) := by
  refine ⟨X^2,?_⟩
  norm_num [column,OMA.S_oeis_a036284.factor,digit,sum_range_succ,Nat.fib_add_two]
  ring_nf
  simp [show (2:R)=0 from CharP.cast_eq_zero R 2]

end A036284Proof

open OMA.S_oeis_a036284 A036284Proof Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a036284.main := by
  intro n hn
  have h : ∃ q : R, column n=factor n*(X*(X+1)*q) := by
    by_cases he : n=1
    · simpa only [he] using factor_one
    · obtain ⟨s,rfl⟩ : ∃ s,n=s+2 := ⟨n-2,by omega⟩
      exact factor_large s
  obtain ⟨q,hq⟩ := h
  have hnz : (X^3+1:R)≠0 := by
    intro h
    have q := congrArg (fun p : R=>p.coeff 0) h
    simp [coeff_zero_eq_eval_zero] at q
  have hf : factor n≠0 := pow_ne_zero _ hnz
  rw [hq,mul_div_cancel_left₀ _ hf]
  exact ⟨dvd_mul_right _ _,rfl,dvd_mul_right _ _⟩

