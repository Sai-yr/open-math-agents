import OMAStatements.S_oeis_a037096

/-!
# The polynomial divisibility conjecture for A037096

For n at least three, shifting the index of a power of three by 2^(n-2)
flips bit n. Consequently the half-column consists of a block followed by
its complement, and the full column repeats the half-column. In characteristic
two each repetition supplies a power of X+1. The complemented block supplies
the remaining factor through the geometric sum of a power-of-two length.
-/
namespace A037096Proof
open OMA.S_oeis_a037096 Finset Polynomial

private theorem power_three (s : ℕ) :
    ∃ t : ℕ,3^(2^(s+1))=1+2^(s+3)*(2*t+1) := by
  induction s with
  | zero => exact ⟨0,by decide⟩
  | succ s ih =>
    obtain ⟨t,h⟩ := ih
    refine ⟨t+2^(s+1)*(2*t+1)^2,?_⟩
    rw [show s+1+1=(s+1)+1 by rfl,pow_succ (2:ℕ) (s+1),pow_mul,h]
    simp only [pow_succ]; ring

private theorem flip (s k : ℕ) :
    digit (s+3) (k+2^(s+1))=digit (s+3) k+1 := by
  obtain ⟨t,ht⟩ := power_three s
  have he : 3^(k+2^(s+1))=3^k+2^(s+3)*(3^k*(2*t+1)) := by rw [pow_add,ht]; ring
  rw [digit,he,Nat.add_mul_div_left _ _ (by positivity),digit]
  simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [show (3:ZMod 2)=1 by decide,show (2:ZMod 2)=0 by decide]
  simp

private theorem repeats (s k : ℕ) :
    digit (s+3) (k+2*2^(s+1))=digit (s+3) k := by
  rw [show k+2*2^(s+1)=(k+2^(s+1))+2^(s+1) by ring,flip,flip]
  have H : (1:ZMod 2)+1=0 := by decide
  rw [add_assoc,H,add_zero]

private theorem frob (b : ℕ) : (X+1:R)^(2^b)=1+X^(2^b) := by
  simpa [add_comm] using add_pow_char_pow (X:R) 1 2 b

private theorem geom (h : ℕ) :
    (∑ k ∈ range (2^h),(X:R)^k)=(X+1)^(2^h-1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    let q := 2^h
    have hq : 0<q := by dsimp [q]; positivity
    rw [pow_succ, Nat.mul_two,sum_range_add]
    simp_rw [pow_add]
    rw [←mul_sum,ih]
    change (X+1:R)^(q-1)+X^q*(X+1)^(q-1)=(X+1)^(q+q-1)
    rw [←one_add_mul,←frob h,←pow_add]
    congr 1; omega

private theorem split_column (n a : ℕ) :
    column n (a+a)=column n a+(X:R)^a*∑ k ∈ range a,C (digit n (k+a))*X^k := by
  rw [column,sum_range_add,column,mul_sum]
  congr 1; apply sum_congr rfl; intro k _
  rw [pow_add,add_comm a k]; ring

private theorem factor (s : ℕ) : ∃ q : R,
    column (s+3) (2^(s+2))=(X+1)^(2^(s+1)-1)*q ∧
    column (s+3) (2^(s+3))=(X+1)^(3*2^(s+1)-1)*q := by
  let m := 2^(s+1)
  let B := column (s+3) m
  let D : R := X+1
  have hm : 0< m := by dsimp [m]; positivity
  have HG : (∑ k ∈ range m,(X:R)^k)=D^(m-1) := geom (s+1)
  have half : column (s+3) (2^(s+2))=D^(m-1)*(D*B+X^m) := by
    rw [show (2:ℕ)^(s+2)=m+m by dsimp [m]; rw [pow_succ (2:ℕ) (s+1)]; omega,split_column]
    have comp : (∑ k ∈ range m, C (digit (s+3) (k+m))*(X:R)^k)=B+D^(m-1) := by
      dsimp only [m] at *
      simp_rw [flip,map_add,map_one,add_mul,one_mul]
      rw [sum_add_distrib,HG]
      rfl
    rw [comp]
    change B+X^m*(B+D^(m-1))=_
    have H1 : (1+(X:R)^m)=D^m := (frob (s+1)).symm
    have H2 : D^m=D^(m-1)*D := by rw [←pow_succ,show m-1+1=m by omega]
    calc B+X^m*(B+D^(m-1)) = (1+X^m)*B+D^(m-1)*X^m := by ring
         _ = _ := by rw [H1,H2]; ring
  refine ⟨D*B+X^m,half,?_⟩
  have h2 : (2:ℕ)^(s+2)=2*m := by dsimp [m]; rw [pow_succ']
  rw [show (2:ℕ)^(s+3)=2^(s+2)+2^(s+2) by rw [pow_succ (2:ℕ) (s+2)]; omega,split_column]
  have rep (k : ℕ) : digit (s+3) (k+2^(s+2))=digit (s+3) k := by rw [h2]; exact repeats s k
  simp_rw [rep]
  change column (s+3) (2^(s+2))+X^(2^(s+2))*column (s+3) (2^(s+2))=_
  rw [←one_add_mul,←frob (s+2),half,←mul_assoc,←pow_add]
  change D^(2^(s+2)+(m-1))*(D*B+X^m)=D^(3*m-1)*(D*B+X^m)
  rw [h2,show 2*m+(m-1)=3*m-1 by omega]

end A037096Proof

open OMA.S_oeis_a037096 A037096Proof Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a037096.main := by
  intro n hn
  obtain ⟨s,rfl⟩ : ∃ s,n=s+3 := ⟨n-3,by omega⟩
  obtain ⟨q,hh,hf⟩ := factor s
  have e : s+3-2=s+1 := by omega
  have e' : s+3-1=s+2 := by omega
  rw [e]
  refine ⟨⟨q,hf⟩,?_⟩
  have hne : (X+1:R)≠0 := by
    intro h
    have hh := congrArg (fun p : R=>p.coeff 0) h
    simp at hh
  rw [quotient,e,e',hh,mul_div_cancel_left₀ _ (pow_ne_zero _ hne),hf]

