import OMAStatements.S_oeis_a057923

namespace OMA.S_oeis_a057923

private theorem or_and (x y : ℕ) : (x ||| y) + (x &&& y) = x+y := by
  induction x using Nat.binaryRec generalizing y with
  | zero => simp
  | bit b x ih =>
    induction y using Nat.binaryRec with
    | zero => simp
    | bit c y _ =>
      have h := ih y
      rw [Nat.lor_bit,Nat.land_bit]
      cases b <;> cases c <;> simp [Nat.bit] <;> omega

-- Clearing shared bits leaves the OR unchanged. Minimality forces
-- the chosen term to have had no such bits.
private theorem greedy_sum (y t : ℕ) : y ||| pick y t = y + pick y t := by
  let z := pick y t
  let w := Nat.ldiff z y
  have hsame : y ||| w = y ||| z := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [w,Nat.testBit_or,Nat.testBit_ldiff]
    cases y.testBit i <;> cases z.testBit i <;> rfl
  have hle : w ≤ z := by
    apply Nat.le_of_testBit
    intro i hi
    simp only [w,Nat.testBit_ldiff,Bool.and_eq_true] at hi
    exact hi.1
  have hz : z = w := by
    apply Nat.le_antisymm _ hle
    apply Nat.find_min' (candidate y t)
    rw [hsame]
    exact Nat.find_spec (candidate y t)
  have hdis : y &&& z = 0 := by
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [hz]
    simp only [w,Nat.testBit_and,Nat.testBit_ldiff]
    cases y.testBit i <;> cases z.testBit i <;> rfl
  simpa only [hdis,Nat.add_zero] using or_and y z

private theorem adjacent (n : ℕ) : (pair n).1 ||| (pair n).2 = (pair n).1 + (pair n).2 := by
  cases n with
  | zero => decide
  | succ n => exact greedy_sum _ _

end OMA.S_oeis_a057923

open OMA.S_oeis_a057923 in
theorem OMA.solution : type_of% @OMA.S_oeis_a057923.main := by
  intro n
  let x := (pair n).1
  let y := (pair n).2
  let z := pick y (x ||| y)
  have h : x ||| y < y ||| z := Nat.find_spec (candidate y (x ||| y))
  have hx : x ||| y = x+y := adjacent n
  have hy : y ||| z = y+z := greedy_sum y (x ||| y)
  rw [hx,hy] at h
  change x < z
  omega
