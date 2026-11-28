import OMAStatements.S_oeis_a375786

/-!
# Lexicographically least edges attain minimum volume

An odd cube edge permits a cuboid with two edges 1. An even cube edge
permits one with two edges 2. For fixed shortest edge, volume increases
with the second shortest edge. For three edges at least two the volume
plus four is at least half the surface area, with equality when the first
two edges are both two. These comparisons cover every possible competitor.
-/
namespace A375786Proof
open OMA.S_oeis_a375786

private theorem exists_least (n : ℕ) (hn : 0<n) :
    ∃ a b c, admissible n a b c ∧ leastSides n a b := by
  classical
  have cube : admissible n n n n := ⟨hn,le_rfl,le_rfl,by ring⟩
  have ex : ∃ a : ℕ, ∃ b c, admissible n a b c := ⟨n,n,n,cube⟩
  let a:=Nat.find ex
  have exb : ∃ b : ℕ, ∃ c, admissible n a b c := Nat.find_spec ex
  let b:=Nat.find exb
  obtain ⟨c,hc⟩:=Nat.find_spec exb
  refine ⟨a,b,c,hc,?_⟩
  intro x y z hg
  have low : a≤x := Nat.find_min' ex ⟨y,z,hg⟩
  rcases low.lt_or_eq with hl|rfl
  · exact Or.inl hl
  · exact Or.inr ⟨rfl,Nat.find_min' exb ⟨z,hg⟩⟩

private theorem equal_pair (n : ℕ) (hn : 0<n) :
    ∃ d z : ℕ, d≤2 ∧ admissible n d d z := by
  rcases Nat.even_or_odd n with ⟨q,hq⟩|⟨q,hq⟩
  · have qp : 0<q := by omega
    have hq2 : 1≤q^2 := Nat.pos_of_ne_zero (pow_ne_zero _ qp.ne')
    refine ⟨2,3*q^2-1,by decide,by decide,le_rfl,by omega,?_⟩
    rw [hq]
    have e : 3*q^2-1+1=3*q^2 := by omega
    nlinarith
  · refine ⟨1,6*q^2+6*q+1,by decide,by decide,le_rfl,by omega,?_⟩
    rw [hq]; ring

private theorem volume_lower {x y z : ℕ} (hx : 2≤x) (hy : 2≤y) (hz : 2≤z) :
    x*y+x*z+y*z ≤ x*y*z+4 := by
  obtain ⟨i,rfl⟩ : ∃ i, x=i+2 := ⟨x-2,by omega⟩
  obtain ⟨j,rfl⟩ : ∃ j, y=j+2 := ⟨y-2,by omega⟩
  obtain ⟨k,rfl⟩ : ∃ k, z=k+2 := ⟨z-2,by omega⟩
  nlinarith [Nat.zero_le (i*j*k),Nat.zero_le (i*j),Nat.zero_le (i*k),Nat.zero_le (j*k)]

private theorem fixed_edge {a b c y z : ℕ} (ha : 0<a) (hb : b≤y) (hz : y≤z)
    (h : a*b+a*c+b*c=a*y+a*z+y*z) : a*b*c ≤ a*y*z := by
  suffices le : b*c≤y*z by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a le
  zify at ha hb hz h ⊢
  have e : ((a:ℤ)+b)*((y:ℤ)*z-(b:ℤ)*c) =
      (a:ℤ)*((y:ℤ)-b)*((z:ℤ)-b) := by linear_combination -(b:ℤ)*h
  have hp : (0:ℤ) ≤ (a:ℤ)*((y:ℤ)-b)*((z:ℤ)-b) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have h0 : (0:ℤ) ≤ (y:ℤ)*z-(b:ℤ)*c :=
    nonneg_of_mul_nonneg_right (e.symm ▸ hp) (by omega)
  omega

private theorem least_volume {n a b c : ℕ} (hn : 0<n) (abc : admissible n a b c)
    (least : leastSides n a b) (x y z : ℕ) (xyz : admissible n x y z) :
    a*b*c ≤ x*y*z := by
  obtain ⟨d,w,hd,trial⟩:=equal_pair n hn
  have small := least _ _ _ trial
  have order := least _ _ _ xyz
  obtain ⟨ha,hab,hbc,hs⟩:=abc
  obtain ⟨hx,hxy,hyz,ht⟩:=xyz
  have same : a*b+a*c+b*c=x*y+x*z+y*z := by omega
  by_cases e : a=x
  · subst x
    exact fixed_edge ha (by omega) hyz same
  have hl : 2≤x := by omega
  have lower := volume_lower hl (by omega : 2≤y) (by omega : 2≤z)
  by_cases a1 : a=1
  · subst a
    simp only [one_mul] at same ⊢
    have bc : 4≤b+c := by
      by_contra! h
      have b2 : b≤2 := by omega
      have c2 : c≤2 := by omega
      have up := Nat.mul_le_mul b2 c2
      have l1 := Nat.mul_le_mul hl (show 2≤y by omega)
      have l2 := Nat.mul_le_mul hl (show 2≤z by omega)
      have l3 := Nat.mul_le_mul (show 2≤y by omega) (show 2≤z by omega)
      omega
    omega
  · have a2 : a=2 := by omega
    have b2 : b=2 := by omega
    subst a; subst b
    omega

end A375786Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a375786.main := by
  intro n hn
  exact ⟨A375786Proof.exists_least n hn,fun _ _ _ hab hs=>A375786Proof.least_volume hn hab hs⟩

