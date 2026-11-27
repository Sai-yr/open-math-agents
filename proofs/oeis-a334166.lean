import OMAStatements.S_oeis_a334166
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

open Finset OMA.S_oeis_a334166

namespace ZumkellerGaps

/-- A chosen subset contributes a specified fraction of the total divisor sum. -/
private def portion (n denominator numerator : ℕ) : Prop :=
  ∃ s ⊆ n.divisors, denominator * (∑ i ∈ s, i) = numerator * ∑ i ∈ n.divisors, i

private lemma portion_mul {m n a b c d : ℕ} (hc : m.Coprime n)
    (hm : portion m a b) (hn : portion n c d) : portion (m*n) (a*c) (b*d) := by
  obtain ⟨s, hs, he⟩ := hm
  obtain ⟨t, ht, hf⟩ := hn
  let f : ℕ × ℕ → ℕ := fun z => z.1*z.2
  have sub : s ×ˢ t ⊆ m.divisors ×ˢ n.divisors := by
    intro z hz
    exact mem_product.mpr ⟨hs (mem_product.mp hz).1, ht (mem_product.mp hz).2⟩
  refine ⟨(s ×ˢ t).image f, ?_, ?_⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
    have ⟨hm, hn⟩ := mem_product.mp (sub hz)
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp hm).1
      (Nat.mem_divisors.mp hn).1, mul_ne_zero (Nat.mem_divisors.mp hm).2 (Nat.mem_divisors.mp hn).2⟩
  · rw [sum_image (hc.mul_injOn_divisors.mono sub), sum_product, hc.sum_divisors_mul]
    change (a*c) * (∑ x ∈ s, ∑ y ∈ t, x*y) = (b*d) * ((∑ x ∈ m.divisors, x)*(∑ y ∈ n.divisors, y))
    rw [← sum_mul_sum]
    calc
      _ = (a * (∑ x ∈ s, x)) * (c * (∑ y ∈ t, y)) := by ring
      _ = _ := by rw [he, hf]; ring

private lemma sums_in_pairs (p m : ℕ) :
    (p+1) * (∑ j ∈ range m, p^(2*j+1)) = p * ∑ i ∈ range (2*m), p^i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = 2*m+1+1 by omega, sum_range_succ, sum_range_succ (f := fun i => p^i),
      sum_range_succ (f := fun i => p^i)]
    rw [show p^(2*m+1) = p^(2*m)*p by rw [pow_succ]]
    nlinarith only [ih]

private lemma prime_portion (p : ℕ) (hp : p.Prime) (m : ℕ) :
    portion (p^(2*m+1)) (p+1) p := by
  let f : ℕ → ℕ := fun j => p^(2*j+1)
  refine ⟨(range (m+1)).image f, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow _ (by have := mem_range.mp hj; omega : 2*j+1 ≤ 2*m+1),
      pow_ne_zero _ hp.ne_zero⟩
  · have inj : Function.Injective f := by
      intro i j hij
      have h := (Nat.pow_right_injective hp.one_lt) hij
      omega
    rw [sum_image inj.injOn, Nat.sum_divisors_prime_pow hp]
    exact (show 2*(m+1) = 2*m+1+1 by omega) ▸ sums_in_pairs p (m+1)

private lemma six_square (w : ℕ) (hw : 0 < w) : Zumkeller (6*w^2) := by
  obtain ⟨a, u, h2u, hwu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hw.ne' 2 (by decide)
  have hu : u ≠ 0 := by rintro rfl; simp at hwu; omega
  obtain ⟨b, v, h3v, huv⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu 3 (by decide)
  have h2v : ¬2 ∣ v := fun h => h2u (huv ▸ dvd_mul_of_dvd_right h _)
  have c23 : (2^(2*a+1)).Coprime (3^(2*b+1)) :=
    ((by decide : Nat.Coprime 2 3).pow_left _).pow_right _
  have cv : (2^(2*a+1)*3^(2*b+1)).Coprime (v^2) :=
    (((Nat.prime_two.coprime_iff_not_dvd.mpr h2v).pow_left _).mul_left
      ((Nat.prime_three.coprime_iff_not_dvd.mpr h3v).pow_left _)).pow_right _
  have htot : portion (v^2) 1 1 := ⟨_, fun _ h => h, rfl⟩
  obtain ⟨s, hs, he⟩ := portion_mul cv
    (portion_mul c23 (prime_portion 2 Nat.prime_two a) (prime_portion 3 Nat.prime_three b)) htot
  have hfac : 6*w^2 = (2^(2*a+1)*3^(2*b+1))*v^2 := by
    rw [hwu, huv]
    simp only [pow_succ, pow_mul', mul_pow]
    ring
  refine ⟨by positivity, s, hfac ▸ hs, ?_⟩
  rw [hfac]
  have split := sum_sdiff (f := fun i : ℕ => i) hs
  omega

theorem gap (x y : ℕ) (_hx : member x) (_hy : member y) (_h : x < y)
    (hnext : ∀ z : ℕ, x < z → z < y → ¬member z) : y ≤ x+6 := by
  by_contra! h
  let w := x/6+1
  have hxw : x < 6*w := by dsimp [w]; omega
  have hwy : 6*w < y := by dsimp [w]; omega
  apply hnext (6*w) hxw hwy
  have hw : 0 < w := Nat.succ_pos _
  refine ⟨w, Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, by positivity⟩, ?_⟩
  convert six_square w hw using 1
  ring

end ZumkellerGaps

theorem OMA.solution : type_of% @OMA.S_oeis_a334166.main := ZumkellerGaps.gap
