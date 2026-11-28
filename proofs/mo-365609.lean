import OMAStatements.S_mo_365609

/-!
Four collinear points, at 0, 1/4, 3/4, and 1, falsify the comparison in
every positive Euclidean dimension. Every maximizing permutation has a
reversed conditional-mean comparison, independently of tie-breaking.
-/

namespace DistanceScoreCounterexample
open OMA.S_mo_365609 Finset

private abbrev P := Equiv.Perm (Fin 4)

private def x : Fin 4 → ℚ := ![0, 1/4, 3/4, 1]

private def weight (i j : Fin 4) : ℚ := 1 - |x i - x j|

private def val (p : P) : ℚ := tripleScore weight p

private noncomputable def points (d : ℕ) (i : Fin 4) : EuclideanSpace ℝ (Fin (d+1)) :=
  PiLp.single 2 0 (x i : ℝ)

private lemma distance_eq (d : ℕ) (i j : Fin 4) :
    dist (points d i) (points d j) = ((|x i - x j| : ℚ) : ℝ) := by
  rw [points, points, PiLp.dist_single_same, Real.dist_eq, Rat.cast_abs, Rat.cast_sub]

private lemma distinct_points (d : ℕ) : Function.Injective (points d) := by
  intro i j h
  have hz : dist (points d i) (points d j) = 0 := by rw [h, dist_self]
  rw [distance_eq] at hz
  have hq : |x i - x j| = 0 := by exact_mod_cast hz
  have inj : ∀ i j : Fin 4, x i = x j → i = j := by decide +kernel
  exact inj i j (sub_eq_zero.mp (abs_eq_zero.mp hq))

private lemma score_eq (d : ℕ) (p : P) : score (points d) p = (val p : ℝ) := by
  simp only [score, val, tripleScore, weight, Rat.cast_sum, distance_eq]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  split <;> simp

private lemma mean_eq (d : ℕ) (i j : Fin 4) :
    meanBefore (score (points d)) i j = ((meanBefore val i j : ℚ) : ℝ) := by
  simp [meanBefore, score_eq]

set_option maxRecDepth 16000 in
private theorem certificate :
    ∀ p : P, (∀ q : P, val q ≤ val p) →
      ∃ i j : Fin 4, p i < p j ∧ meanBefore val i j < meanBefore val j i := by
  decide +kernel

/-- Each possible choice of maximizer violates the required inequality. -/
theorem every_maximizer_fails (d : ℕ) (p : P)
    (hp : ∀ q, score (points d) q ≤ score (points d) p) :
    ∃ i j, p i < p j ∧ meanBefore (score (points d)) i j < meanBefore (score (points d)) j i := by
  have hq (q : P) : val q ≤ val p := by
    have h := hp q
    simp only [score_eq] at h
    exact_mod_cast h
  obtain ⟨i,j,hij,hm⟩ := certificate p hq
  refine ⟨i,j,hij,?_⟩
  simp only [mean_eq]
  exact_mod_cast hm

/-- In every positive dimension there is a diameter-one configuration for
which every maximizer orders some pair against its conditional mean. -/
theorem counterexample_in_dimension (d : ℕ) :
    ∃ f : Fin 4 → EuclideanSpace ℝ (Fin (d+1)), Function.Injective f ∧
      (∀ i j, dist (f i) (f j) ≤ 1) ∧ (∃ i j, dist (f i) (f j) = 1) ∧
      ∀ p : P, (∀ q, score f q ≤ score f p) →
        ∃ i j, p i < p j ∧ meanBefore (score f) i j < meanBefore (score f) j i := by
  refine ⟨points d, distinct_points d, ?_, ⟨0,3,?_⟩, every_maximizer_fails d⟩
  · intro i j
    rw [distance_eq]
    have h : ∀ i j : Fin 4, |x i-x j| ≤ 1 := by decide +kernel
    exact_mod_cast h i j
  · rw [distance_eq]
    have h : |x 0 - x 3| = 1 := by decide +kernel
    exact_mod_cast h

theorem counterexample : ¬ (type_of% @OMA.S_mo_365609.main) := by
  intro conjecture
  obtain ⟨f,hinj,hbound,hdiam,hfails⟩ := counterexample_in_dimension 0
  obtain ⟨p,_,hp⟩ := (univ : Finset P).exists_max_image (score f) univ_nonempty
  have hmax := fun q => hp q (mem_univ q)
  obtain ⟨i,j,hij,hm⟩ := hfails p hmax
  exact (not_le_of_gt hm) (conjecture 1 4 f hinj hbound hdiam p hmax i j hij)

end DistanceScoreCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365609.main) :=
  DistanceScoreCounterexample.counterexample
