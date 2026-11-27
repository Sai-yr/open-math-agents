import OMAStatements.S_oeis_a140831
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

open OMA.S_oeis_a140831

namespace InvertedFactors

private lemma witness {n p q : ℕ} (hn : 0<n) (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hsize : q < p^2) (hs : p^2 ∣ n) (hd : q ∣ n) (he : ¬ q^2 ∣ n) : inversion n := by
  have hpe := (hp.pow_dvd_iff_le_factorization hn.ne').mp hs
  have hq₁ := hq.factorization_pos_of_dvd hn.ne' hd
  have hq₂ : n.factorization q < 2 := by
    exact lt_of_not_ge (fun h => he ((hq.pow_dvd_iff_le_factorization hn.ne').mpr h))
  have hqe : n.factorization q=1 := by omega
  refine ⟨hn,p,q,hp,hq,hpq,(dvd_pow_self p (by decide : 2 ≠ 0)).trans hs,hd,?_⟩
  rw [hqe,pow_one]
  exact hsize.trans_le (Nat.pow_le_pow_right hp.pos hpe)

end InvertedFactors

theorem OMA.solution : type_of% @OMA.S_oeis_a140831.main := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  let k := 44100*m+28524
  refine ⟨k,?_,by dsimp [k]; omega⟩
  constructor
  · apply InvertedFactors.witness (p:=2) (q:=3) (by dsimp [k]; omega) (by decide) (by decide) (by decide) (by decide)
    · change 4 ∣ 44100*m+28524; omega
    · change 3 ∣ 44100*m+28524; omega
    · change ¬ 9 ∣ 44100*m+28524; omega
  · apply InvertedFactors.witness (p:=5) (q:=7) (by dsimp [k]; omega) (by decide) (by decide) (by decide) (by decide)
    · change 25 ∣ 44100*m+28524+1; omega
    · change 7 ∣ 44100*m+28524+1; omega
    · change ¬ 49 ∣ 44100*m+28524+1; omega
