import OMAStatements.S_oeis_a014865
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

open OMA.S_oeis_a014865

namespace FifteenDivisibility

private lemma step (n : ℕ) : s (n+1) = 15*s n + (n+1) := by
  cases n <;> rfl

private lemma closed (n : ℕ) : 196*s n + 14*n + 15 = 15^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [step, pow_succ 15 (n+1), ← ih]
    ring

/-- Squaring lifts the congruence modulo one additional power of two. -/
private lemma two_part (j : ℕ) :
    ∃ w : ℕ, 15^(2^(j+1)) = 1+2^(j+3)*w := by
  induction j with
  | zero => exact ⟨28, by decide⟩
  | succ j ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w + 2^(j+2)*w^2, ?_⟩
    rw [show 2^(j+1+1) = 2^(j+1)*2 by ring, pow_mul, hw]
    simp only [pow_succ]
    ring

private lemma lift_power {x m : ℕ} (h : ∃ w, x = 1+m*w) (u : ℕ) :
    ∃ w, x^u = 1+m*w := by
  obtain ⟨b, rfl⟩ := h
  induction u with
  | zero => exact ⟨0, by simp⟩
  | succ u ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨a+b+m*a*b, by rw [pow_succ, ha]; ring⟩

private lemma odd_term {n : ℕ} (h : IsTerm n) : Odd n := by
  obtain ⟨v, u, hu, hform⟩ := Nat.exists_eq_two_pow_mul_odd h.1.ne'
  cases v with
  | zero => simpa [hform] using hu
  | succ j =>
    obtain ⟨w, hw⟩ := lift_power (two_part j) u
    have hpow : 15^n = 1+2^(j+3)*w := by rw [hform, pow_mul]; exact hw
    obtain ⟨d, hd⟩ := h.2
    have hclosed := closed n
    rw [hd, pow_succ, hpow, hform,
      show 2^(j+3) = 4*2^(j+1) by ring] at hclosed
    have heq : 2^(j+1)*(196*u*d+14*u) = 2^(j+1)*(60*w) := by
      nlinarith only [hclosed]
    have hcoeff := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^(j+1)) heq
    obtain ⟨a, ha⟩ := hu
    have himp (x t z : ℕ) : 196*x+14*(2*t+1) ≠ 60*z := by omega
    exact (himp (u*d) a w (by rw [← ha, ← Nat.mul_assoc]; exact hcoeff)).elim

private lemma one_of_three {n : ℕ} (h : IsTerm n) (hn : 1 < n) :
    3 ∣ n ∨ 5 ∣ n ∨ 7 ∣ n := by
  by_contra! hnone
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd _
  have hps := hpn.trans h.2
  let : Fact p.Prime := ⟨hp⟩
  have nonzero : (15 : ZMod p) ≠ 0 := by
    intro h15
    have hd := (ZMod.natCast_eq_zero_iff 15 p).mp h15
    have hd' : p ∣ 3*5 := hd
    rcases hp.dvd_mul.mp hd' with h3 | h5
    · rcases (Nat.dvd_prime Nat.prime_three).mp h3 with he | he
      · exact hp.ne_one he
      · exact hnone.1 (he ▸ hpn)
    · rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp h5 with he | he
      · exact hp.ne_one he
      · exact hnone.2.1 (he ▸ hpn)
  have zn := (ZMod.natCast_eq_zero_iff n p).mpr hpn
  have zs := (ZMod.natCast_eq_zero_iff (s n) p).mpr hps
  have zc := congrArg (fun t : ℕ => (t : ZMod p)) (closed n)
  push_cast at zc
  rw [zn, zs, pow_succ] at zc
  have zpow : (15 : ZMod p)^n = 1 := by
    apply mul_right_cancel₀ nonzero
    simpa using zc.symm
  have ho1 := orderOf_dvd_of_pow_eq_one zpow
  have ho2 := ZMod.orderOf_dvd_card_sub_one nonzero
  have pg := hp.two_le
  have hc : n.gcd (p-1) = 1 :=
    Nat.gcd_eq_one_of_lt_minFac (by omega) (show p-1 < p by omega)
  have hord := Nat.dvd_gcd ho1 ho2
  rw [hc, Nat.dvd_one] at hord
  have zone := orderOf_eq_one_iff.mp hord
  have h14 : (14 : ZMod p) = 0 := by linear_combination zone
  have pd14 : p ∣ 2*7 := (ZMod.natCast_eq_zero_iff 14 p).mp h14
  rcases hp.dvd_mul.mp pd14 with hd | hd
  · rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact hp.ne_one he
    · have ht : 2 ∣ n := he ▸ hpn
      exact (Nat.not_even_iff_odd.mpr (odd_term h)) (even_iff_two_dvd.mpr ht)
  · rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with he | he
    · exact hp.ne_one he
    · exact hnone.2.2 (he ▸ hpn)

end FifteenDivisibility

theorem OMA.solution : type_of% @OMA.S_oeis_a014865.main := by
  refine ⟨fun _ => FifteenDivisibility.odd_term, ?_, fun _ => FifteenDivisibility.one_of_three⟩
  intro k hk hk7 hp
  rcases FifteenDivisibility.one_of_three hk (by omega) with hd | hd | hd
  all_goals rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
