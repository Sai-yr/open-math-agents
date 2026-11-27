import OMAStatements.S_oeis_a060765
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

open OMA.S_oeis_a060765

theorem OMA.solution : type_of% @OMA.S_oeis_a060765.main := by
  intro n hmem p hp hpn
  obtain ⟨hn,hgap⟩ := hmem
  let r := Nat.findGreatest (fun k => k ∣ n) (p-1)
  have hbound : 1 ≤ p-1 := by have := hp.two_le; omega
  have hrn : r ∣ n := Nat.findGreatest_spec (P := fun k => k ∣ n) hbound (one_dvd n)
  have hrpos : 0 < r := Nat.le_findGreatest (P := fun k => k ∣ n) hbound (one_dvd n)
  have hrlt : r < p := by
    have h : r ≤ p-1 := Nat.findGreatest_le _
    omega
  have hcop : p.Coprime r := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hrpos hrlt)
  have hbetween : ∀ d, d ∣ n → n/p < d → d < n/r → False := by
    intro d hd hlo hhi
    have hdd := Nat.div_dvd_of_dvd hd
    have he := Nat.div_div_self hd hn.ne'
    have h₁ : r < n/d := (Nat.div_lt_div_left hn.ne' hdd hrn).mp (by simpa only [he] using hhi)
    have h₂ : n/d < p := (Nat.div_lt_div_left hn.ne' hpn hdd).mp (by simpa only [he] using hlo)
    exact (Nat.findGreatest_is_greatest h₁ (by omega)) hdd
  have hdif := hgap (n/p) (n/r) (Nat.div_dvd_of_dvd hpn) (Nat.div_dvd_of_dvd hrn)
    ((Nat.div_lt_div_left hn.ne' hpn hrn).mpr hrlt) hbetween
  obtain ⟨k,hk⟩ := hcop.mul_dvd_of_dvd_of_dvd hpn hrn
  have hkpos : 0 < k := by
    by_contra! hzero
    have : k=0 := by omega
    simp [this] at hk
    omega
  have h₁ : n/p = r*k := Nat.div_eq_of_eq_mul_right hp.pos (by rw [hk]; ring)
  have h₂ : n/r = p*k := Nat.div_eq_of_eq_mul_right hrpos (by rw [hk]; ring)
  rw [h₁,h₂,← Nat.sub_mul,hk] at hdif
  have hcancel : p-r ∣ p*r := Nat.dvd_of_mul_dvd_mul_right hkpos hdif
  have hcp : (p-r).Coprime p := (Nat.coprime_self_sub_left hrlt.le).mpr hcop.symm
  have hcr : (p-r).Coprime r := (Nat.coprime_sub_self_left hrlt.le).mpr hcop
  have hone := (hcp.mul_right hcr).eq_one_of_dvd hcancel
  have heqr : p-1 = r := by omega
  rw [heqr,h₁]
  exact dvd_mul_right r k
