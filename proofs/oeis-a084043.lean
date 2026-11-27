import OMAStatements.S_oeis_a084043
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open OMA.S_oeis_a084043

namespace DecimalPalindromes

private lemma periodic_powers (n : ℕ) (hn : 0 < n) : ∃ s p : ℕ, 0 < p ∧
    ∀ j t : ℕ, 10^(s+j+p*t) ≡ 10^(s+j) [MOD n] := by
  let f (i : ℕ) : Fin n := ⟨10^i % n, Nat.mod_lt _ hn⟩
  obtain ⟨x,y,hne,heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hh : 10^x ≡ 10^y [MOD n] := congrArg Fin.val heq
  have hc : ∃ a b : ℕ, a < b ∧ 10^b ≡ 10^a [MOD n] := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨x,y,h,hh.symm⟩
    · exact ⟨y,x,h,hh⟩
  obtain ⟨s,b,hs,hb⟩ := hc
  let p := b-s
  have he : s+p=b := by dsimp [p]; omega
  refine ⟨s,p,by dsimp [p]; omega,?_⟩
  intro j t
  induction t with
  | zero => simp [Nat.ModEq]
  | succ t ih =>
    have step := hb.mul_right (10^(j+p*t))
    rw [← pow_add, ← pow_add] at step
    rw [show s+j+p*(t+1) = b+(j+p*t) by rw [Nat.mul_succ]; omega]
    exact step.trans (by simpa [Nat.add_assoc] using ih)

private def copies (v : List ℕ) (k : ℕ) := (List.replicate k v).flatten

private lemma copies_succ (v : List ℕ) (k : ℕ) : copies v (k+1) = v ++ copies v k := by
  simp [copies, List.replicate_succ]

private lemma copies_pal {v : List ℕ} (hv : v.reverse=v) (k : ℕ) :
    (copies v k).reverse = copies v k := by
  simp [copies, List.reverse_flatten, hv]

private lemma copies_mem {d : ℕ} {v : List ℕ} {k : ℕ} (h : d ∈ copies v k) : d ∈ v := by
  obtain ⟨u,hu,hd⟩ := List.mem_flatten.mp h
  simpa [List.eq_of_mem_replicate hu] using hd

private lemma copies_mod {n : ℕ} (v : List ℕ)
    (hs : 10^v.length * Nat.ofDigits 10 v ≡ Nat.ofDigits 10 v [MOD n]) (k : ℕ) :
    Nat.ofDigits 10 (copies v k) ≡ k * Nat.ofDigits 10 v [MOD n] := by
  induction k with
  | zero => simp [copies, Nat.ModEq]
  | succ k ih =>
    rw [copies_succ, Nat.ofDigits_append, Nat.succ_mul]
    have h := (ih.mul_left (10^v.length)).trans (by
      simpa only [mul_left_comm] using hs.mul_left k)
    simpa [Nat.add_comm] using h.add_left (Nat.ofDigits 10 v)

private lemma last_eq_head {v : List ℕ} (hp : v.reverse=v) (hn : v ≠ []) :
    v.getLast hn = v.head! := by
  have hlast : v.getLast hn = v.head hn := by
    calc v.getLast hn = v.reverse.getLast (by simpa [hp] using hn) := by simp [hp]
         _ = v.head hn := List.getLast_reverse _
  cases v with
  | nil => contradiction
  | cons a l => simpa using hlast

private lemma witness {n : ℕ} (hn : 0 < n) (h10 : ¬ 10 ∣ n) : ∃ m, admissible n m := by
  let ds := Nat.digits 10 n
  have hds : ds ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  obtain ⟨first,tail,hfirst⟩ := List.exists_cons_of_ne_nil hds
  have hfirst0 : first ≠ 0 := by
    have h := Nat.head!_digits (n := n) (b := 10) (by decide)
    change ds.head! = n%10 at h
    simp [hfirst] at h
    exact h ▸ fun hz => h10 (Nat.dvd_of_mod_eq_zero hz)
  obtain ⟨s,p,hp,hperiod⟩ := periodic_powers n hn
  let t := s + 2*ds.length + 1
  let z := p*t - 2*ds.length
  have hbig : t ≤ p*t := Nat.le_mul_of_pos_left t hp
  have hlen : 2*ds.length+z = p*t := by dsimp [t,z] at *; omega
  have hstart : s ≤ ds.length+z := by dsimp [t,z] at *; omega
  let zeros := List.replicate z 0
  let v := ds ++ zeros ++ ds.reverse
  have hvlen : v.length = p*t := by
    simp only [v, zeros, List.length_append, List.length_replicate, List.length_reverse]
    omega
  have hvpal : v.reverse=v := by simp [v,zeros,List.reverse_append,List.append_assoc]
  have hvne : v ≠ [] := by simp [v,hds]
  have hval : Nat.ofDigits 10 v = n+10^(ds.length+z)*Nat.ofDigits 10 ds.reverse := by
    simp [v,zeros,Nat.ofDigits_append,Nat.ofDigits_replicate_zero,ds,Nat.ofDigits_digits,pow_add,Nat.mul_assoc]
  have hl : Nat.ofDigits 10 v ≡ 10^(ds.length+z)*Nat.ofDigits 10 ds.reverse [MOD n] := by
    rw [hval]
    simp [Nat.ModEq]
  have hs := hperiod (ds.length+z-s) t
  rw [show s+(ds.length+z-s) = ds.length+z by omega, ← hvlen] at hs
  have hstable : 10^v.length*Nat.ofDigits 10 v ≡ Nat.ofDigits 10 v [MOD n] := by
    calc 10^v.length*Nat.ofDigits 10 v
        ≡ 10^v.length*(10^(ds.length+z)*Nat.ofDigits 10 ds.reverse) [MOD n] := hl.mul_left _
      _ = 10^(ds.length+z+v.length)*Nat.ofDigits 10 ds.reverse := by rw [pow_add]; ring
      _ ≡ 10^(ds.length+z)*Nat.ofDigits 10 ds.reverse [MOD n] := hs.mul_right _
      _ ≡ Nat.ofDigits 10 v [MOD n] := hl.symm
  let k := 2*n-2
  have hk : k+2=2*n := by dsimp [k]; omega
  let word := copies v (k+2)
  have hwp := copies_pal hvpal (k+2)
  have hwhead : word.head! = first := by
    simp [word,copies_succ,v,hfirst]
  have hwne : word ≠ [] := by simp [word,copies_succ,hvne]
  have hbounded : ∀ d ∈ word, d < 10 := by
    intro d hd
    have hv := copies_mem hd
    simp only [v, List.mem_append, List.mem_reverse] at hv
    rcases hv with (hd | hz) | hd
    · exact Nat.digits_lt_base (by decide) hd
    · have hd0 := List.eq_of_mem_replicate hz
      omega
    · exact Nat.digits_lt_base (by decide) hd
  have hdigits : Nat.digits 10 (Nat.ofDigits 10 word) = word := by
    apply Nat.digits_ofDigits 10 (by decide) word hbounded
    intro hne
    rw [last_eq_head hwp hne, hwhead]
    exact hfirst0
  have hwpos : 0 < Nat.ofDigits 10 word := Nat.pos_of_ne_zero
    (Nat.digits_ne_nil_iff_ne_zero.mp (hdigits ▸ hwne))
  have hwmod := copies_mod v hstable (k+2)
  change Nat.ofDigits 10 word ≡ (k+2)*Nat.ofDigits 10 v [MOD n] at hwmod
  rw [hk] at hwmod
  have hdiv : n ∣ Nat.ofDigits 10 word := Nat.modEq_zero_iff_dvd.mp
    (hwmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)))
  refine ⟨Nat.ofDigits 10 word,hwpos,hdiv,by simpa only [hdigits] using hwp,?_⟩
  refine ⟨v, (zeros++ds.reverse)++copies v k, hvne, by simp [hds], ?_⟩
  rw [hdigits]
  change copies v (k+2) = v ++ ds ++ ((zeros++ds.reverse)++copies v k)
  simp only [copies_succ, List.append_assoc, v]

private lemma no_multiple_ten {n m : ℕ} (hn : 10 ∣ n) (h : admissible n m) : False := by
  obtain ⟨hm,hd,hp,_⟩ := h
  have hs := Nat.head!_digits (n := m) (b := 10) (by decide)
  rw [Nat.mod_eq_zero_of_dvd (hn.trans hd)] at hs
  have hw := Nat.getLast_digit_ne_zero 10 hm.ne'
  rw [last_eq_head hp _, hs] at hw
  exact hw rfl

end DecimalPalindromes

theorem OMA.solution : type_of% @OMA.S_oeis_a084043.main := by
  classical
  intro n hn
  by_cases h : 10 ∣ n
  · have hx : ¬ ∃ m, admissible n m := fun ⟨_,hm⟩ => DecimalPalindromes.no_multiple_ten h hm
    simp [a,hx,h]
  · obtain hw := DecimalPalindromes.witness hn h
    have hf : 0 < Nat.find hw := (Nat.find_spec hw).1
    simp [a,hw,h,hf.ne']
