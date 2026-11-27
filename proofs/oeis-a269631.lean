import OMAStatements.S_oeis_a269631
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

open Finset OMA.S_oeis_a269631

namespace DigitLengthGreedy

private lemma length_pos (n : ℕ) : 0 < (digits n).length := by
  by_cases hn : n=0
  · simp [digits,hn]
  · simp [digits,hn,Nat.length_digits 10 n (by decide) hn]

private def prefixNumber (d L j : ℕ) := j+10^L*d

/-- Put the positive integer d at the front, padding the remaining L positions
with zeros followed by the digits of j. Mathlib lists these in reverse order. -/
private lemma prefix_digits {d L j : ℕ} (hd : 0<d) (hj : j<10^L) :
    (digits d).IsInfix (digits (prefixNumber d L j)) ∧
    (digits (prefixNumber d L j)).length = L+(digits d).length := by
  have hlen := (Nat.digits_length_le_iff (b:=10) (k:=L) (by decide) j).mpr hj
  let k := L-(Nat.digits 10 j).length
  have hadd : (Nat.digits 10 j).length+k=L := by dsimp [k]; omega
  have hrepr := Nat.digits_append_zeroes_append_digits (by decide : 1<10) hd (n:=j) (k:=k)
  rw [hadd] at hrepr
  have hp : prefixNumber d L j ≠ 0 := by unfold prefixNumber; positivity
  rw [show digits d = Nat.digits 10 d from if_neg hd.ne',
    show digits (prefixNumber d L j) = Nat.digits 10 (prefixNumber d L j) from if_neg hp,
    prefixNumber, ← hrepr]
  refine ⟨⟨Nat.digits 10 j ++ List.replicate k 0, [], by simp⟩,?_⟩
  simp only [List.length_append, List.length_replicate]
  omega

private lemma exists_eligible (seen : Finset ℕ) (prev : ℕ) : ∃ x, eligible seen prev x := by
  let d := (digits prev).length
  let B := seen.sup id
  let L := (Nat.digits 10 B).length
  have hpos : 0 < 10^L*d := Nat.mul_pos (by positivity) (length_pos prev)
  have hbig : B < prefixNumber d L B := by unfold prefixNumber; omega
  exact ⟨_,fun h => hbig.not_ge (le_sup (f:=id) h),
    (prefix_digits (length_pos prev) (Nat.lt_base_pow_length_digits (b:=10) (by decide))).1⟩

private lemma chosen (n : ℕ) : eligible (state n).2 (a n) (a (n+1)) := by
  classical
  change eligible _ _ (next (state n).2 (a n))
  simpa [next, dif_pos (exists_eligible ..)] using Nat.find_spec (exists_eligible (state n).2 (a n))

private lemma least {n x : ℕ} (h : eligible (state n).2 (a n) x) : a (n+1) ≤ x := by
  classical
  change next (state n).2 (a n) ≤ _
  simpa [next, dif_pos (exists_eligible ..)] using Nat.find_min' (exists_eligible ..) h

private lemma history (n : ℕ) : (state n).2 = (range (n+1)).image a := by
  induction n with
  | zero => simp [state,range_add_one,a]
  | succ n ih => rw [range_add_one,image_insert,← ih]; rfl

private lemma injective : Function.Injective a := by
  have neq (i j : ℕ) (hij : i<j) : a i ≠ a j := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    intro eq
    have hf := (chosen n).1
    rw [history] at hf
    exact hf (mem_image.mpr ⟨i,mem_range.mpr hij,eq⟩)
  intro i j h
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact (neq i j hlt h).elim
  · exact he
  · exact (neq j i hgt h.symm).elim

private lemma large (B : ℕ) : ∃ i, B ≤ a i := by
  have hfin : (a ⁻¹' Set.Iio B).Finite := (Set.finite_Iio B).preimage injective.injOn
  obtain ⟨M,hM⟩ := hfin.bddAbove
  refine ⟨M+1,?_⟩
  by_contra! h
  have := hM (show M+1 ∈ a ⁻¹' Set.Iio B from h)
  omega

private lemma room {t : ℕ} (ht : 2≤t) : t<10^(t/2) := by
  have grow (j : ℕ) : 2*j+3 < 10^(j+1) := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ]; omega
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t/2 ≠ 0)
  have := grow j
  rw [hj]
  omega

theorem permutation : Function.Bijective a := by
  classical
  refine ⟨injective,?_⟩
  intro t
  change t ∈ Set.range a
  by_cases ht : t<2
  · interval_cases t
    · exact ⟨0,rfl⟩
    · have e : eligible (state 0).2 (a 0) 1 :=
        ⟨by decide,List.infix_refl _⟩
      have hl : a 1 ≤ 1 := least e
      have hn : a 1 ≠ 0 := fun h => (by decide : 1 ≠ 0) (injective (show a 1 = a 0 from h))
      exact ⟨1,by omega⟩
  by_contra absent
  have hskip (i : ℕ) : t ∉ (state i).2 := by
    rw [history]
    intro h
    obtain ⟨k,_,hk⟩ := mem_image.mp h
    exact absent ⟨k,hk⟩
  have hB := large (10^t)
  have first_pos : Nat.find hB ≠ 0 := by
    intro he
    have hh := Nat.find_spec hB
    rw [he] at hh
    change 10^t ≤ 0 at hh
    have : 0 < 10^t := by positivity
    omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero first_pos
  have big : 10^t ≤ a (n+1) := by
    have h := Nat.find_spec hB
    change 10^t ≤ a (Nat.find hB) at h
    rwa [hn] at h
  have small : a n < 10^t := lt_of_not_ge (Nat.find_min hB (by omega : n < Nat.find hB))
  let d := (digits (a n)).length
  have hd : 0<d := length_pos _
  have hdt : d≤t := by
    by_cases hz : a n = 0
    · simp [d,digits,hz]; omega
    · simpa [d,digits,hz] using (Nat.digits_length_le_iff (by decide : 1<10) (a n)).mpr small
  let L := t-(digits d).length
  have hroom := room (by omega : 2≤t)
  have hlen : (digits d).length ≤ t/2 := by
    simpa [digits,hd.ne'] using (Nat.digits_length_le_iff (by decide : 1<10) d).mpr (hdt.trans_lt hroom)
  have htail : t < 10^L := hroom.trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [L]; omega))
  let w (j : Fin (t+1)) := prefixNumber d L j.val
  have hwords (j : Fin (t+1)) : (digits d).IsInfix (digits (w j)) ∧
      (digits (w j)).length = t := by
    have h := prefix_digits hd (show j.val<10^L by have := j.isLt; omega)
    exact ⟨h.1,h.2.trans (by dsimp [L]; omega)⟩
  have occur (j : Fin (t+1)) : ∃ i, a i = w j := by
    by_cases hs : w j ∈ (state n).2
    · rw [history] at hs
      obtain ⟨i,_,hi⟩ := mem_image.mp hs
      exact ⟨i,hi⟩
    · have hh := least (n:=n) (x:=w j) ⟨hs,(hwords j).1⟩
      have pos : w j ≠ 0 := by dsimp [w,prefixNumber]; positivity
      have hlen := (hwords j).2
      simp only [digits,if_neg pos] at hlen
      have hlim := Nat.lt_base_pow_length_digits (b:=10) (m:=w j) (by decide)
      rw [hlen] at hlim
      exact (hlim.not_ge (big.trans hh)).elim
  choose I hI using occur
  have hlow (j : Fin (t+1)) : a (I j+1) < t := by
    have hl : (digits (a (I j))).length = t := (hI j) ▸ (hwords j).2
    have eligible_t : eligible (state (I j)).2 (a (I j)) t :=
      ⟨hskip _,by rw [hl]⟩
    have hle := least eligible_t
    exact lt_of_le_of_ne hle (fun e => absent ⟨_,e⟩)
  let f (j : Fin (t+1)) : Fin t := ⟨_,hlow j⟩
  have hf : Function.Injective f := by
    intro i j he
    have heq : a (I i+1) = a (I j+1) := congrArg Fin.val he
    have hindex : I i = I j := by have := injective heq; omega
    have hw : w i = w j := (hI i).symm.trans (hindex ▸ hI j)
    apply Fin.ext
    dsimp [w,prefixNumber] at hw
    omega
  have := Fintype.card_le_of_injective f hf
  simp at this

end DigitLengthGreedy

theorem OMA.solution : type_of% @OMA.S_oeis_a269631.main := DigitLengthGreedy.permutation
