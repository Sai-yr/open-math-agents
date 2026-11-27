import OMAReductions.R_mo_509919_R1

open OMA.S_mo_509919 OMA.R_mo_509919_R1

namespace EarlyPrimeFactors

private def prefixDivisors (k n : ℕ) : List ℕ := (n.divisors.sort (· ≤ ·)).take k

private def sizeBound (k B : ℕ) : ℕ := k * (k * B^(2*(k-1)))^(2*(k-1))


private theorem down_list {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) {e d k : ℕ}
    (hd : d ∈ l.take k) (he : e ∈ l) (hed : e ≤ d) : e ∈ l.take k := by
  induction l generalizing k with
  | nil => simp at hd
  | cons a l ih =>
    cases k with
    | zero => simp at hd
    | succ k =>
      simp only [List.take_succ_cons,List.mem_cons] at hd he ⊢
      obtain rfl|hem := he
      · exact Or.inl rfl
      rcases hd with eq|hd
      · have h := (List.pairwise_cons.mp hl).1 e hem
        exact Or.inl (by omega)
      · exact Or.inr (ih (List.pairwise_cons.mp hl).2 hd hem)

private theorem mem_full {k n d : ℕ} (hd : d ∈ prefixDivisors k n) : d ∈ n.divisors := by
  simpa using (List.mem_of_mem_take hd : d ∈ n.divisors.sort (· ≤ ·))

private theorem closed {k n d e : ℕ} (hd : d ∈ prefixDivisors k n) (he : e ∣ d) :
    e ∈ prefixDivisors k n := by
  have full := mem_full hd
  have en : e ∈ n.divisors := Nat.mem_divisors.mpr ⟨he.trans (Nat.dvd_of_mem_divisors full),
    (Nat.mem_divisors.mp full).2⟩
  exact down_list (n.divisors.pairwise_sort (· ≤ ·)) hd (by simpa using en)
    (Nat.le_of_dvd (Nat.pos_of_mem_divisors full) he)

private theorem ranked_size {d B : ℕ} (hd : 0<d) (hB : 0<B)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ B) : d ≤ B^(d.divisors.card-1) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h1 : d=1
    · simp [h1]
    let p := d.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    have pd : p ∣ d := Nat.minFac_dvd _
    let e := d/p
    have mul : p*e=d := Nat.mul_div_cancel' pd
    have ed : e ∣ d := Nat.div_dvd_of_dvd pd
    have lt : e < d := Nat.div_lt_self hd hp.one_lt
    have ep : 0 < e := Nat.div_pos (Nat.le_of_dvd hd pd) hp.pos
    have smaller : e.divisors.card < d.divisors.card := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Nat.divisors_subset_of_dvd hd.ne' ed)).mpr
      refine ⟨d,Nat.mem_divisors.mpr ⟨dvd_refl _,hd.ne'⟩,fun dm => ?_⟩
      exact (not_lt_of_ge (Nat.le_of_dvd ep (Nat.dvd_of_mem_divisors dm))) lt
    have one : 0 < e.divisors.card := Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,ep.ne'⟩⟩
    calc
      d = p*e := mul.symm
      _ ≤ B*B^(e.divisors.card-1) := Nat.mul_le_mul (hpr p hp pd) (ih e lt ep
        (fun q hq hqe => hpr q hq (hqe.trans ed)))
      _ = B^((e.divisors.card-1)+1) := by rw [pow_succ']
      _ ≤ _ := Nat.pow_le_pow_right hB (by omega)

private theorem element_bound {k n d B : ℕ} (hd : d ∈ prefixDivisors k n) (hB : 0<B)
    (hpr : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ B) : d ≤ B^(k-1) := by
  have sub : d.divisors ⊆ (prefixDivisors k n).toFinset := by
    intro t ht
    exact List.mem_toFinset.mpr (closed hd (Nat.dvd_of_mem_divisors ht))
  have le := (Finset.card_le_card sub).trans ((List.toFinset_card_le _).trans (List.length_take_le k _))
  exact (ranked_size (Nat.pos_of_mem_divisors (mem_full hd)) hB hpr).trans
    (Nat.pow_le_pow_right hB (by omega))

private theorem sum_bound {l : List ℕ} {f : ℕ → ℕ} {C : ℕ} (bound : ∀ x ∈ l, f x ≤ C) :
    (l.map f).sum ≤ l.length*C := by
  simpa using (List.sum_le_sum (g:=fun _ => C) bound)

private theorem discard {p : ℕ} (l : List ℕ) :
    (l.map (fun x => x^2)).sum ≡
      (l.map (fun x => if p ∣ x then 0 else x^2)).sum [MOD p] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons]
    apply Nat.ModEq.add _ ih
    split
    · exact Nat.modEq_zero_iff_dvd.mpr (dvd_trans ‹p ∣ a› (dvd_pow_self a (by decide : 2 ≠ 0)))
    · rfl

theorem quantitative_gap : H1 := by
  intro k n B sol hB hn
  by_contra no
  let S := prefixDivisors k n
  have len : S.length ≤ k := List.length_take_le _ _
  have eq : n = (S.map (fun d => d^2)).sum := sol.2
  have np : 0 < n := by omega
  have kp : 0 < k := by
    by_contra! h
    have : k=0 := by omega
    simp [this,S,prefixDivisors] at eq
    omega
  have one : 1 ∈ S := by
    have nonempty : S ≠ [] := by intro nil; simp [nil] at eq; omega
    obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil S nonempty
    exact closed hd (one_dvd _)
  let C := k*B^(2*(k-1))
  have Cp : 0<C := Nat.mul_pos kp (pow_pos (by omega) _)
  have prime_bound (p : ℕ) (hp : p.Prime) (pm : p ∈ S) : p ≤ C := by
    have kk : 2 ≤ k := by
      have incl : ({1,p} : Finset ℕ) ⊆ S.toFinset := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · exact List.mem_toFinset.mpr one
        · exact List.mem_toFinset.mpr pm
      have card := (Finset.card_le_card incl).trans ((List.toFinset_card_le S).trans len)
      simpa [hp.ne_one.symm] using card
    by_cases small : p ≤ B
    · exact small.trans ((Nat.le_self_pow (by omega : 2*(k-1) ≠ 0) B).trans
        (Nat.le_mul_of_pos_left _ kp))
    let f (d : ℕ) := if p ∣ d then 0 else d^2
    have residue : n ≡ (S.map f).sum [MOD p] := eq ▸ discard S
    have pdn := Nat.dvd_of_mem_divisors (mem_full pm)
    have divsum : p ∣ (S.map f).sum := Nat.modEq_zero_iff_dvd.mp
      (residue.symm.trans (Nat.modEq_zero_iff_dvd.mpr pdn))
    have pos : 0 < (S.map f).sum := by
      have h := List.single_le_sum (l:=S.map f) (fun _ _ => Nat.zero_le _) (f 1)
        (List.mem_map_of_mem one)
      have low : 1 ≤ (S.map f).sum := by simpa [f,hp.not_dvd_one] using h
      omega
    apply (Nat.le_of_dvd pos divsum).trans
    apply (sum_bound (C:=B^(2*(k-1))) ?_).trans (Nat.mul_le_mul_right _ len)
    intro d hd
    dsimp [f]
    split
    · omega
    · rename_i nd
      have bound := element_bound hd (by omega : 0 < B) (fun q hq qd => by
        by_contra! large
        exact no ⟨p,pm,q,closed hd qd,hp,hq,by omega,large,fun e => nd (e ▸ qd)⟩)
      simpa [Nat.mul_comm 2, pow_mul] using Nat.pow_le_pow_left bound 2
  have all (d : ℕ) (hd : d ∈ S) : d^2 ≤ C^(2*(k-1)) := by
    have h := element_bound hd Cp (fun q hq qd => prime_bound q hq (closed hd qd))
    simpa [Nat.mul_comm 2,pow_mul] using Nat.pow_le_pow_left h 2
  have nbound : n ≤ sizeBound k B := eq ▸ (sum_bound all).trans (Nat.mul_le_mul_right _ len)
  exact (not_lt_of_ge nbound) hn

end EarlyPrimeFactors

theorem OMA.solution : OMA.R_mo_509919_R1.H1 := EarlyPrimeFactors.quantitative_gap
