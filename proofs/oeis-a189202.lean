import OMAStatements.S_oeis_a189202

namespace OMA.S_oeis_a189202

-- The two terms occupy disjoint digit positions in base b.
private theorem separate {b w x y : ℕ} (hb : 1 < b) (hx : x < b^w)
    (hy : 0 < y) (hd : b^w ∣ y) : ds b (x+y) = ds b x + ds b y := by
  obtain ⟨t,ht⟩ := hd
  have htpos : 0 < t := by by_contra! hz; obtain rfl := Nat.eq_zero_of_le_zero hz; simp [ht] at hy
  have hlen := (Nat.digits_length_le_iff hb x).mpr hx
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le hlen
  have h := Nat.digits_append_zeroes_append_digits (b:=b) (n:=x) (m:=t) (k:=z) hb htpos
  rw [← hz, ← ht] at h
  have hsum := congrArg List.sum h.symm
  have hy' : ds b y = ds b t := by
    rw [ht, ds, Nat.digits_base_pow_mul hb htpos]
    simp [ds]
  rw [hy']
  simpa [ds] using hsum

private theorem quotient_integral {n x : ℕ} (hn : 2 ≤ n) (hx : n-1 ∣ x) :
    n-1 ∣ ds n x := by
  by_cases h₂ : n = 2
  · simp [h₂]
  have hmod : n % (n-1) = 1 := by
    rw [Nat.mod_eq_sub_mod (by omega), show n-(n-1)=1 by omega, Nat.mod_eq_of_lt (by omega)]
  exact ((Nat.modEq_digits_sum _ _ hmod x).dvd_iff (dvd_refl _)).mp hx

private def exponent (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 =>
    let e := exponent n i
    e + 2*((n-1)*(2*n)^e) + 1

private theorem construct {n : ℕ} (hn : 2 ≤ n) : ∃ m, admissible n m := by
  let e := exponent n
  let y (i : ℕ) := (n-1)*(2*n)^(e i)
  have hy (i : ℕ) : 0 < y i :=
    Nat.mul_pos (by omega : 0 < n-1) (pow_pos (by omega : 0 < 2*n) _)
  have inc (i : ℕ) : e i < e (i+1) := by change e i < e i+2*y i+1; omega
  have mono : StrictMono e := strictMono_nat_of_lt_succ inc
  let A (i : ℕ) := ds 2 (y i)
  let B (i : ℕ) := ds n (2*y i)/(n-1)
  let parity (t : ℕ) : Fin 2 := ⟨t%2, Nat.mod_lt _ (by decide)⟩
  let f (i : Fin 5) := (parity (A i), parity (B i))
  obtain ⟨u,v,hne,hmatch⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by decide)
  obtain ⟨i,j,hij,h₁,h₂⟩ : ∃ i j : ℕ, i < j ∧ A i%2 = A j%2 ∧ B i%2 = B j%2 := by
    have ha := congrArg (fun q : Fin 2 × Fin 2 => (q.1:ℕ)) hmatch
    have hb := congrArg (fun q : Fin 2 × Fin 2 => (q.2:ℕ)) hmatch
    change A u%2=A v%2 at ha
    change B u%2=B v%2 at hb
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨u,v,h,ha,hb⟩
    · exact ⟨v,u,h,ha.symm,hb.symm⟩
  have hgap : 2*y i < e j := by
    have h := mono.monotone (show i+1≤j by omega)
    change e i+2*y i+1 ≤ e j at h
    omega
  have hx₂ : y i < 2^e j := by
    have h : e j < 2^e j := Nat.lt_pow_self (by decide)
    omega
  have hxn : 2*y i < n^e j := hgap.trans (Nat.lt_pow_self (by omega))
  have hp₂ : 2^(e j) ∣ y j := by
    refine ⟨(n-1)*n^(e j), ?_⟩
    dsimp only [y]
    rw [mul_pow]
    ring
  have hpn : n^(e j) ∣ 2*y j := by
    refine ⟨2*(n-1)*2^(e j), ?_⟩
    dsimp only [y]
    rw [mul_pow]
    ring
  have s₂ : ds 2 (y i+y j) = A i + A j := separate (by decide) hx₂ (hy _) hp₂
  have sn : ds n (2*(y i+y j)) = ds n (2*y i)+ds n (2*y j) := by
    rw [Nat.mul_add]
    exact separate (by omega) hxn (by have := hy j; omega) hpn
  have hbmul (k : ℕ) : B k * (n-1) = ds n (2*y k) := by
    apply Nat.div_mul_cancel
    apply quotient_integral hn
    exact ⟨2*(2*n)^(e k), by dsimp only [y]; ring⟩
  have hquot : ds n (2*(y i+y j))/(n-1) = B i+B j := by
    rw [sn, ← hbmul i, ← hbmul j, ← Nat.add_mul, Nat.mul_div_cancel _ (by omega : 0<n-1)]
  let m := (2*n)^(e i)+(2*n)^(e j)
  have hm : m*(n-1) = y i+y j := by dsimp only [m,y]; ring
  refine ⟨m, by dsimp only [m]; positivity, ?_, ?_⟩
  · rw [hm,s₂,Nat.even_iff]
    omega
  · rw [Nat.mul_assoc,hm,hquot,Nat.even_iff]
    omega

end OMA.S_oeis_a189202

open OMA.S_oeis_a189202 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189202.main := by
  classical
  intro n hn
  have h := construct hn
  rw [term,dif_pos h]
  exact (Nat.find_spec h).1
