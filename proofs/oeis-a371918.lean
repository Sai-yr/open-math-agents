import OMAStatements.S_oeis_a371918

namespace A371918Proof
open OMA.S_oeis_a371918

private theorem irrational_ratio : Irrational (Real.log 2 / Real.log 10) := by
  rintro ⟨q, hq⟩
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hten : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hpos : 0 < q := by exact_mod_cast (show 0 < (q : ℝ) by rw [hq]; positivity)
  let m := q.num.toNat
  have hm : (m : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hpos).le
  have hnum : 0 < q.num := Rat.num_pos.mpr hpos
  have hm0 : 0 < m := by omega
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have he : (m : ℝ) * Real.log 10 = (q.den : ℝ) * Real.log 2 := by
    rw [Rat.cast_def] at hq
    have h := (div_eq_div_iff hd hten.ne').1 hq
    have hm' : (m : ℝ) = (q.num : ℝ) := by exact_mod_cast hm
    rw [hm']; linarith
  have eq : (10 : ℕ)^m = 2^q.den := by
    have := congrArg Real.exp he
    rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num),
      Real.exp_log (by norm_num)] at this
    exact_mod_cast this
  have hdiv : 5 ∣ (10 : ℕ)^m := dvd_trans (by decide : 5 ∣ 10) (dvd_pow_self 10 (by omega))
  rw [eq] at hdiv
  exact (by decide : ¬5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hdiv)

/-- Every positive decimal prefix occurs in arbitrarily late powers of two. -/
private theorem prefix_exists (n K : ℕ) (hn : 0 < n) :
    ∃ k ≥ K, ∃ j : ℕ, 2^k / 10^j = n := by
  let p := Real.log 10
  let a := Real.log 2
  let B := K + n + 1
  have hp : 0 < p := Real.log_pos (by norm_num)
  have ha : 0 < a := Real.log_pos (by norm_num)
  let : Fact (0 < p) := ⟨hp⟩
  have hd : DenseRange (fun m : ℕ => m • (a : AddCircle p)) :=
    denseRange_zsmul_iff_nsmul.mp (AddCircle.denseRange_zsmul_coe_iff.mpr irrational_ratio)
  let U := Set.Ioo (Real.log n - B*a) (Real.log (n+1) - B*a)
  have hu : U.Nonempty := Set.nonempty_Ioo.mpr (by
    exact sub_lt_sub_right (Real.log_lt_log (by positivity) (by linarith)) _)
  obtain ⟨k, x, hx, he⟩ := hd.exists_mem_open
    (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples p) U isOpen_Ioo)
    (hu.image ((↑) : ℝ → AddCircle p))
  have hz : ((k • a - x : ℝ) : AddCircle p) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_nsmul, ← he, sub_self]
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff p).mp hz
  simp only [zsmul_eq_mul, nsmul_eq_mul] at hj
  change Real.log n - B*a < x ∧ x < Real.log (n+1) - B*a at hx
  have hBn : n+1 ≤ (2 : ℕ)^B :=
    le_trans (by dsimp [B]; omega) (Nat.lt_two_pow_self (n := B)).le
  have hB : Real.log (n+1) ≤ B*a := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hBn
  have hj0 : 0 ≤ j := by
    by_contra! h
    have h' : (j : ℝ) < 0 := by exact_mod_cast h
    have hneg := mul_neg_of_neg_of_pos h' hp
    have hka : 0 ≤ (k : ℝ)*a := by positivity
    linarith [hx.2]
  let t := j.toNat
  have ht : (t : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
  have lo : Real.log n + t*p < (B+k : ℕ)*a := by
    push_cast; rw [ht]; linarith [hx.1]
  have hi : ((B+k : ℕ) : ℝ)*a < Real.log (n+1) + t*p := by
    push_cast; rw [ht]; linarith [hx.2]
  have lo' := Real.exp_lt_exp.mpr lo
  have hi' := Real.exp_lt_exp.mpr hi
  simp only [p, a, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (n : ℝ)),
    Real.exp_log (by positivity : 0 < (n : ℝ) + 1), Real.exp_log (by norm_num : (0 : ℝ) < 10),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at lo' hi'
  refine ⟨B+k, by dsimp [B]; omega, t, Nat.div_eq_of_lt_le ?_ ?_⟩
  · exact_mod_cast lo'.le
  · exact_mod_cast hi'

private theorem unbounded (n K : ℕ) : ∃ k ≥ K, contains (2^k) n := by
  by_cases hn : n = 0
  · subst n
    obtain ⟨k, hk, j, hj⟩ := prefix_exists 10 K (by decide)
    refine ⟨k, hk, Or.inr ⟨j, ?_, ?_⟩⟩
    · have h : 1 ≤ 2^k / 10^j := by omega
      simpa using (Nat.le_div_iff_mul_le (by positivity)).mp h
    · rw [hj]; decide
  · obtain ⟨k, hk, j, hj⟩ := prefix_exists n K (by omega)
    refine ⟨k, hk, Or.inr ⟨j, ?_, ?_⟩⟩
    · have h : 1 ≤ 2^k / 10^j := by omega
      simpa using (Nat.le_div_iff_mul_le (by positivity)).mp h
    · rw [hj, Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by decide) n)]

private def allowed (n : ℕ) (s : Finset ℕ) (k : ℕ) : Prop :=
  0 < k ∧ contains (2^k) n ∧ k ∉ s

private theorem available (n : ℕ) (s : Finset ℕ) : ∃ k, allowed n s k := by
  obtain ⟨k, hk, h⟩ := unbounded n (s.sup id + 1)
  refine ⟨k, by omega, h, fun hmem => ?_⟩
  have hle : k ≤ s.sup id := Finset.le_sup (f := id) hmem
  omega

private noncomputable def pick (n : ℕ) (s : Finset ℕ) : ℕ := by
  classical exact Nat.find (available n s)

private theorem pick_spec (n : ℕ) (s : Finset ℕ) :
    allowed n s (pick n s) ∧ ∀ k, allowed n s k → pick n s ≤ k := by
  classical exact ⟨Nat.find_spec _, fun _ => Nat.find_min' _⟩

private noncomputable def history : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => insert (pick n (history n)) (history n)

private noncomputable def term (n : ℕ) := pick n (history n)

private theorem history_mem (k n : ℕ) : k ∈ history n ↔ ∃ i < n, term i = k := by
  induction n with
  | zero => simp [history]
  | succ n ih =>
    rw [history, Finset.mem_insert, ih]
    change (k = term n ∨ _) ↔ _
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i = n
      · exact Or.inl (congrArg term h)
      · exact Or.inr ⟨i, by omega, rfl⟩

private theorem term_greedy : greedy term := by
  intro n
  have iff (k : ℕ) : allowed n (history n) k ↔ eligible term n k := by
    simp [allowed, eligible, history_mem]
  exact ⟨(iff _).mp (pick_spec n _).1, fun k h => (pick_spec n _).2 k ((iff k).mpr h)⟩

private theorem contains_le {x n : ℕ} (h : contains x n) : n ≤ x := by
  rcases h with ⟨rfl, rfl⟩ | ⟨j, _, hj⟩
  · exact le_rfl
  · rw [← hj]
    exact (Nat.mod_le _ _).trans (Nat.div_le_self _ _)

private theorem contains_self (x : ℕ) (hx : 0 < x) : contains x x := by
  refine Or.inr ⟨0, by simpa using (show 1 ≤ x by omega), ?_⟩
  simp [Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (b := 10) (by decide) x)]

end A371918Proof

open OMA.S_oeis_a371918 A371918Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a371918.main := by
  refine ⟨⟨_, term_greedy⟩, ?_⟩
  intro a ha
  constructor
  · intro i j he
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim ((ha j).1.2.2 i h he)
    · exact h
    · exact False.elim ((ha i).1.2.2 j h he.symm)
  · ext k
    constructor
    · rintro ⟨n, rfl⟩
      exact (ha n).1.1
    · intro hk
      change 0 < k at hk
      by_cases h : ∃ i < 2^k, a i = k
      · obtain ⟨i, _, hi⟩ := h
        exact ⟨i, hi⟩
      · have hadm : eligible a (2^k) k :=
          ⟨hk, contains_self _ (by positivity), fun i hi he => h ⟨i, hi, he⟩⟩
        refine ⟨2^k, le_antisymm ((ha _).2 k hadm) ?_⟩
        by_contra! hlt
        exact (Nat.not_le_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hlt))
          (contains_le (ha _).1.2.1)
