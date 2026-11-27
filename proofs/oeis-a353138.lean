import OMAStatements.S_oeis_a353138

namespace OMA.S_oeis_a353138

private abbrev score (b : ℕ) (ds : List ℕ) := (ds.map (fun d => b^d)).sum

/-- Twelve or more places are impossible: the smallest number of that
length already exceeds the sum of its digit powers. -/
private theorem lengthBound {n : ℕ} (hn : 0 < n) (hfixed : term n = n) :
    (Nat.digits 10 n).length ≤ 11 := by
  let ds := Nat.digits 10 n
  let b := ds.length
  have hb : 0 < b := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne')
  have upper (xs : List ℕ) (h : ∀ d ∈ xs, d < 10) : score b xs ≤ xs.length * b^9 := by
    induction xs with
    | nil => simp [score]
    | cons d xs ih =>
      have hd := h d (by simp)
      have htail := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have hp := Nat.pow_le_pow_right hb (by omega : d ≤ 9)
      change b^d + score b xs ≤ (xs.length+1)*b^9
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have hu := upper ds (fun _ h => Nat.digits_lt_base (by decide : 1 < 10) h)
  change score b ds ≤ b * b^9 at hu
  change score b ds = n at hfixed
  rw [hfixed, ← pow_succ'] at hu
  have large (k : ℕ) : (k+12)^10 < 10^(k+11) := by
    induction k with
    | zero => decide
    | succ k ih =>
      have grow : (k+13)^10 ≤ 10*(k+12)^10 := by
        have hp := Nat.pow_le_pow_left (by omega : 12*(k+13) ≤ 13*(k+12)) 10
        rw [mul_pow, mul_pow] at hp
        norm_num at hp
        omega
      calc
        (k+13)^10 ≤ 10*(k+12)^10 := grow
        _ < 10*10^(k+11) := Nat.mul_lt_mul_of_pos_left ih (by decide)
        _ = 10^(k+12) := (pow_succ' 10 (k+11)).symm
  by_contra! hl
  change 11 < b at hl
  obtain ⟨k, hk⟩ : ∃ k, b = k+12 := ⟨b-12, by omega⟩
  have hlow : 10^(k+11) ≤ n := (Nat.lt_digits_length_iff (by decide : 1 < 10) n).mp (by change k+11 < b; omega)
  have := large k
  rw [hk] at hu
  change n ≤ (k+12)^10 at hu
  omega

-- At a leaf `t` is the sum of the digit powers and `w` the sum of the
-- digits chosen. Congruence modulo nine and length cheaply discard
-- candidates before evaluating the digit powers of `t` itself.
private def safe (b t w : ℕ) : Bool := decide
  (w%9 ≠ t%9 ∨ t < 10^(b-1) ∨ 10^b ≤ t ∨ t = 1 ∨ t = 4624 ∨ score b (Nat.digits 10 t) ≠ t)

private def check (b : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, t, w => safe b t w
  | k+1, hi, t, w => (List.range (hi+1)).all (fun d => check b k d (t+b^d) (w+d))

/-- Every multiset of a given length has a decreasing ordering and follows
one branch of the exhaustive check. -/
private theorem leaf {b : ℕ} (xs : List ℕ) (hs : xs.Pairwise (· ≥ ·)) {hi t w : ℕ}
    (hb : ∀ d ∈ xs, d ≤ hi) (hc : check b xs.length hi t w = true) :
    safe b (t+score b xs) (w+xs.sum) = true := by
  induction xs generalizing hi t w with
  | nil => simpa [check, score] using hc
  | cons d xs ih =>
    have hp := List.pairwise_cons.mp hs
    have hd := hb d (by simp)
    have hc' := List.all_eq_true.mp hc d (List.mem_range.mpr (by omega))
    have hleaf := ih hp.2 hp.1 hc'
    simpa only [score, List.map_cons, List.sum_cons, Nat.add_assoc] using hleaf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem checked (b : ℕ) (hb : b ≤ 11) : check b b 9 0 0 = true := by
  interval_cases b <;> decide +kernel

private theorem classify {n : ℕ} (hn : 0 < n) (hf : term n = n) : n = 1 ∨ n = 4624 := by
  let ds := Nat.digits 10 n
  let b := ds.length
  let xs := ds.mergeSort (fun x y => decide (x ≥ y))
  have hp : xs.Perm ds := List.mergeSort_perm ..
  have hs : xs.Pairwise (· ≥ ·) := List.pairwise_mergeSort' _ _
  have hb : ∀ d ∈ xs, d ≤ 9 := by
    intro d hd
    exact Nat.le_of_lt_succ (Nat.digits_lt_base (by decide : 1 < 10) (hp.mem_iff.mp hd))
  have hc : check b xs.length 9 0 0 = true := hp.length_eq ▸ checked b (lengthBound hn hf)
  have hl := leaf xs hs hb hc
  have hscore : score b xs = n := (hp.map (fun d => b^d)).sum_eq.trans hf
  rw [Nat.zero_add, Nat.zero_add, hscore, hp.sum_eq] at hl
  have hmod : n%9 = ds.sum%9 := Nat.modEq_nine_digits_sum n
  have hpos : 0 < b := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne')
  have hlow : 10^(b-1) ≤ n := (Nat.lt_digits_length_iff (by decide : 1 < 10) n).mp (by change b-1 < b; omega)
  have hhigh : n < 10^b := Nat.lt_base_pow_length_digits (by decide)
  change score b (Nat.digits 10 n) = n at hf
  simp only [safe, decide_eq_true_eq] at hl
  omega

end OMA.S_oeis_a353138

open OMA.S_oeis_a353138 in
theorem OMA.solution : type_of% @OMA.S_oeis_a353138.main := by
  intro n hn
  refine ⟨classify hn, ?_⟩
  rintro (rfl | rfl) <;> decide +kernel
