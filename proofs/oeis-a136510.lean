import OMAStatements.S_oeis_a136510

namespace OMA.S_oeis_a136510

/-- For an odd base, Euler's theorem preserves its entire low binary block. -/
private theorem oddPowerPrefix {u : ℕ} (hu : Odd u) :
    ∃ t : ℕ, 0 < t ∧ ∃ tail : List ℕ,
      Nat.digits 2 u ++ tail = Nat.digits 2 (u ^ (t + 1)) := by
  let M := 2 ^ (Nat.digits 2 u).length
  have hlt : u < M := Nat.lt_base_pow_length_digits (by decide)
  have hM : 0 < M := by dsimp [M]; positivity
  have hcop : u.Coprime M := hu.coprime_two_right.pow_right _
  let t := Nat.totient M
  have hcong : u ^ (t + 1) ≡ u [MOD M] := by
    simpa only [pow_succ, one_mul] using (Nat.ModEq.pow_totient hcop).mul_right u
  have hrem : u ^ (t + 1) % M = u := Eq.trans hcong (Nat.mod_eq_of_lt hlt)
  let q := u ^ (t + 1) / M
  have hparts : u + M * q = u ^ (t + 1) := by
    calc
      u + M * q = u ^ (t + 1) % M + M * q := by rw [hrem]
      _ = _ := Nat.mod_add_div _ _
  refine ⟨t, Nat.totient_pos.mpr hM, Nat.digits 2 q, ?_⟩
  rw [Nat.digits_append_digits (by decide : 0 < 2)]
  exact congrArg (Nat.digits 2) hparts

private theorem hasExponent (n : ℕ) (hn : 0 < n) : ∃ k, k ∈ exponents n := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hpos : 0 < u := by obtain ⟨a, ha⟩ := hu; omega
  obtain ⟨t, ht, tail, htail⟩ := oddPowerPrefix hu
  refine ⟨t + 1, by omega, List.replicate (v * t) 0, tail, ?_⟩
  rw [Nat.digits_base_pow_mul (by decide : 1 < 2) hpos, mul_pow, ← pow_mul,
    Nat.digits_base_pow_mul (by decide : 1 < 2) (pow_pos hpos _), Nat.mul_add,
    Nat.mul_one, ← List.replicate_append_replicate]
  simp only [List.append_assoc, htail]

end OMA.S_oeis_a136510

theorem OMA.solution : type_of% @OMA.S_oeis_a136510.main := by
  classical
  intro n hn
  let h := OMA.S_oeis_a136510.hasExponent n hn
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hk => Nat.find_min' h hk⟩
