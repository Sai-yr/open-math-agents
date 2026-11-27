import OMAStatements.S_oeis_a088862

namespace OMA.S_oeis_a088862

private def bracket (p d l : ℕ) : Prop := (p-1)^d < 2^l ∧ 2^l ≤ p^d

-- For fixed d and l at most one integer can bracket the power of two.
private theorem unique_bracket {p q d l : ℕ} (hp : bracket p d l) (hq : bracket q d l) : p=q := by
  have oneWay {a b : ℕ} (ha : bracket a d l) (hb : bracket b d l) : b ≤ a := by
    by_contra! h
    have hh := Nat.pow_le_pow_left (show a ≤ b-1 by omega) d
    exact (not_lt_of_ge (ha.2.trans hh)) hb.1
  exact Nat.le_antisymm (oneWay hq hp) (oneWay hp hq)

-- Bad primes are sparse: their reciprocal sum is bounded by finitely
-- many copies of a geometric series. Euler's divergent prime
-- reciprocal sum therefore supplies a prime avoiding every bracket.
private theorem good_prime (n : ℕ) :
    ∃ p : Nat.Primes, ∀ d l : ℕ, 0 < d → d ≤ n → ¬ bracket p d l := by
  classical
  by_contra! bad
  choose degree exponent hpos hdeg hbr using bad
  let code (p : Nat.Primes) : (Fin (n+1) × Fin (n+1)) × ℕ :=
    ((⟨degree p,by have := hdeg p; omega⟩,
      ⟨exponent p%(n+1),Nat.mod_lt _ (by omega)⟩),exponent p/(n+1))
  have hinj : Function.Injective code := by
    intro p q h
    have hd : degree p=degree q := congrArg (fun z : (Fin (n+1) × Fin (n+1)) × ℕ => z.1.1.val) h
    have hr : exponent p%(n+1)=exponent q%(n+1) :=
      congrArg (fun z : (Fin (n+1) × Fin (n+1)) × ℕ => z.1.2.val) h
    have hq : exponent p/(n+1)=exponent q/(n+1) := congrArg Prod.snd h
    have ep := Nat.mod_add_div (exponent p) (n+1)
    have eq := Nat.mod_add_div (exponent q) (n+1)
    rw [hr,hq,eq] at ep
    apply Subtype.ext
    exact unique_bracket (hbr p) (by simpa [hd,← ep] using hbr q)
  let f (z : (Fin (n+1) × Fin (n+1)) × ℕ) : ℝ := (1/2:ℝ)^z.2
  have hf : Summable f := (summable_prod_of_nonneg (fun _ => by dsimp [f]; positivity)).mpr
    ⟨fun _ => summable_geometric_of_lt_one (by norm_num) (by norm_num),Summable.of_finite⟩
  have hbound (p : Nat.Primes) : (1/(p:ℝ)) ≤ f (code p) := by
    let q := exponent p/(n+1)
    have hl : q*degree p ≤ exponent p := calc
      _ ≤ q*(n+1) := Nat.mul_le_mul_left _ (by have := hdeg p; omega)
      _ ≤ exponent p := Nat.div_mul_le_self _ _
    have hp : (2^q)^degree p ≤ (p:ℕ)^degree p := by
      rw [← pow_mul]
      exact (Nat.pow_le_pow_right (by decide) hl).trans (hbr p).2
    have hbase : 2^q ≤ (p:ℕ) := (Nat.pow_le_pow_iff_left (by have := hpos p; omega)).mp hp
    change 1/(p:ℝ) ≤ (1/2:ℝ)^q
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hbase
  exact Nat.Primes.not_summable_one_div (Summable.of_nonneg_of_le (fun p => by positivity)
    hbound (hf.comp_injective hinj))

-- If the binary word for p^i is a proper prefix of p^(i+d), then
-- division by the appropriate power of two has quotient p^i. This
-- places that same power of two strictly above (p-1)^d and at most p^d.
private theorem collision {p i d l : ℕ} (hp : 1 < p) (hi : 0 < i) (hd : 0 < d)
    (h : p^(i+d)/2^l=p^i) : bracket p d l := by
  have hden : 0 < 2^l := by positivity
  have hu := (Nat.div_lt_iff_lt_mul hden).mp (show p^(i+d)/2^l < p^i+1 by omega)
  have hlo := (Nat.le_div_iff_mul_le hden).mp h.ge
  rw [pow_add] at hu hlo
  have hx : 0 < p^i := by positivity
  have hx' : p ≤ p^i := by simpa using Nat.pow_le_pow_right (n := p) (by omega) hi
  constructor
  · by_contra! hbad
    obtain ⟨r,hr⟩ : ∃ r, d=r+1 := ⟨d-1,by omega⟩
    subst d
    have hm : (p^i+1)*(p-1) ≤ p^i*p := by
      have hpred : p-1+1=p := by omega
      nlinarith [congrArg (fun z : ℕ => p^i*z) hpred]
    have hlim : (p^i+1)*(p-1)^(r+1) ≤ p^i*p^(r+1) := calc
      _ = (p^i+1)*(p-1)^r*(p-1) := by rw [pow_succ]; ring
      _ ≤ (p^i+1)*p^r*(p-1) := by gcongr; omega
      _ = ((p^i+1)*(p-1))*p^r := by ring
      _ ≤ (p^i*p)*p^r := Nat.mul_le_mul_right _ hm
      _ = p^i*p^(r+1) := by rw [pow_succ p r]; ring
    exact (not_lt_of_ge ((Nat.mul_le_mul_left (p^i+1) hbad).trans hlim)) hu
  · exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hlo) hx

end OMA.S_oeis_a088862

open OMA.S_oeis_a088862 in
theorem OMA.solution : type_of% @OMA.S_oeis_a088862.main := by
  classical
  intro n
  obtain ⟨p,hp⟩ := good_prime n
  have he : eligible n ((p:ℕ)^n) := by
    refine ⟨pow_pos p.property.pos _,by simp [p.property.primeFactorsList_pow],?_⟩
    intro a ha ha₁ b hb hb₁ l hl
    obtain ⟨i,hin,rfl⟩ := (Nat.dvd_prime_pow p.property).mp ha
    obtain ⟨j,hjn,rfl⟩ := (Nat.dvd_prime_pow p.property).mp hb
    have hi : 0 < i := by
      by_contra! h
      have hzero : i=0 := by omega
      simp [hzero] at ha₁
    have hle : (p:ℕ)^i ≤ (p:ℕ)^j := hl ▸ Nat.div_le_self _ _
    have hij : i ≤ j := (Nat.pow_le_pow_iff_right p.property.one_lt).mp hle
    by_cases heq : i=j
    · rw [heq]
    · have hbr := collision p.property.one_lt hi (show 0 < j-i by omega)
          (by simpa [show i+(j-i)=j by omega] using hl)
      exact False.elim (hp (j-i) l (by omega) (by omega) hbr)
  have existsTerm : ∃ m, eligible n m := ⟨_,he⟩
  exact ⟨Nat.find existsTerm,Nat.find_spec existsTerm,fun _ hx => Nat.find_min' existsTerm hx⟩
