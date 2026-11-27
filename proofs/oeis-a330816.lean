import OMAStatements.S_oeis_a330816
import Mathlib

/-!
# Exhaustive predecessor closure for Corneth's list

For a fixed listed target v, a predecessor of interest has the form vd with
d = τ(vd). Bounds on d and the prime factors of τ(vd) reduce this to a tree
of prime exponents. A positive divisor z left to choose can only reduce the
ratio τ(vdz)/(dz) compared with τ(vd)/d. This supplies the pruning certificate.
-/

open OMA.S_oeis_a330816

private abbrev tau (n : ℕ) := n.divisors.card

private lemma tau_submul (a b : ℕ) : tau (a*b) ≤ tau a * tau b := by
  classical
  by_cases ha : a=0
  · simp [ha,tau]
  by_cases hb : b=0
  · simp [hb,tau]
  have sub : (a*b).divisors ⊆ (a.divisors ×ˢ b.divisors).image (fun xy : ℕ × ℕ => xy.1*xy.2) := by
    intro x hx
    obtain ⟨i,j,hi,hj,hij⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.mem_divisors.mp hx).1
    exact Finset.mem_image.mpr ⟨(i,j), Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hi,ha⟩,
      Nat.mem_divisors.mpr ⟨hj,hb⟩⟩, hij.symm⟩
  exact (Finset.card_le_card sub).trans (by simpa using (Finset.card_image_le
    (s:=a.divisors ×ˢ b.divisors) (f:=fun xy : ℕ × ℕ => xy.1*xy.2)))

private lemma tau_sqrt (n : ℕ) : tau n ≤ 2*n.sqrt := by
  classical
  let small := Finset.Icc 1 n.sqrt
  have sub : n.divisors ⊆ small ∪ small.image (n/·) := by
    intro d hd
    obtain ⟨hdiv,hn⟩ := Nat.mem_divisors.mp hd
    have he := Nat.mul_div_cancel' hdiv
    have hp : 0 < d := Nat.pos_of_mem_divisors hd
    have hq : 0 < n/d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv) hp
    rcases Nat.le_sqrt_of_eq_mul he.symm with hlo | hlo
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hp,hlo⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n/d, Finset.mem_Icc.mpr ⟨hq,hlo⟩,Nat.div_div_self hdiv hn⟩
  calc
    _ ≤ _ := Finset.card_le_card sub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := by
      have hcard : small.card = n.sqrt := by simp [small]
      have hi := Finset.card_image_le (s:=small) (f:=(n/·))
      omega

private lemma bound_multiplier {v d : ℕ} (hd : 0 < d) (he : d=tau (v*d)) :
    d ≤ 4*(tau v)^2 := by
  have hs := tau_sqrt d
  have ht := tau_submul v d
  have hb : d ≤ 2*tau v*d.sqrt := by nlinarith [Nat.mul_le_mul_left (tau v) hs]
  have hs' : d.sqrt^2 ≤ d := by simpa [pow_two] using Nat.sqrt_le d
  have hprod : d^2 ≤ (2*tau v)^2*d := calc
    d^2 ≤ (2*tau v*d.sqrt)^2 := Nat.pow_le_pow_left hb _
    _ = (2*tau v)^2*d.sqrt^2 := mul_pow .. 
    _ ≤ _ := Nat.mul_le_mul_left _ hs'
  have := Nat.le_of_mul_le_mul_right (show d*d ≤ ((2*tau v)^2)*d by simpa [pow_two] using hprod) hd
  nlinarith

private lemma tau_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : tau (p^k) = k+1 := by
  rw [tau, ← ArithmeticFunction.sigma_zero_apply]
  exact ArithmeticFunction.sigma_zero_apply_prime_pow hp

private lemma tau_coprime {m n : ℕ} (h : m.Coprime n) : tau (m*n) = tau m*tau n := h.card_divisors_mul

private lemma tau_mul_prime {x p : ℕ} (hx : x≠0) (hp : p.Prime) :
    tau (x*p) = tau x / (x.factorization p + 1) * (x.factorization p + 2) := by
  let k := x.factorization p
  let u := x / p^k
  have he : p^k*u=x := Nat.ordProj_mul_ordCompl_eq_self x p
  have hc : p.Coprime u := Nat.coprime_ordCompl hp hx
  have h0 : tau x=(k+1)*tau u := by
    calc
      _ = tau (p^k*u) := congrArg tau he.symm
      _ = _ := by rw [tau_coprime (hc.pow_left k),tau_pow hp]
  have h1 : x*p=p^(k+1)*u := by rw [← he,pow_succ]; ring
  rw [h1,tau_coprime (hc.pow_left (k+1)), tau_pow hp,h0]
  change (k+1+1)*tau u=(k+1)*tau u / (k+1) * (k+2)
  rw [Nat.mul_div_cancel_left _ (by omega)]
  ring

private lemma bounded_support {v d : ℕ} (hv : v≠0) (hd : 0<d) (he : d=tau (v*d))
    (ht : 4*(tau v)^2 < 2^42) (hext : ∀ p, v.factorization p ≤ 59) :
    ∀ q, q.Prime → q ∣ d → q ≤ 101 := by
  intro q hq hdq
  have hpow := (bound_multiplier hd he).trans_lt ht
  rw [he, tau, Nat.card_divisors (mul_ne_zero hv hd.ne')] at hdq
  obtain ⟨p,hp,hqf⟩ := (hq.prime.dvd_finsetProd_iff _).mp hdq
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.ordProj_dvd d p
  have hle := Nat.le_of_dvd hd hpd
  have hx : d.factorization p < 42 := by
    by_contra! h
    have h' : 2^42 ≤ p^(d.factorization p) :=
      (Nat.pow_le_pow_left hpp.two_le 42).trans (Nat.pow_le_pow_right hpp.pos h)
    omega
  have last := Nat.le_of_dvd (Nat.succ_pos _) hqf
  rw [Nat.factorization_mul hv hd.ne', Finsupp.add_apply] at last
  have := hext p
  omega

private def check (v : ℕ) (good : List ℕ) : ℕ → List (ℕ × ℕ) → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel+1, ps, d, t =>
    if d > t then true else
    match ps with
    | [] => d != t || good.contains (v*d)
    | (p,e)::rest =>
      if d*p > 2*t then d != t || good.contains (v*d) else
      check v good fuel rest d t &&
        (if 17 ≤ p ∧ ¬p ∣ t then true else
          check v good fuel ((p,e+1)::rest) (d*p) (t/e*(e+1)))

private lemma partial_le {d x z : ℕ} (hz : 0 < z) (he : d*z = tau (x*z)) : d ≤ tau x := by
  apply Nat.le_of_mul_le_mul_right _ hz
  calc
    d*z = _ := he
    _ ≤ _ := tau_submul x z
    _ ≤ tau x*z := Nat.mul_le_mul_left (tau x) (Nat.card_divisors_le_self z)

private lemma high_prime_forced {d x z p : ℕ} (hx : x≠0) (hz : z≠0) (hp : p.Prime)
    (hcut : 17 ≤ p) (hdiv : p ∣ z) (hle : ∀ q, q.Prime → q ∣ z → p ≤ q)
    (hsmooth : ∀ q, q.Prime → 17 ≤ q → (x*z).factorization q+1 < 17)
    (he : d*z=tau (x*z)) : p ∣ tau x := by
  have hd : p ∣ tau (x*z) := he ▸ dvd_mul_of_dvd_right hdiv d
  rw [tau, Nat.card_divisors (mul_ne_zero hx hz)] at hd
  obtain ⟨q,hq,hdf⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  obtain ⟨hqprime,hqd,_⟩ := Nat.mem_primeFactors.mp hq
  have hv := Nat.le_of_dvd (Nat.succ_pos _) hdf
  have hlo : q<17 := by
    by_contra! hq'
    have := hsmooth q hqprime hq'
    omega
  have hn : ¬q ∣ z := fun h => (by have := hle q hqprime h; omega)
  have hqx := (hqprime.dvd_mul.mp hqd).resolve_right hn
  rw [Nat.factorization_mul hx hz,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hn,add_zero] at hdf
  rw [tau,Nat.card_divisors hx]
  exact hdf.trans (Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hqprime,hqx,hx⟩))

private lemma check_sound (v : ℕ) (good : List ℕ) (fuel : ℕ) :
    ∀ (ps : List (ℕ × ℕ)) (d x z : ℕ), x≠0 → 0<z →
      ps.Pairwise (fun a b => a.1 < b.1) →
      (∀ k ∈ ps, k.1.Prime ∧ k.2 = x.factorization k.1 + 1) →
      (∀ q, q.Prime → q ∣ z → ∃ e, (q,e) ∈ ps) →
      (∀ q, q.Prime → 17 ≤ q → (x*z).factorization q+1 < 17) →
      d*z = tau (x*z) → check v good fuel ps d (tau x) = true → v*(d*z) ∈ good := by
  induction fuel with
  | zero => simp [check]
  | succ fuel ih =>
    intro ps d x z hx hz hsort hval hsup hsmooth he hc
    have hdt := partial_le hz he
    have hlast (hz1 : z=1) (hh : (d != tau x || good.contains (v*d))=true) : v*(d*z) ∈ good := by
      subst z
      simp only [mul_one] at he ⊢
      simpa [he] using hh
    cases ps with
    | nil =>
      apply hlast
      · by_contra hh
        obtain ⟨_,he'⟩ := hsup _ (Nat.minFac_prime hh) (Nat.minFac_dvd z)
        simp at he'
      · simpa [check,not_lt.mpr hdt] using hc
    | cons k ps =>
      rcases k with ⟨p,e⟩
      obtain ⟨hp,hxe⟩ := hval (p,e) (by simp)
      change p.Prime at hp
      change e = x.factorization p + 1 at hxe
      obtain ⟨hstart,htail⟩ := List.pairwise_cons.mp hsort
      have hval' (b) (hb : b ∈ ps) := hval b (List.mem_cons_of_mem _ hb)
      by_cases hcut : 2*tau x < d*p
      · apply hlast _ (by simpa [check,not_lt.mpr hdt,hcut] using hc)
        by_contra hn
        let q := z.minFac
        have hq : q.Prime := Nat.minFac_prime hn
        have hqdiv : q ∣ z := Nat.minFac_dvd z
        obtain ⟨i,hi⟩ := hsup q hq hqdiv
        have hpq : p ≤ q := by
          rcases List.mem_cons.mp hi with heq | hm
          · exact le_of_eq (congrArg Prod.fst heq).symm
          · exact Nat.le_of_lt (hstart (q,i) hm)
        obtain ⟨w,hw⟩ := hqdiv
        have hwpos : 0 < w := by by_contra! hw0; simp [show w=0 by omega] at hw; omega
        have hpart : d*q ≤ tau (x*q) := partial_le hwpos (by simpa [hw,mul_assoc] using he)
        have ht := tau_submul x q
        have hqt : tau q=2 := by simpa using tau_pow hq 1
        rw [hqt] at ht
        have := Nat.mul_le_mul_left d hpq
        omega
      · simp only [check,not_lt.mpr hdt,hcut,if_false,Bool.and_eq_true] at hc
        by_cases hdiv : p ∣ z
        · have hlow (q : ℕ) (hq : q.Prime) (hqd : q ∣ z) : p ≤ q := by
            obtain ⟨j,hj⟩ := hsup q hq hqd
            rcases List.mem_cons.mp hj with h | h
            · exact le_of_eq (congrArg Prod.fst h).symm
            · exact Nat.le_of_lt (hstart (q,j) h)
          have hkeep : ¬(17 ≤ p ∧ ¬p ∣ tau x) := fun ⟨h,n⟩ =>
            n (high_prime_forced hx hz.ne' hp h hdiv hlow hsmooth he)
          obtain ⟨w,hw⟩ := hdiv
          have hwpos : 0 < w := by by_contra! hw0; simp [show w=0 by omega] at hw; omega
          have hx' : x*p≠0 := mul_ne_zero hx hp.ne_zero
          have hval2 : ∀ k ∈ (p,e+1)::ps, k.1.Prime ∧ k.2=(x*p).factorization k.1+1 := by
            rintro ⟨q,j⟩ hj
            rw [Nat.factorization_mul hx hp.ne_zero, Finsupp.add_apply,hp.factorization]
            rcases List.mem_cons.mp hj with h | h
            · cases h
              simpa using And.intro hp hxe
            · have hne : p≠q := Nat.ne_of_lt (hstart (q,j) h)
              simpa [Finsupp.single_apply,hne,hne.symm] using hval' (q,j) h
          have hs2 : ∀ q, q.Prime → q ∣ w → ∃ j, (q,j) ∈ (p,e+1)::ps := by
            intro q hq hqw
            obtain ⟨j,hj⟩ := hsup q hq (by rw [hw]; exact dvd_mul_of_dvd_right hqw p)
            rcases List.mem_cons.mp hj with h | h
            · cases h; exact ⟨e+1,by simp⟩
            · exact ⟨j,List.mem_cons_of_mem _ h⟩
          have ht : tau (x*p)=tau x/e*(e+1) := by simpa [hxe] using tau_mul_prime hx hp
          have hout := ih ((p,e+1)::ps) (d*p) (x*p) w hx' hwpos (List.pairwise_cons.mpr ⟨hstart,htail⟩) hval2 hs2
            (by simpa [hw,mul_assoc] using hsmooth) (by simpa [hw,mul_assoc] using he)
            (by simpa [ht,hkeep] using hc.2)
          simpa [hw,mul_assoc] using hout
        · apply ih ps d x z hx hz htail hval' _ hsmooth he hc.1
          intro q hq hqz
          obtain ⟨j,hj⟩ := hsup q hq hqz
          rcases List.mem_cons.mp hj with hh | hh
          · cases hh; exact (hdiv hqz).elim
          · exact ⟨j,hh⟩

private def value : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p,a)::xs => p^a * value xs

private def exponentAt : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (p,a)::xs, q => (if p=q then a else 0) + exponentAt xs q

private def countTau : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_,a)::xs => (a+1)*countTau xs

private def certified (xs : List (ℕ × ℕ)) : Prop :=
  xs.Pairwise (fun a b => a.1<b.1) ∧ ∀ k ∈ xs, k.1.Prime ∧ k.2 ≤ 59

private instance (xs : List (ℕ × ℕ)) : Decidable (certified xs) := by
  unfold certified
  infer_instance

private lemma exp_zero {xs : List (ℕ × ℕ)} {q : ℕ} (hh : ∀ k ∈ xs, q≠k.1) :
    exponentAt xs q=0 := by
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    obtain ⟨p,a⟩ := k
    have hn := hh (p,a) (by simp)
    have hr := ih (fun k hk => hh k (List.mem_cons_of_mem _ hk))
    simp [exponentAt,hr,Ne.symm hn]

private lemma factor_certificate {xs : List (ℕ × ℕ)} (hv : certified xs) :
    0<value xs ∧ (∀ q, (value xs).factorization q = exponentAt xs q) ∧
    tau (value xs) = countTau xs ∧ ∀ q, exponentAt xs q ≤ 59 := by
  induction xs with
  | nil => simp [value,exponentAt,countTau,tau]
  | cons k xs ih =>
    rcases k with ⟨p,a⟩
    obtain ⟨hs,hall⟩ := hv
    obtain ⟨hlo,hs'⟩ := List.pairwise_cons.mp hs
    obtain ⟨hp,ha⟩ := hall (p,a) (by simp)
    change p.Prime at hp
    change a ≤ 59 at ha
    obtain ⟨hx,hxv,hxt,hxm⟩ := ih ⟨hs',fun j hj => hall j (List.mem_cons_of_mem _ hj)⟩
    have hp0 := exp_zero (q := p) (xs := xs) (fun k hk => Nat.ne_of_lt (hlo k hk))
    have hcop : p.Coprime (value xs) := by
      apply hp.coprime_iff_not_dvd.mpr
      rcases (Nat.factorization_eq_zero_iff _ _).mp ((hxv p).trans hp0) with h | h | h
      · exact (h hp).elim
      · exact h
      · omega
    refine ⟨Nat.mul_pos (pow_pos hp.pos _) hx, ?_, ?_, ?_⟩
    · intro q
      rw [value,Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hx.ne',Finsupp.add_apply,
        Nat.factorization_pow,Finsupp.smul_apply,hp.factorization,hxv,exponentAt]
      by_cases h : p=q <;> simp [h,Ne.symm]
    · rw [value,tau_coprime (hcop.pow_left a),tau_pow hp,hxt,countTau]
    · intro q
      by_cases h : p=q
      · subst q; simpa [exponentAt,hp0] using ha
      · simpa [exponentAt,h] using hxm q

private lemma expAt_large {xs : List (ℕ × ℕ)}
    (hs : xs.Pairwise (fun a b => a.1 < b.1))
    (hh : ∀ k∈xs, 17 ≤ k.1 → k.2 ≤ 1) {p : ℕ} (hp : 17≤p) : exponentAt xs p ≤ 1 := by
  induction xs with
  | nil => simp [exponentAt]
  | cons k xs ih =>
    obtain ⟨q,a⟩ := k
    obtain ⟨hl,hs'⟩ := List.pairwise_cons.mp hs
    by_cases he : q=p
    · subst p
      have hzero := exp_zero (fun k hk => Nat.ne_of_lt (hl k hk))
      simpa [exponentAt,hzero] using hh (q,a) (by simp) hp
    · simpa [exponentAt,he] using ih hs' (fun j hj => hh j (List.mem_cons_of_mem _ hj))

private def primes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

private def rows : List (List (ℕ × ℕ)) :=
  [[],
   [(2, 1)],
   [(2, 3)],
   [(2, 2), (3, 1)],
   [(2, 4), (5, 1)],
   [(2, 5), (3, 1)],
   [(2, 4), (3, 1), (5, 1)],
   [(2, 6), (5, 1), (7, 1)],
   [(2, 4), (3, 2), (5, 2)],
   [(2, 6), (3, 2), (7, 1)],
   [(2, 6), (3, 2), (5, 1), (7, 1)],
   [(2, 11), (3, 1), (5, 1), (7, 1)],
   [(2, 9), (3, 1), (5, 2), (7, 1)],
   [(2, 11), (3, 3), (7, 1)],
   [(2, 8), (3, 5), (7, 1)],
   [(2, 8), (3, 4), (5, 1), (7, 1)],
   [(2, 6), (3, 4), (5, 2), (7, 2)],
   [(2, 14), (3, 3), (5, 2), (7, 1)],
   [(2, 11), (3, 8), (7, 1)],
   [(2, 13), (3, 5), (7, 2)],
   [(2, 14), (3, 5), (5, 1), (7, 1)],
   [(2, 13), (3, 4), (5, 1), (7, 2)],
   [(2, 15), (3, 5), (5, 1), (7, 1)],
   [(2, 11), (3, 6), (5, 1), (7, 2)],
   [(2, 12), (3, 5), (5, 1), (7, 1), (13, 1)],
   [(2, 9), (3, 6), (5, 2), (7, 2)],
   [(2, 11), (3, 7), (5, 2), (7, 2)],
   [(2, 19), (3, 3), (5, 4), (7, 1)],
   [(2, 17), (3, 6), (5, 1), (7, 3)],
   [(2, 16), (3, 6), (5, 1), (7, 2), (17, 1)],
   [(2, 16), (3, 7), (5, 1), (7, 2), (17, 1)],
   [(2, 22), (3, 4), (5, 5), (7, 1), (23, 1)],
   [(2, 19), (3, 6), (5, 4), (7, 4)],
   [(2, 22), (3, 7), (5, 1), (7, 2), (17, 1), (23, 1)],
   [(2, 20), (3, 9), (5, 2), (7, 3), (17, 1)],
   [(2, 27), (3, 4), (5, 6), (7, 3), (23, 1)],
   [(2, 25), (3, 7), (5, 5), (7, 4), (13, 1)],
   [(2, 31), (3, 9), (5, 3), (7, 3), (17, 1)],
   [(2, 34), (3, 10), (5, 5), (7, 4), (11, 1), (17, 1)],
   [(2, 38), (3, 10), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1)],
   [(2, 44), (3, 14), (5, 5), (7, 3), (11, 1), (13, 1), (17, 1)],
   [(2, 46), (3, 11), (5, 4), (7, 3), (11, 1), (13, 1), (17, 1), (47, 1)],
   [(2, 43), (3, 12), (5, 4), (7, 3), (11, 2), (13, 2), (17, 1)],
   [(2, 52), (3, 17), (5, 5), (7, 3), (11, 1), (13, 1), (17, 1), (53, 1)],
   [(2, 59), (3, 20), (5, 6), (7, 5), (11, 1), (13, 1), (17, 1), (53, 1)]]

private def start (xs : List (ℕ × ℕ)) := primes.map (fun p => (p,exponentAt xs p+1))

private lemma in_primes {q : ℕ} (hp : q.Prime) (hq : q ≤ 101) : q∈primes := by
  have hh : ∀ i : Fin 102, i.val.Prime → i.val ∈ primes := by decide
  exact hh ⟨q,by omega⟩ hp

private lemma initial_order (xs : List (ℕ × ℕ)) : (start xs).Pairwise (fun a b => a.1 < b.1) := by
  have : primes.Pairwise (·<·) := by decide
  exact this.map _ (fun _ _ h => h)

private lemma rows_values : rows.map value = entries := by decide
private lemma rows_valid : ∀ xs ∈ rows, certified xs := by decide
private lemma rows_bound : ∀ xs ∈ rows, 4*(countTau xs)^2 < 2^42 := by decide
private lemma rows_large : ∀ xs∈rows, ∀ k∈xs, 17 ≤ k.1 → k.2 ≤ 1 := by decide
private lemma rows_down : ∀ xs ∈ rows, value xs = 1 ∨
    (countTau xs ∣ value xs ∧ 1<countTau xs ∧ value xs / countTau xs ∈ entries) := by decide

private lemma checked_row {xs : List (ℕ × ℕ)} (hx : xs∈rows)
    (hcheck : check (value xs) entries 85 (start xs) 1 (countTau xs)=true) {d : ℕ}
    (hd : 0<d) (he : d=tau (value xs*d)) : value xs*d ∈ entries := by
  obtain ⟨hpos,hext,htau,hmax⟩ := factor_certificate (rows_valid xs hx)
  rw [← Nat.one_mul d] at ⊢
  apply check_sound (value xs) entries 85 (start xs) 1 (value xs) d hpos.ne' hd (initial_order _) _ _ _ (by simpa using he) (htau ▸ hcheck)
  · intro k hk
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
    have hpr : ∀ q∈primes, Nat.Prime q := by decide
    exact ⟨hpr p hp,by simp [hext]⟩
  · intro q hq hdiv
    have hle := bounded_support hpos.ne' hd he (htau ▸ rows_bound xs hx) (fun p => (hext p) ▸ hmax p) q hq hdiv
    exact ⟨_, List.mem_map_of_mem (f := fun p => (p,exponentAt xs p+1)) (in_primes hq hle)⟩

  · intro q hq h17
    have hl := expAt_large (rows_valid xs hx).1 (rows_large xs hx) h17
    have hd0 := (bound_multiplier hd he).trans_lt (htau ▸ rows_bound xs hx)
    have heq : d.factorization q < 11 := by
      by_contra! h
      have hpow : 17^11 ≤ q^(d.factorization q) :=
        (Nat.pow_le_pow_left h17 11).trans (Nat.pow_le_pow_right hq.pos h)
      have hh := Nat.le_of_dvd hd (Nat.ordProj_dvd d q)
      omega
    rw [Nat.factorization_mul hpos.ne' hd.ne',Finsupp.add_apply,hext]
    omega

private lemma classification (hc : ∀ xs ∈ rows,
    check (value xs) entries 85 (start xs) 1 (countTau xs) = true) :
    type_of% @OMA.S_oeis_a330816.main := by
  have hasrow {v : ℕ} (hv : v∈entries) : ∃ xs∈rows, value xs = v := by
    rw [← rows_values] at hv
    exact List.mem_map.mp hv
  have backwards {n : ℕ} (hn : 0<n) (hv : step n ∈ entries) : n ∈ entries := by
    by_cases hh : tau n ∣ n
    · have hstep : step n = n/tau n := if_pos hh
      obtain ⟨xs,hx,he⟩ := hasrow hv
      have hprod : value xs*tau n=n := by rw [he,hstep]; exact Nat.div_mul_cancel hh
      have hd : 0 < tau n := by exact Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩⟩
      exact hprod ▸ checked_row hx (hc xs hx) hd (by rw [hprod])
    · simpa [step,hh] using hv
  have pos_step {n : ℕ} (hn : 0<n) : 0<step n := by
    by_cases hh : tau n ∣ n
    · have ht : 0<tau n := Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩⟩
      exact (show step n=n/tau n from if_pos hh) ▸ Nat.div_pos (Nat.le_of_dvd hn hh) ht
    · simpa [step,hh] using hn
  intro n hn
  constructor
  · rintro ⟨k,hk⟩
    induction k generalizing n with
    | zero => simp [show n=1 from hk,entries]
    | succ k ih =>
      exact backwards hn (ih (step n) (pos_step hn) (by simpa [Function.iterate_succ_apply] using hk))
  · intro hv
    induction n using Nat.strong_induction_on with
    | h n ih =>
      obtain ⟨xs,hx,he⟩ := hasrow hv
      subst n
      obtain h | ⟨hdiv,hbig,hmem⟩ := rows_down xs hx
      · exact ⟨0,h⟩
      obtain ⟨_,_,ht,_⟩ := factor_certificate (rows_valid xs hx)
      have hs : step (value xs) = value xs/countTau xs := by
        unfold step
        change (if tau (value xs) ∣ value xs then value xs/tau (value xs) else _) = _
        rw [ht,if_pos hdiv]
      obtain ⟨k,hk⟩ := ih _ (Nat.div_lt_self hn hbig) (Nat.div_pos (Nat.le_of_dvd hn hdiv) (by omega)) hmem
      exact ⟨k+1,by simpa [Function.iterate_succ_apply,hs] using hk⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 120000000 in
private lemma rows_checked : ∀ xs ∈ rows,
    check (value xs) entries 85 (start xs) 1 (countTau xs) = true := by
  intro xs h
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change check 1 entries 85
      [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 1 = true
    decide +kernel
  · change check 2 entries 85
      [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 2 = true
    decide +kernel
  · change check 8 entries 85
      [(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 4 = true
    decide +kernel
  · change check 12 entries 85
      [(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 6 = true
    decide +kernel
  · change check 80 entries 85
      [(2, 5), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 10 = true
    decide +kernel
  · change check 96 entries 85
      [(2, 6), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 12 = true
    decide +kernel
  · change check 240 entries 85
      [(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 20 = true
    decide +kernel
  · change check 2240 entries 85
      [(2, 7), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 28 = true
    decide +kernel
  · change check 3600 entries 85
      [(2, 5), (3, 3), (5, 3), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 45 = true
    decide +kernel
  · change check 4032 entries 85
      [(2, 7), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 42 = true
    decide +kernel
  · change check 20160 entries 85
      [(2, 7), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 84 = true
    decide +kernel
  · change check 215040 entries 85
      [(2, 12), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 96 = true
    decide +kernel
  · change check 268800 entries 85
      [(2, 10), (3, 2), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 120 = true
    decide +kernel
  · change check 387072 entries 85
      [(2, 12), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 96 = true
    decide +kernel
  · change check 435456 entries 85
      [(2, 9), (3, 6), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 108 = true
    decide +kernel
  · change check 725760 entries 85
      [(2, 9), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 180 = true
    decide +kernel
  · change check 6350400 entries 85
      [(2, 7), (3, 5), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 315 = true
    decide +kernel
  · change check 77414400 entries 85
      [(2, 15), (3, 4), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 360 = true
    decide +kernel
  · change check 94058496 entries 85
      [(2, 12), (3, 9), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 216 = true
    decide +kernel
  · change check 97542144 entries 85
      [(2, 14), (3, 6), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 252 = true
    decide +kernel
  · change check 139345920 entries 85
      [(2, 15), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 360 = true
    decide +kernel
  · change check 162570240 entries 85
      [(2, 14), (3, 5), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 420 = true
    decide +kernel
  · change check 278691840 entries 85
      [(2, 16), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 384 = true
    decide +kernel
  · change check 365783040 entries 85
      [(2, 12), (3, 7), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 504 = true
    decide +kernel
  · change check 452874240 entries 85
      [(2, 13), (3, 6), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 624 = true
    decide +kernel
  · change check 457228800 entries 85
      [(2, 10), (3, 7), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 630 = true
    decide +kernel
  · change check 5486745600 entries 85
      [(2, 12), (3, 8), (5, 3), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 864 = true
    decide +kernel
  · change check 61931520000 entries 85
      [(2, 20), (3, 4), (5, 5), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 800 = true
    decide +kernel
  · change check 163870801920 entries 85
      [(2, 18), (3, 7), (5, 2), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 1008 = true
    decide +kernel
  · change check 198985973760 entries 85
      [(2, 17), (3, 7), (5, 2), (7, 3), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 1428 = true
    decide +kernel
  · change check 596957921280 entries 85
      [(2, 17), (3, 8), (5, 2), (7, 3), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 1632 = true
    decide +kernel
  · change check 170930995200000 entries 85
      [(2, 23), (3, 5), (5, 6), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 2760 = true
    decide +kernel
  · change check 573547806720000 entries 85
      [(2, 20), (3, 7), (5, 5), (7, 5), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 3500 = true
    decide +kernel
  · change check 878722060124160 entries 85
      [(2, 23), (3, 8), (5, 2), (7, 3), (11, 1), (13, 1), (17, 2), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 4416 = true
    decide +kernel
  · change check 3008667923251200 entries 85
      [(2, 21), (3, 10), (5, 3), (7, 4), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 5040 = true
    decide +kernel
  · change check 1340099002368000000 entries 85
      [(2, 28), (3, 5), (5, 7), (7, 4), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 7840 = true
    decide +kernel
  · change check 7157876627865600000 entries 85
      [(2, 26), (3, 8), (5, 6), (7, 5), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 12480 = true
    decide +kernel
  · change check 30808759534092288000 entries 85
      [(2, 32), (3, 10), (5, 4), (7, 4), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 10240 = true
    decide +kernel
  · change check 1423364690475063705600000 entries 85
      [(2, 35), (3, 11), (5, 6), (7, 5), (11, 2), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 46200 = true
    decide +kernel
  · change check 1691770603536075718656000 entries 85
      [(2, 39), (3, 11), (5, 4), (7, 4), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 54912 = true
    decide +kernel
  · change check 219253470218275413137817600000 entries 85
      [(2, 45), (3, 15), (5, 6), (7, 4), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 129600 = true
    decide +kernel
  · change check 305330758526190945703034880000 entries 85
      [(2, 47), (3, 12), (5, 5), (7, 4), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 2), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 180480 = true
    decide +kernel
  · change check 348369402680148711985643520000 entries 85
      [(2, 44), (3, 13), (5, 5), (7, 4), (11, 3), (13, 3), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 205920 = true
    decide +kernel
  · change check 80320439265882141747255548313600000 entries 85
      [(2, 53), (3, 18), (5, 6), (7, 4), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 366336 = true
    decide +kernel
  · change check 68008922335207727060236217868091392000000 entries 85
      [(2, 60), (3, 21), (5, 7), (7, 6), (11, 2), (13, 2), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 2), (59, 1), (61, 1), (67, 1), (71, 1), (73, 1), (79, 1), (83, 1), (89, 1), (97, 1), (101, 1)] 1 846720 = true
    decide +kernel

theorem OMA.solution : type_of% @OMA.S_oeis_a330816.main := classification rows_checked
