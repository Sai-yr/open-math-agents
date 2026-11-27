import OMAStatements.S_oeis_a384309

namespace OMA.S_oeis_a384309

private def tick (a b : Digit) : ℕ := if a=b then 1 else 0
private def hits (d : Digit) : ℕ → ℕ
  | 0 => 0
  | n+1 => hits d n+tick (leading (n+1)) d

private theorem lead_block (k j r : ℕ) (hj : 1 ≤ j) (hJ : j ≤ 9) (hr : r < 10^k) :
    (leading (j*10^k+r)).val=j-1 := by
  have hB : 0 < 10^k := by positivity
  have hl : 10^k ≤ j*10^k+r := by nlinarith [Nat.mul_le_mul_right (10^k) hj]
  have hu : j*10^k+r < 10^(k+1) := by
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (10^k) hJ]
  simp only [leading,Nat.log_eq_of_pow_le_of_lt_pow hl hu]
  rw [Nat.mul_comm j (10^k),Nat.mul_add_div hB,Nat.div_eq_of_lt hr,Nat.add_zero,Nat.mod_eq_of_lt (by omega)]

private theorem band (d : Digit) (k j : ℕ) (hj : 1 ≤ j) (hJ : j ≤ 9) :
    ∀ r ≤ 10^k, hits d (j*10^k-1+r) =
      hits d (j*10^k-1)+(if d.val+1=j then r else 0) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    intro hr
    have hB : 0 < 10^k := by positivity
    have hp : 0 < j*10^k := Nat.mul_pos (by omega) hB
    have he : leading (j*10^k-1+r+1)=d ↔ d.val+1=j := by
      rw [show j*10^k-1+r+1=j*10^k+r by omega, ← Fin.val_inj,lead_block k j r hj hJ (by omega)]
      omega
    rw [show j*10^k-1+(r+1)=j*10^k-1+r+1 by omega,hits,ih (by omega),tick]
    by_cases hd : d.val+1=j <;> simp [he,hd]
    omega

private theorem bands (d : Digit) (k : ℕ) : ∀ j ≤ 9,
    hits d ((j+1)*10^k-1) = hits d (10^k-1)+(if d.val<j then 10^k else 0) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro hj
    have hh := band d k (j+1) (by omega) hj (10^k) le_rfl
    have hB : 0 < 10^k := by positivity
    have hp : 0 < (j+1)*10^k := Nat.mul_pos (by omega) hB
    rw [show (j+1+1)*10^k-1=(j+1)*10^k-1+10^k by rw [Nat.add_mul]; simp; omega,hh,ih (by omega)]
    split_ifs <;> omega

private theorem common (d : Digit) (k : ℕ) : 9*hits d (10^k-1)=10^k-1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := bands d k 9 le_rfl
    rw [if_pos d.isLt] at hh
    rw [pow_succ,show 10^k*10=(9+1)*10^k by ring,hh]
    have hp : 0 < 10^k := by positivity
    omega

private def cap (k : ℕ) (d : Digit) := if d=0 then 9*10^k else if d=8 then 10^k-1 else 2*10^k-1
private def received (u : Digit → ℕ) (d : Digit) := ∑ e, hits d (u e)

private theorem cap_sum (k : ℕ) : (∑ d, cap k d)=24*10^k-8 := by
  have hp : 0 < 10^k := by positivity
  simp (disch := decide +kernel) [Fin.sum_univ_succ,cap,if_pos,if_neg]
  omega

private theorem cap_balance (k : ℕ) (d : Digit) :
    cap k d+tick 8 d=received (cap k) d+tick 0 d := by
  have hp : 0 < 10^k := by positivity
  have h2 := bands d k 1 (by decide)
  have h9 := bands d k 8 (by decide)
  have hd : leading (9*10^k)=8 := Fin.ext (by simpa using lead_block k 9 0 (by decide) (by decide) hp)
  have H9 : hits d (9*10^k) = hits d (10^k-1)+(if d.val<8 then 10^k else 0)+tick 8 d := by
    conv_lhs => rw [show 9*10^k=(9*10^k-1)+1 by omega,hits]
    rw [show 9*10^k-1+1=9*10^k by omega,hd,h9]
  have hc := common d k
  fin_cases d <;> simp (disch := decide +kernel) [received,Fin.sum_univ_succ,cap,tick,if_pos,if_neg] at H9 h2 hc ⊢ <;> omega

private theorem cap_last (k : ℕ) (hk : 0 < k) (d : Digit) :
    leading (cap k d) = if d=0 ∨ d=8 then 8 else 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hp : 0 < 10^k := by positivity
    have hp' : 0 < 10^(k+1) := by positivity
    by_cases hd : d=0
    · simp [cap,hd]
      apply Fin.ext
      simpa using lead_block (k+1) 9 0 (by decide) (by decide) hp'
    · by_cases he : d=8
      · simp [cap,he]
        apply Fin.ext
        have ha := lead_block k 9 (10^k-1) (by decide) (by decide) (by omega)
        rw [show 10^(k+1)-1=9*10^k+(10^k-1) by rw [pow_succ]; omega]
        exact ha
      · simp [cap,hd,he]
        apply Fin.ext
        have ha := lead_block (k+1) 1 (10^(k+1)-1) (by decide) (by decide) (by omega)
        simpa [show 2*10^(k+1)-1=10^(k+1)+(10^(k+1)-1) by omega] using ha

private abbrev value (t : ℕ) := (state t).1
private abbrev used (t : ℕ) := (state t).2
private abbrev src (t : ℕ) := leading (value t)

private theorem used_step (t : ℕ) (i : Digit) : used (t+1) i=used t i+tick i (src t) := rfl
private theorem value_step (t : ℕ) : value (t+1)=used t (src t)+1 := rfl

private theorem used_mono (i : Digit) : Monotone (fun t => used t i) :=
  monotone_nat_of_le_succ (fun t => by rw [used_step]; omega)

private theorem total_used (t : ℕ) : (∑ i, used t i)=t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [used_step,Finset.sum_add_distrib,ih,tick]
    simp

private theorem received_step (t : ℕ) (d : Digit) :
    received (used (t+1)) d = received (used t) d+tick (src (t+1)) d := by
  have row (e : Digit) : hits d (used (t+1) e) = hits d (used t e) +
      if e=src t then tick (src (t+1)) d else 0 := by
    by_cases h : e=src t
    · subst e
      simp [used_step,tick,hits,src,value_step]
      rfl
    · simp [used_step,tick,h]
  simp only [received,row,Finset.sum_add_distrib]
  simp

private theorem balance (t : ℕ) (d : Digit) :
    used t d+tick (src t) d = received (used t) d+tick 0 d := by
  induction t with
  | zero =>
    have h : src 0=0 := by decide
    simp [h,used,state,received,hits]
  | succ t ih =>
    rw [used_step,received_step]
    have h : tick d (src t)=tick (src t) d := by simp only [tick,eq_comm]
    omega

private theorem hits_mono (d : Digit) : Monotone (hits d) :=
  monotone_nat_of_le_succ (fun n => by rw [hits]; omega)

private theorem receipts_mono {u v : Digit → ℕ} (h : ∀ i, u i≤v i) (d : Digit) :
    received u d ≤ received v d := Finset.sum_le_sum (fun i _ => hits_mono d (h i))

private theorem last_receipt {u v : Digit → ℕ} (le : ∀ i, u i≤v i)
    {e d : Digit} (hl : leading (v e)=d) (hr : received u d=received v d) : u e=v e := by
  by_contra h
  have gap : u e≤v e-1 := by have := le e; omega
  have H : hits d (u e) < hits d (v e) := by
    have hm := hits_mono d gap
    have hs := congrArg (hits d) (show v e=(v e-1)+1 by omega)
    rw [hits,show v e-1+1=v e by omega,hl,tick,if_pos rfl] at hs
    omega
  have hsum : received u d < received v d :=
    Finset.sum_lt_sum (fun i _ => hits_mono d (le i)) ⟨e,Finset.mem_univ _,H⟩
  omega

-- The remaining prescribed departures can never stop at an exhausted
-- digit before all departures are exhausted. Equality of receipts at
-- digit 9 forces digit 1 to be exhausted, then all the other digits.
private theorem exhausted (k t : ℕ) (hk : 0 < k) (le : ∀ d, used t d≤cap k d)
    (he : used t (src t)=cap k (src t)) : ∀ d, used t d=cap k d := by
  have cur : src t=8 := by
    by_contra h
    have hb := balance t (src t)
    have hc := cap_balance k (src t)
    have hm := receipts_mono le (src t)
    simp [tick,Ne.symm h] at hb hc
    omega
  rw [cur] at he
  have same (d : Digit) (hd : used t d=cap k d) :
      received (used t) d=received (cap k) d := by
    have a := balance t d
    have b := cap_balance k d
    rw [cur,hd] at a
    omega
  have first : used t 0=cap k 0 := last_receipt le (by simpa using cap_last k hk 0) (same 8 he)
  intro d
  by_cases h : d=0 ∨ d=8
  · rcases h with rfl | rfl <;> assumption
  · exact last_receipt le (by simpa [h] using cap_last k hk d) (same 0 first)

private theorem within_cap (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : t≤24*10^k-8) :
    ∀ d, used t d≤cap k d := by
  induction t with
  | zero => intro d; exact Nat.zero_le _
  | succ t ih =>
    have le := ih (by omega)
    have h : used t (src t)<cap k (src t) := by
      by_contra! hh
      have eq := exhausted k t hk le (by have := le (src t); omega)
      have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset Digit)) rfl (fun i _ => eq i)
      rw [total_used,cap_sum] at hsum
      omega
    intro d
    rw [used_step,tick]
    split_ifs with he
    · subst d; omega
    · simpa using le d

private theorem endpoint (k : ℕ) (hk : 0 < k) (d : Digit) :
    used (24*10^k-8) d=cap k d := by
  have h := within_cap k hk (24*10^k-8) le_rfl
  by_contra hn
  have hh : used (24*10^k-8) d<cap k d := by have := h d; omega
  have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset Digit))
    (fun i _ => h i) ⟨d,Finset.mem_univ _,hh⟩
  rw [total_used,cap_sum] at hsum
  omega

private theorem cap_low (k : ℕ) (d : Digit) : 10^k-1 ≤ cap k d := by
  simp only [cap]
  split_ifs <;> omega

private theorem last_value (k : ℕ) (hk : 0 < k) : value (24*10^k-8)=10^k-1 := by
  let T := 24*10^k-8
  have hb : 10 ≤ 10^k := by simpa using (Nat.pow_le_pow_right (n := 10) (by decide) hk)
  have h8 : cap k 8=10^k-1 := by norm_num [cap,← Fin.val_inj]
  let P (t : ℕ) := cap k 8 ≤ used t 8
  have hex : ∃ t, P t := ⟨T,(endpoint k hk 8).ge⟩
  let s := Nat.find hex
  have hs : P s := Nat.find_spec hex
  have hst : s≤T := Nat.find_min' hex (endpoint k hk 8).ge
  have hpos : 0 < s := by
    by_contra! hz
    have : s=0 := by omega
    rw [this] at hs
    change cap k 8 ≤ 0 at hs
    omega
  obtain ⟨t,ht⟩ : ∃ t, s=t+1 := ⟨s-1,by omega⟩
  have htprev : ¬ P t := Nat.find_min hex (by change t<s; omega)
  change ¬ cap k 8 ≤ used t 8 at htprev
  rw [ht] at hs hst
  change cap k 8 ≤ used (t+1) 8 at hs
  have ht8 := (within_cap k hk (t+1) hst 8).antisymm hs
  have hd : src t=8 := by
    by_contra h
    rw [used_step,tick,if_neg (Ne.symm h),add_zero] at hs
    omega
  have hv : value (t+1)=cap k 8 := by
    rw [value_step,hd,← ht8,used_step,tick,if_pos hd.symm]
  have hsrc : src (t+1)=8 := by
    change leading (value (t+1))=8
    rw [hv,cap_last _ hk]
    simp
  have hfull := exhausted k (t+1) hk (within_cap k hk (t+1) hst) (by rw [hsrc,ht8])
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset Digit)) rfl (fun i _ => hfull i)
  rw [total_used,cap_sum] at hsum
  rw [← hsum,hv,h8]

private theorem after (k : ℕ) (hk : 0 < k) {s : ℕ} (hs : 24*10^k-8 ≤ s) :
    10^k ≤ value (s+1) := by
  rw [value_step]
  have h : used (24*10^k-8) (src s) ≤ used s (src s) := used_mono (src s) hs
  rw [endpoint _ hk] at h
  have := cap_low k (src s)
  omega

-- By time t, the outputs generated by digit d are precisely the
-- integers 1 through its departure count, each appearing once.
private theorem occurrences (x : ℕ) (hx : 0 < x) (t : ℕ) :
    (∑ s ∈ Finset.range (t+1), if value s=x then 1 else 0) =
      (if x=1 then 1 else 0)+(∑ d, if x≤used t d then 1 else 0) := by
  induction t with
  | zero =>
    rw [Finset.sum_range_succ]
    simp only [Finset.sum_range_zero,zero_add]
    change (if 1=x then 1 else 0)=(if x=1 then 1 else 0)+∑ _ : Digit, if x≤0 then 1 else 0
    simp [Nat.not_le_of_gt hx,eq_comm]
  | succ t ih =>
    rw [Finset.sum_range_succ,ih]
    have hh (d : Digit) : (if x≤used (t+1) d then 1 else 0) =
        (if x≤used t d then 1 else 0) +
        (if d=src t then (if value (t+1)=x then 1 else 0) else 0) := by
      rw [used_step,value_step,tick]
      by_cases h : d=src t
      · subst d
        split_ifs <;> omega
      · simp [h]
    simp only [hh,Finset.sum_add_distrib]
    simp [Nat.add_assoc]

end OMA.S_oeis_a384309

open OMA.S_oeis_a384309 in
theorem OMA.solution : type_of% @OMA.S_oeis_a384309.main := by
  constructor
  · intro x hx
    have hb : x < 10^x := Nat.lt_pow_self (by decide)
    refine ⟨24*10^x-8+1,?_⟩
    intro m hm
    obtain ⟨t,ht⟩ : ∃ t, m=t+1 := ⟨m-1,by omega⟩
    subst m
    have reached (d : Digit) : x ≤ used t d := by
      have h : used (24*10^x-8) d ≤ used t d := used_mono d (by omega)
      rw [endpoint x hx] at h
      have := cap_low x d
      omega
    rw [Finset.card_filter]
    change (∑ s ∈ Finset.range (t+1), if value s=x then 1 else 0)=_
    rw [occurrences x hx t]
    simp only [if_pos (reached _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
    split_ifs <;> decide
  · intro k hk
    have hp : 0 < 10^k := by positivity
    refine ⟨?_,?_⟩
    · change value (24*10^k-7-1)=10^k-1
      rw [show 24*10^k-7-1=24*10^k-8 by omega,last_value k hk]
    · intro n hn
      change 10^k ≤ value (n-1)
      rw [show n-1=(n-2)+1 by omega]
      exact after k hk (by omega)
