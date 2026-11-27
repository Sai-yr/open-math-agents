import OMAStatements.S_mo_472052

open OMA.S_mo_472052 Filter Set
open scoped Topology BigOperators

private abbrev History := ℕ → Bool
private abbrev fresh : History := fun _ => true

private lemma at_most (s t n : ℕ) (h : History) : continuations s t n h ≤ 2^n := by
  induction n generalizing h with
  | zero => simp [continuations]
  | succ n ih =>
    have a := ih (push true h)
    have b := ih (push false h)
    simp only [continuations, pow_succ]; split <;> omega

private lemma at_least (s t n : ℕ) (h : History) : 1 ≤ continuations s t n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => exact (ih (push true h)).trans (Nat.le_add_right _ _)

/-- The second history agrees in the most recent k places, then contains only ones. -/
private def dominates (k : ℕ) (h f : History) : Prop :=
  (∀ i<k, h i=f i) ∧ (∀ i : ℕ, k ≤ i → f i = true)

private lemma dominates_push {k : ℕ} {h f : History} (d : dominates k h f) (b : Bool) :
    dominates (k+1) (push b h) (push b f) := by
  constructor
  · intro i hi; cases i with
    | zero => rfl
    | succ i => exact d.1 i (by omega)
  · intro i hi; cases i with
    | zero => omega
    | succ i => exact d.2 i (by omega)

private lemma zero_mono {k s t : ℕ} {h f : History} (d : dominates k h f)
    (z : allowZero s t h=true) : allowZero s t f=true := by
  by_cases a : k≤t+s-1
  · simp [allowZero,d.2 _ a]
  by_cases b : k≤s+s-1
  · simp [allowZero,d.2 _ b]
  simpa only [allowZero, d.1 _ (show t+s-1<k by omega),
    d.1 _ (show s+s-1<k by omega), d.1 _ (show s-1<k by omega)] using z

private lemma dominate_count (s t n : ℕ) {k : ℕ} {h f : History} (d : dominates k h f) :
    continuations s t n h ≤ continuations s t n f := by
  induction n generalizing k h f with
  | zero => rfl
  | succ n ih =>
    have a := ih (dominates_push d true)
    have b := ih (dominates_push d false)
    simp only [continuations]
    by_cases z : allowZero s t h=true
    · simp only [z,zero_mono d z,if_true]; omega
    · rw [if_neg z]; exact a.trans (Nat.le_add_right _ _)

private lemma agree_count (s t n : ℕ) {h f : History}
    (d : ∀ i<max t s+s, h i=f i) : continuations s t n h = continuations s t n f := by
  induction n generalizing h f with
  | zero => rfl
  | succ n ih =>
    have e (b : Bool) : ∀ i<max t s+s, push b h i=push b f i := by
      intro i hi; cases i with | zero => rfl | succ i => exact d i (by omega)
    by_cases emp : max t s+s=0
    · have hs : s=0 := by omega
      have ht : t=0 := by omega
      subst s; subst t
      simp [continuations,allowZero,ih (e true),ih (e false)]
    · have z : allowZero s t h=allowZero s t f := by
        simp only [allowZero,d _ (show t+s-1<max t s+s by omega),
          d _ (show s+s-1<max t s+s by omega), d _ (show s-1<max t s+s by omega)]
      simp only [continuations,z,ih (e true),ih (e false)]

private def fill (k : ℕ) (w h : History) (i : ℕ) : Bool :=
  if i<k then w i else h (i-k)

@[simp] private lemma fill_zero (w h : History) : fill 0 w h=h := by funext i; simp [fill]

private lemma fill_succ (k : ℕ) (w h : History) : fill (k+1) w h=fill k w (push (w k) h) := by
  funext i
  by_cases a : i<k
  · simp [fill,a,show i<k+1 by omega]
  by_cases b : i=k
  · subst i; simp [fill,push]
  · have c : i-k=(i-(k+1))+1 := by omega
    simp [fill,a,show ¬ i<k+1 by omega,c,push]

private lemma true_branch (s t k n : ℕ) (h : History) :
    continuations s t n (fill k fresh h) ≤ continuations s t (k+n) h := by
  induction k generalizing h with
  | zero => simpa only [fill_zero, Nat.zero_add] using (le_rfl : continuations s t n h ≤ _)
  | succ k ih =>
    rw [fill_succ,Nat.succ_add]
    exact (ih (push true h)).trans (Nat.le_add_right _ _)

private lemma upper_split (s t k n : ℕ) (h : History) :
    continuations s t (k+n) h ≤ continuations s t k h * count s t n := by
  induction k generalizing h with
  | zero =>
    simpa [continuations,count] using
      (dominate_count s t n (k:=0) (h:=h) (f:=fresh) ⟨by simp,by simp⟩)
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [continuations]
    have a := ih (push true h)
    have b := ih (push false h)
    by_cases z : allowZero s t h=true
    · simpa only [z,if_true,Nat.add_mul] using Nat.add_le_add a b
    · simpa only [if_neg z,Nat.add_zero] using a

private lemma lower_split (s t k n : ℕ) (h : History) :
    continuations s t k h * count s t n ≤ continuations s t (k+(max t s+s+n)) h := by
  induction k generalizing h with
  | zero =>
    have eq := agree_count s t n (h:=fill (max t s+s) fresh h) (f:=fresh)
      (fun i hi => by simp [fill,hi])
    simpa [continuations,count, eq] using true_branch s t (max t s+s) n h
  | succ k ih =>
    rw [Nat.succ_add]
    simp only [continuations]
    have a := ih (push true h)
    have b := ih (push false h)
    by_cases z : allowZero s t h=true
    · simpa only [z,if_true,Nat.add_mul] using Nat.add_le_add a b
    · simpa only [if_neg z,Nat.add_zero] using a

private lemma full_child {s t n : ℕ} {h : History} (e : continuations s t (n+1) h=2^(n+1)) (b : Bool) :
    continuations s t n (push b h)=2^n ∧ allowZero s t h=true := by
  have a := at_most s t n (push true h)
  have c := at_most s t n (push false h)
  have p : 0<2^n := by positivity
  simp only [continuations, pow_succ] at e
  split at e <;> cases b <;> simp_all <;> omega

private lemma full_follow {s t : ℕ} (k n : ℕ) (w h : History)
    (e : continuations s t (k+n) h=2^(k+n)) : continuations s t n (fill k w h)=2^n := by
  induction k generalizing h with
  | zero => simpa only [fill_zero, Nat.zero_add] using e
  | succ k ih =>
    rw [Nat.succ_add] at e
    rw [fill_succ]
    exact ih _ (full_child e (w k)).1

private lemma strict_count (s t : ℕ) (hs : 0<s) (ht : 0<t) :
    count s t (max t s+s+1)<2^(max t s+s+1) := by
  apply lt_of_le_of_ne (at_most s t _ _)
  intro e
  let w : History := fun i => decide (i=s-1)
  have f := full_follow (s:=s) (t:=t) (max t s+s) 1 w fresh e
  have z := (full_child (n:=0) f true).2
  simp [allowZero,fill,w,
    show t+s-1<max t s+s by omega,show s+s-1<max t s+s by omega,
    show s-1<max t s+s by omega,show t+s-1≠s-1 by omega,show s+s-1≠s-1 by omega] at z

private def weight (older recent : Bool) : ℕ :=
  if recent then if older then 21 else 12 else 16

private def potential (s : ℕ) (h : History) : ℕ :=
  ∏ i ∈ Finset.range s, weight (h (i+s)) (h i)

private lemma potential_le (s : ℕ) (h : History) : potential s h ≤ 21^s := by
  calc
    _ ≤ ∏ _i ∈ Finset.range s, (21:ℕ) := by
      apply Finset.prod_le_prod' (fun i _ => ?_)
      cases h (i+s) <;> cases h i <;> decide
    _ = _ := by simp

private lemma potential_fresh (s : ℕ) : potential s fresh=21^s := by
  simp [potential,weight,fresh]

private lemma weighted_step (s t : ℕ) (h : History) :
    7*potential (s+1) h ≤ 4*(potential (s+1) (push true h) +
      if allowZero (s+1) t h then potential (s+1) (push false h) else 0) := by
  let p := ∏ i ∈ Finset.range s, weight (h (i+(s+1))) (h i)
  have old : potential (s+1) h=p*weight (h (s+(s+1))) (h s) :=
    Finset.prod_range_succ _ _
  have next (b : Bool) : potential (s+1) (push b h)=p*weight (h s) b := by
    unfold potential
    rw [Finset.prod_range_succ']
    change (∏ i ∈ Finset.range s, weight (h ((i+1)+s)) (h i)) * weight (h (0+s)) b = _
    simp only [Nat.zero_add]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [show i+1+s=i+(s+1) by omega]
  rw [old,next,next]
  have legal : allowZero (s+1) t h =
      (h (t+(s+1)-1) || h (s+(s+1)) || !(h s)) := by
    simp [allowZero,show s+1+(s+1)-1=s+(s+1) by omega]
  rw [legal]
  cases h (t+(s+1)-1) <;> cases h (s+(s+1)) <;> cases h s <;> simp [weight] <;> omega

private lemma weighted_count (s t n : ℕ) (hs : 0<s) (h : History) :
    7^n * potential s h ≤ 4^n * 21^s * continuations s t n h := by
  induction n generalizing h with
  | zero => simpa [continuations] using potential_le s h
  | succ n ih =>
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
    have step := Nat.mul_le_mul_left (7^n) (weighted_step s t h)
    have a := Nat.mul_le_mul_left 4 (ih (push true h))
    have b := Nat.mul_le_mul_left 4 (ih (push false h))
    simp only [continuations,pow_succ 4 n,pow_succ 7 n]
    by_cases z : allowZero (s+1) t h=true
    · simp only [z,if_true] at step ⊢
      nlinarith only [step,a,b]
    · simp only [if_neg z,Nat.add_zero] at step ⊢
      nlinarith only [step,a]

private lemma uniform_lower (s t n : ℕ) (hs : 0<s) : (7/4:ℝ)^n≤count s t n := by
  have raw := weighted_count s t n hs fresh
  rw [potential_fresh] at raw
  have natI : 7^n ≤ 4^n * count s t n := by
    apply Nat.le_of_mul_le_mul_right (c:=21^s) _ (by positivity)
    calc
      _ ≤ _ := raw
      _ = _ := by unfold count; ring
  rw [div_pow,div_le_iff₀ (by positivity)]
  exact_mod_cast (by simpa [Nat.mul_comm] using natI : 7^n≤count s t n*4^n)

private lemma power_upper (s t n m : ℕ) : count s t (m*n) ≤ (count s t n)^m := by
  induction m with
  | zero => simp [count,continuations]
  | succ m ih =>
    rw [Nat.succ_mul,pow_succ]
    exact (upper_split s t (m*n) n fresh).trans (Nat.mul_le_mul_right _ ih)

private lemma power_lower (s t n m : ℕ) : (count s t n)^m ≤ count s t (m*(n+(max t s+s))) := by
  induction m with
  | zero => simp [count,continuations]
  | succ m ih =>
    rw [Nat.succ_mul,pow_succ]
    apply (Nat.mul_le_mul_right _ ih).trans
    calc
      _ ≤ count s t (m*(n+(max t s+s))+(max t s+s+n)) := lower_split s t _ _ fresh
      _ = _ := by congr 1; omega

private lemma general_bounds (s t : ℕ) (hs : 0<s) (ht : 0<t) :
    ∃ c : ℝ, 7/4≤c ∧ c<2 ∧ ∀ n : ℕ,
      c^n≤(count s t n : ℝ) ∧ (count s t n : ℝ)≤c^(n+max t s+s) := by
  let C : ℕ → ℝ := fun n => count s t n
  let L := max t s+s
  have cp (n : ℕ) : 0<C n := by
    change 0<(continuations s t n fresh : ℝ)
    exact_mod_cast (show 0<continuations s t n fresh from at_least s t n fresh)
  let vals : Set ℝ := (fun m : ℕ => Real.log (C m)/m) '' Ici 1
  let a := sInf vals
  have ne : vals.Nonempty := ⟨_,⟨(1:ℕ),show (1:ℕ)≤1 by decide,rfl⟩⟩
  have low (m : ℕ) (hm : 1≤m) : Real.log (7/4)≤Real.log (C m)/m := by
    have h := Real.log_le_log (by positivity : 0<(7/4:ℝ)^m) (uniform_lower s t m hs)
    rw [Real.log_pow] at h
    exact (le_div_iff₀ (by exact_mod_cast (by omega : 0<m))).mpr (by linarith)
  have islow : Real.log (7/4) ∈ lowerBounds vals := by
    rintro _ ⟨m,hm,rfl⟩; exact low m hm
  have upper (m : ℕ) (hp : 1≤m) : a≤Real.log (C m)/m :=
    csInf_le ⟨_,islow⟩ ⟨m,hp,rfl⟩
  have a1 : Real.log (7/4)≤a := le_csInf ne islow
  have a2 : a<Real.log 2 := by
    let m := max t s+s+1
    have hm : 0<m := by dsimp [m]; omega
    have h : C m < (2:ℝ)^m := by dsimp only [C,m]; exact_mod_cast strict_count s t hs ht
    have lg := Real.log_lt_log (cp m) h
    rw [Real.log_pow] at lg
    exact (upper m hm).trans_lt ((div_lt_iff₀ (by exact_mod_cast hm)).mpr (by linarith))
  refine ⟨Real.exp a, ?_, ?_, fun n => ⟨?_,?_⟩⟩
  · simpa only [Real.exp_log (by norm_num : (0:ℝ)<7/4)] using Real.exp_le_exp.mpr a1
  · simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_lt_exp.mpr a2
  · change Real.exp a ^ n ≤ C n
    by_cases hn : n=0
    · subst n; simp [C,count,continuations]
    have h := (le_div_iff₀ (by exact_mod_cast (by omega : 0<n))).mp (upper n (by omega))
    rw [← Real.exp_nat_mul, ← Real.exp_log (cp n)]
    exact Real.exp_le_exp.mpr (by linarith)
  · change C n ≤ Real.exp a ^ (n+max t s+s)
    have nh : 0<n+L := by dsimp [L]; omega
    have minL : Real.log (C n)/(n+L:ℕ) ≤ a := by
      apply le_csInf ne
      rintro _ ⟨m,hm,rfl⟩
      have hm' : 0<m := hm
      have cross : (C n)^m ≤ (C m)^(n+L) := by
        have raw := power_lower s t n m
        rw [Nat.mul_comm] at raw
        dsimp only [C]; exact_mod_cast raw.trans (power_upper s t m (n+L))
      have lg := Real.log_le_log (pow_pos (cp n) _) cross
      rw [Real.log_pow,Real.log_pow] at lg
      apply (div_le_div_iff₀ (by exact_mod_cast nh) (by exact_mod_cast hm')).mpr
      linarith
    have h := (div_le_iff₀ (by exact_mod_cast nh)).mp minL
    rw [← Real.exp_nat_mul, ← Real.exp_log (cp n)]
    apply Real.exp_le_exp.mpr
    simpa [L,Nat.add_assoc,mul_comm] using h

/-! The five remembered bits have 32 possible states. The positive
eigenvector below has nine distinct entries, written in powers of r−1. -/
private def stateClass : Bool → Bool → Bool → Bool → Bool → ℕ
  | false, false, false, false, false => 0
  | true, false, false, false, false => 1
  | false, true, false, false, false => 2
  | true, true, false, false, false => 3
  | false, false, true, false, false => 4
  | true, false, true, false, false => 5
  | false, true, true, false, false => 2
  | true, true, true, false, false => 2
  | false, false, false, true, false => 0
  | true, false, false, true, false => 6
  | false, true, false, true, false => 7
  | true, true, false, true, false => 5
  | false, false, true, true, false => 4
  | true, false, true, true, false => 5
  | false, true, true, true, false => 7
  | true, true, true, true, false => 5
  | false, false, false, false, true => 0
  | true, false, false, false, true => 1
  | false, true, false, false, true => 7
  | true, true, false, false, true => 8
  | false, false, true, false, true => 4
  | true, false, true, false, true => 5
  | false, true, true, false, true => 7
  | true, true, true, false, true => 5
  | false, false, false, true, true => 0
  | true, false, false, true, true => 6
  | false, true, false, true, true => 7
  | true, true, false, true, true => 5
  | false, false, true, true, true => 4
  | true, false, true, true, true => 5
  | false, true, true, true, true => 7
  | true, true, true, true, true => 5

private def stateWeight (u : ℝ) : ℕ → ℝ
  | 0 => 3 + 8*u + 18*u^2 + 45*u^3 + 47*u^4 + 22*u^5 + 4*u^6
  | 1 => 8 + 19*u + 24*u^2 + 30*u^3 + 25*u^4 + 11*u^5 + 2*u^6
  | 2 => 7 + 22*u + 34*u^2 + 40*u^3 + 30*u^4 + 12*u^5 + 2*u^6
  | 3 => 5 + 13*u + 17*u^2 + 20*u^3 + 15*u^4 + 6*u^5 + 1*u^6
  | 4 => 5 + 14*u + 32*u^2 + 61*u^3 + 56*u^4 + 24*u^5 + 4*u^6
  | 5 => 11 + 37*u + 64*u^2 + 80*u^3 + 60*u^4 + 24*u^5 + 4*u^6
  | 6 => 10 + 27*u + 44*u^2 + 60*u^3 + 50*u^4 + 22*u^5 + 4*u^6
  | 7 => 8 + 27*u + 53*u^2 + 76*u^3 + 60*u^4 + 24*u^5 + 4*u^6
  | 8 => 10 + 26*u + 34*u^2 + 40*u^3 + 30*u^4 + 12*u^5 + 2*u^6
  | _ => 1

private def W (r : ℝ) (h : History) : ℝ :=
  stateWeight (r-1) (stateClass (h 0) (h 1) (h 2) (h 3) (h 4))


private def poly (r : ℝ) := r^7-2*r^6+2*r^3-r^2-3*r+1

private lemma exists_root : ∃ r : ℝ, 1884337/1000000<r ∧ r<1884338/1000000 ∧ poly r=0 := by
  let a : ℝ := 1884337/1000000
  let b : ℝ := 1884338/1000000
  have fa : poly a<0 := by norm_num [a,poly]
  have fb : 0<poly b := by norm_num [b,poly]
  have cts : Continuous poly := by unfold poly; fun_prop
  obtain ⟨r,hr,er⟩ := intermediate_value_Icc (show a≤b by norm_num [a,b]) cts.continuousOn
    (show (0:ℝ)∈Icc (poly a) (poly b) from ⟨fa.le,fb.le⟩)
  change ∃ r, a<r ∧ r<b ∧ poly r=0
  exact ⟨r, lt_of_le_of_ne hr.1 (fun e => by rw [e,er] at fa; linarith),
    lt_of_le_of_ne hr.2 (fun e => by rw [← e,er] at fb; linarith), er⟩

private def leading : ℕ → ℝ
  | 1 | 2 | 8 => 2
  | 3 => 1
  | _ => 4

private lemma eigen (r : ℝ) (root : poly r=0) (h : History) :
    r*W r h=W r (push true h) + if allowZero 2 3 h then W r (push false h) else 0 := by
  have localEq (a b c d e : Bool) :
      r*stateWeight (r-1) (stateClass a b c d e) -
      (stateWeight (r-1) (stateClass true a b c d) +
        if e || d || !b then stateWeight (r-1) (stateClass false a b c d) else 0) =
      leading (stateClass a b c d e)*poly r := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
      norm_num [stateClass,stateWeight,leading,poly] <;> ring
  have Eq := localEq (h 0) (h 1) (h 2) (h 3) (h 4)
  rw [root,mul_zero,sub_eq_zero] at Eq
  exact Eq

private lemma W_bounded (r : ℝ) (hlo : 1≤r) (hhi : r≤2) (h : History) :
    1≤W r h ∧ W r h≤280 := by
  let u := r-1
  have ulo : 0≤u := by dsimp [u]; linarith
  have uhi : u≤1 := by dsimp [u]; linarith
  have pos (j : ℕ) : 0≤u^j := pow_nonneg ulo j
  have small (j : ℕ) : u^j≤1 := pow_le_one₀ ulo uhi
  have bounds (k : ℕ) (hk : k<9) : 1≤stateWeight u k ∧ stateWeight u k≤280 := by
    interval_cases k <;> simp only [stateWeight] <;> constructor <;>
      linarith only [ulo,uhi,pos 2,pos 3,pos 4,pos 5,pos 6,small 2,small 3,small 4,small 5,small 6]
  have size : ∀ a b c d e : Bool, stateClass a b c d e<9 := by decide
  exact bounds _ (size ..)

private lemma compare_eigen (r : ℝ) (rlo : 1≤r) (rhi : r≤2) (root : poly r=0)
    (n : ℕ) (h : History) :
    (continuations 2 3 n h : ℝ) ≤ r^n * W r h ∧
      r^n * W r h ≤ 280 * (continuations 2 3 n h : ℝ) := by
  induction n generalizing h with
  | zero => simpa [continuations] using W_bounded r rlo rhi h
  | succ n ih =>
    obtain ⟨a,b⟩ := ih (push true h)
    obtain ⟨d,e⟩ := ih (push false h)
    simp only [pow_succ,mul_assoc,eigen r root,continuations]
    by_cases z : allowZero 2 3 h=true
    · simp only [z,if_true,Nat.cast_add,mul_add]
      exact ⟨add_le_add a d,add_le_add b e⟩
    · simpa only [if_neg z,add_zero,Nat.add_zero] using And.intro a b

private lemma compare_rate {a b M : ℝ} (hb : 0<b) (h : ∀ n : ℕ, a^n ≤ M*b^n) : a≤b := by
  by_contra! lt
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt M ((one_lt_div hb).mpr lt)
  rw [div_pow,lt_div_iff₀ (pow_pos hb n)] at hn
  exact (not_lt_of_ge (h n)) hn

theorem OMA.solution : type_of% @OMA.S_mo_472052.main := by
  intro s t hs ht
  obtain ⟨c,clo,chi,growth⟩ := general_bounds s t hs ht
  refine ⟨c,clo,chi,growth,?_⟩
  rintro rfl rfl
  obtain ⟨r,lo,hi,root⟩ := exists_root
  have rlo : 1≤r := by linarith
  have rhi : r≤2 := by linarith
  have ev (n : ℕ) := compare_eigen r rlo rhi root n fresh
  obtain ⟨wl,wh⟩ := W_bounded r rlo rhi fresh
  have cr : c≤r := by
    apply compare_rate (M:=280) (by linarith)
    intro n
    calc
      _ ≤ _ := (growth n).1
      _ ≤ _ := (ev n).1
      _ ≤ _ := by rw [mul_comm (280:ℝ)]; gcongr
  have rc : r≤c := by
    apply compare_rate (M:=280*c^5) (by linarith)
    intro n
    have h := (ev n).2
    change r^n*W r fresh ≤ 280*(count 2 3 n : ℝ) at h
    have g := (growth n).2
    rw [show n+max 3 2+2=n+5 by omega,pow_add] at g
    calc
      r^n ≤ r^n*W r fresh := le_mul_of_one_le_right (pow_nonneg (by linarith) n) wl
      _ ≤ _ := h
      _ ≤ 280*(c^n*c^5) := by gcongr
      _ = _ := by ring
  exact le_antisymm cr rc ▸ ⟨lo,hi,root⟩
