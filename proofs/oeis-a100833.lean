import OMAStatements.S_oeis_a100833

/-!
# The greedy word avoiding palindromes and squares

Two of each three positions contain 1 and 2. At every third position
the formula adds 3 to the exponent of 2 in its block number. A repeated
block would have a period 3r, but one block number divisible by the full
power of 2 in r necessarily changes its valuation after that shift.
Conversely, replacing a third-position entry by 3+s below its prescribed
value produces an explicit repeated suffix of half-length 3·2^s.
-/

namespace A100833Proof
open OMA.S_oeis_a100833

private abbrev v (x : ℕ) := x.factorization 2

private theorem dvd_v {x : ℕ} (hx : 0 < x) (s : ℕ) : 2^s∣x ↔ s ≤ v x :=
  Nat.prime_two.pow_dvd_iff_le_factorization hx.ne'

private theorem exact_v {x s : ℕ} (hx : 0 < x) : v x = s ↔ 2^s∣x ∧ ¬2^(s+1)∣x := by
  rw [dvd_v hx,dvd_v hx]; omega

private theorem plus_power {x : ℕ} (hx : 0 < x) : 2^(v x+1)∣x+2^(v x) := by
  let D:=2^(v x)
  have hD : 0<D := by dsimp [D]; positivity
  have hd : D∣x := (dvd_v hx _).mpr le_rfl
  obtain ⟨b,hb⟩:=hd
  have hnot := ((exact_v hx).mp rfl).2
  rw [pow_succ] at hnot ⊢
  change ¬ D*2∣x at hnot
  change D*2∣x+D
  rw [hb,Nat.mul_dvd_mul_iff_left hD] at hnot
  rw [hb,←Nat.mul_add_one,Nat.mul_dvd_mul_iff_left hD]
  omega

private theorem different {x r : ℕ} (hx : 0<x) (hr : 0<r) (hD : 2^(v r)∣x) :
    v x ≠ v (x+r) := by
  intro eq
  have h1 := plus_power hx
  have h2 := plus_power (show 0<x+r by omega)
  rw [←eq] at h2
  have d := (Nat.dvd_add_right h1).mp (show 2^(v x+1)∣(x+2^(v x))+r by
    simpa only [Nat.add_right_comm x r (2^(v x))] using h2)
  have lo := (dvd_v hx _).mp hD
  have hi := (dvd_v hr _).mp d
  omega

private theorem shift_low {x s : ℕ} (hx : 0<x) (hn : ¬2^s∣x) :
    v (x+2^s)=v x := by
  have hlt : v x < s := by rw [dvd_v hx] at hn; omega
  have dlo : 2^(v x)∣2^s := pow_dvd_pow _ hlt.le
  have dhi : 2^(v x+1)∣2^s := pow_dvd_pow _ hlt
  have hv := (exact_v hx).mp rfl
  apply (exact_v (show 0<x+2^s by omega)).mpr
  exact ⟨dvd_add hv.1 dlo,fun h=>hv.2 ((Nat.dvd_add_left dhi).mp h)⟩

private theorem before_multiple {q s : ℕ} (hq : 0<q) (hd : 2^(s+1)∣q) :
    v (q-2^s)=s := by
  let D:=2^s
  have Dpos : 0<D := by dsimp [D]; positivity
  rw [pow_succ] at hd
  change D*2∣q at hd
  have le := Nat.le_of_dvd hq hd
  have lo : D∣q := (dvd_mul_right D 2).trans hd
  apply (exact_v (show 0<q-D by omega)).mpr
  refine ⟨Nat.dvd_sub lo dvd_rfl,?_⟩
  rw [pow_succ]
  intro h
  have hz := Nat.dvd_sub hd h
  change D*2∣q-(q-D) at hz
  rw [show q-(q-D)=D by omega] at hz
  have big := Nat.le_of_dvd Dpos hz
  omega

private theorem miss_between {q x D : ℕ} (_hD : 0<D) (hd : D*2∣q)
    (lo : q < x+2*D) (hi : x+D < q) : ¬D∣x := by
  intro hx
  have hq := (dvd_mul_right D 2).trans hd
  have hd' := Nat.dvd_sub hq (dvd_add hx (dvd_refl D))
  have hpos : 0<q-(x+D) := by omega
  have := Nat.le_of_dvd hpos hd'
  omega

private theorem next_multiple (i m : ℕ) (hi : 0 < i) (hm : 0< m) :
    ∃ b : ℕ, i ≤ m*(b+1) ∧ m*(b+1)< i+m := by
  refine ⟨(i-1)/m,?_⟩
  have h := Nat.div_add_mod (i-1) m
  have hlt := Nat.mod_lt (i-1) hm
  rw [Nat.mul_add,Nat.mul_one]; omega

end A100833Proof

namespace A100833Proof
open OMA.S_oeis_a100833

private theorem at_one {i : ℕ} (h : i%3=1) : formula i=1 := by simp [formula,h]
private theorem at_two {i : ℕ} (h : i%3=2) : formula i=2 := by simp [formula,h]
private theorem at_three (q : ℕ) : formula (3*q)=3+v q := by simp [formula]

private theorem residues {i j : ℕ} (eq : formula i=formula j) : i%3=j%3 := by
  unfold formula at eq
  split_ifs at eq <;> omega

private theorem nonzero_match {i j : ℕ} (e : i%3=j%3) (h : i%3≠0) : formula i=formula j := by
  have h1 : i%3=1 ∨ i%3=2 := by omega
  rcases h1 with h|h
  · rw [at_one h,at_one (e ▸ h)]
  · rw [at_two h,at_two (e ▸ h)]

private theorem free (N : ℕ) : admissible formula N := by
  constructor
  · intro i L _ hL _ hp
    let j:=(L-2)/2
    have h1 := residues (hp j (by dsimp [j]; omega))
    dsimp [j] at h1
    omega
  · intro i h hi hpos _ hs
    have h0 := residues (hs 0 hpos)
    simp only [Nat.add_zero] at h0
    have h3 : 3∣h := by omega
    obtain ⟨r,rfl⟩:=h3
    have rpos : 0<r := by omega
    let D:=2^(v r)
    have Dpos : 0<D := by dsimp [D]; positivity
    have hd : D∣r := (dvd_v rpos _).mpr le_rfl
    have le := Nat.le_of_dvd rpos hd
    obtain ⟨b,hb1,hb2⟩:=next_multiple i (3*D) hi (by omega)
    let q := D*(b+1)
    have hl : i≤3*q := by dsimp [q]; rwa [←Nat.mul_assoc]
    have hu : 3*q < i+3*r := by dsimp [q]; rw [←Nat.mul_assoc]; omega
    have he := hs (3*q-i) (by omega)
    rw [show i+(3*q-i)=3*q by omega,show i+3*r+(3*q-i)=3*(q+r) by omega,
      at_three,at_three] at he
    exact different (x:=q) (r:=r) (by dsimp [q]; positivity) rpos (dvd_mul_right _ _) (by omega)

end A100833Proof

namespace A100833Proof
open OMA.S_oeis_a100833

private theorem adjacent {f : ℕ → ℕ} {N i : ℕ} (hg : admissible f N) (hi : 0 < i) (hl : i+1≤N) :
    f i ≠ f (i+1) := by
  intro e
  apply hg.1 i 2 hi (by decide) (by omega)
  intro j hj
  interval_cases j <;> simp [e]

private theorem one_between {f : ℕ → ℕ} {N i : ℕ} (hg : admissible f N) (hi : 0 < i) (hl : i+2≤N) :
    f i ≠ f (i+2) := by
  intro e
  apply hg.1 i 3 hi (by decide) (by omega)
  intro j hj
  interval_cases j <;> simp [e]

private theorem replaced_square {q r : ℕ} (hq : 0<q) (hr : r<v q) :
    ¬admissible (Function.update formula (3*q) (3+r)) (3*q) := by
  let D:=2^r
  have Dpos : 0<D := by dsimp [D]; positivity
  have hd : 2^(r+1)∣q := (dvd_v hq _).mpr hr
  have hm : D*2∣q := by simpa only [pow_succ,D] using hd
  have le := Nat.le_of_dvd hq hm
  let i:=3*q-6*D+1
  have hi : 0 < i := by dsimp [i]; omega
  have hn : i+6*D=3*q+1 := by dsimp [i]; omega
  intro hg
  apply hg.2 i (3*D) hi (by omega) (by omega)
  intro j hj
  let x:=i+j
  have xpos : 0<x := by dsimp [x]; omega
  have lim : x+3*D ≤ 3*q := by dsimp [x]; omega
  have early : 3*q < x+6*D := by dsimp [x]; omega
  change Function.update formula (3*q) (3+r) x =
    Function.update formula (3*q) (3+r) (i+3*D+j)
  rw [show i+3*D+j=x+3*D by dsimp [x]; omega,Function.update_of_ne (by omega : x≠3*q)]
  by_cases he : x+3*D=3*q
  · rw [he,Function.update_self,show x=3*(q-D) by omega,at_three,before_multiple hq hd]
  · rw [Function.update_of_ne he]
    by_cases h0 : x%3=0
    · have hx : x=3*(x/3) := by omega
      have low := miss_between Dpos hm (x:=x/3) (by omega) (by omega)
      have hs := shift_low (x:=x/3) (s:=r) (by omega) low
      calc
        formula x = 3+v (x/3) := by rw [hx] at ⊢; simp [formula]
        _ = 3+v (x/3+D) := by rw [hs]
        _ = formula (x+3*D) := by rw [show x+3*D=3*(x/3+D) by omega,at_three]
    · exact nonzero_match (by omega) h0

private theorem smallest (n c : ℕ) (hn : 0<n) (hc : 0<c) (hl : c<formula n) :
    ¬admissible (Function.update formula n c) n := by
  by_cases h1 : n%3=1
  · rw [at_one h1] at hl; omega
  by_cases h2 : n%3=2
  · rw [at_two h2] at hl
    have ce : c=1 := by omega
    intro hg
    have hx := adjacent (i:=n-1) hg (by omega) (by omega)
    rw [show n-1+1=n by omega,Function.update_self,Function.update_of_ne (by omega : n-1≠n),
      at_one (by omega : (n-1)%3=1),ce] at hx
    exact hx rfl
  have h0 : n=3*(n/3) := by omega
  have qpos : 0<n/3 := by omega
  have fn : formula n=3+v (n/3) := by rw [h0] at ⊢; simp [formula]
  rw [fn] at hl
  by_cases c1 : c=1
  · intro hg
    have hx := one_between (i:=n-2) hg (by omega) (by omega)
    rw [show n-2+2=n by omega,Function.update_self,Function.update_of_ne (by omega : n-2≠n),
      at_one (by omega : (n-2)%3=1),c1] at hx
    exact hx rfl
  by_cases c2 : c=2
  · intro hg
    have hx := adjacent (i:=n-1) hg (by omega) (by omega)
    rw [show n-1+1=n by omega,Function.update_self,Function.update_of_ne (by omega : n-1≠n),
      at_two (by omega : (n-1)%3=2),c2] at hx
    exact hx rfl
  have hh := replaced_square (q:=n/3) (r:=c-3) qpos (by omega)
  rwa [←h0,show 3+(c-3)=c by omega] at hh

end A100833Proof

namespace A100833Proof
open OMA.S_oeis_a100833

private theorem transfer {f g : ℕ → ℕ} {N : ℕ} (same : ∀ i, 0 < i → i≤N → f i=g i)
    (h : admissible f N) : admissible g N := by
  constructor
  · intro i L hi hL hN hp
    apply h.1 i L hi hL hN
    intro j hj
    rw [same (i+j) (by omega) (by omega),same (i+(L-1-j)) (by omega) (by omega)]
    exact hp j hj
  · intro i t hi ht hN hs
    apply h.2 i t hi ht hN
    intro j hj
    rw [same (i+j) (by omega) (by omega),same (i+t+j) (by omega) (by omega)]
    exact hs j hj

private theorem no_less {f g : ℕ → ℕ} (hf : greedy f) (hg : greedy g) {n : ℕ} (hn : 0<n)
    (agree : ∀ i, 0 < i → i<n → f i=g i) : ¬f n<g n := by
  intro lt
  have hx := (hg n hn).2.2 (f n) (hf n hn).1 lt
  apply hx
  apply transfer (f:=f) _ (hf n hn).2.1
  intro i hi hN
  by_cases e : i=n
  · subst i; rw [Function.update_self]
  · rw [Function.update_of_ne e,agree i hi (by omega)]

private theorem solved : greedy formula ∧ ∀ a : ℕ → ℕ, greedy a →
    ∀ n : ℕ, 0 < n → a n = formula n := by
  have h : greedy formula := by
    intro n hn
    refine ⟨?_,free n,fun c hc hl=>smallest n c hn hc hl⟩
    unfold formula; split_ifs <;> omega
  refine ⟨h,?_⟩
  intro a ha n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have ag : ∀ i, 0 < i → i<n → a i=formula i := fun i hi lt=>ih i lt hi
    have h1 := no_less ha h hn ag
    have h2 := no_less h ha hn (fun i hi lt=>(ag i hi lt).symm)
    omega

end A100833Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a100833.main :=
  A100833Proof.solved
