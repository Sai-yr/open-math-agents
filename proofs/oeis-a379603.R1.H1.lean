import OMAReductions.R_oeis_a379603_R1

open OMA.S_oeis_a379603

private def block (x d : ℕ) : ℕ → ℕ
  | 0 => x
  | m+1 => 10*block x d m+d

private lemma block_good {x d : ℕ} (g : good x) (hd : 6≤d) (hd' : d<10) (m : ℕ) :
    good (block x d m) := by
  induction m with
  | zero => exact g
  | succ m ih =>
    intro i hi
    cases i with
    | zero => simpa [block,Nat.mul_add_mod,Nat.mod_eq_of_lt hd'] using hd
    | succ i =>
      have hdiv : (10*block x d m+d)/10 = block x d m := by omega
      have hle : 10^i≤block x d m := by
        simp only [pow_succ,block] at hi; omega
      simpa only [block,pow_succ, Nat.mul_comm (10^i) 10,← Nat.div_div_eq_div_mul,hdiv] using ih i hle

private lemma block_val (x d m : ℕ) :
    (block x d m : ℚ) = x*(10:ℚ)^m + d*((10:ℚ)^m-1)/9 := by
  induction m with
  | zero => simp [block]
  | succ m ih => push_cast [block,pow_succ,ih]; ring

private lemma tenmod (n : ℕ) : 10^n%9=1 := by
  induction n with
  | zero => decide
  | succ n ih => simp [pow_succ,Nat.mul_mod,ih]

private lemma formula (n : ℕ) (T K : ℕ) (hT : T=10^n) (hK : K=evenValue n) (hl : 10≤T) :
    3*K+(5*T+1)=3*T^2 := by
  have m := tenmod n
  rw [← hT] at m
  have h : 100^n=T^2 := by rw [hT,← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  have a : (5*T+1)%3=0 := by omega
  rw [hK,evenValue,h,← hT]
  have : (5*T+1)/3≤T^2 := by
    nlinarith [Nat.div_mul_le_self (5*T+1) 3, Nat.mul_le_mul_right T hl]
  omega

set_option maxRecDepth 4000 in
private lemma witnesses (n : ℕ) (hn : 5≤n) :
    eligible (2*n) (evenValue n) ∧ eligible (2*n+1) (10*evenValue n+6) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2,by omega⟩
  let T := 10^(m+2)
  let K := evenValue (m+2)
  have hT : 100≤T := Nat.pow_le_pow_right (n:=10) (by decide) (show 2≤m+2 by omega)
  have F := formula (m+2) T K rfl rfl (by omega)
  have FQ : (K:ℚ)=(3*((10:ℚ)^(m+2))^2-(5*(10:ℚ)^(m+2)+1))/3 := by
    have q : 3*(K:ℚ)+(5*(10:ℚ)^(m+2)+1)=3*((10:ℚ)^(m+2))^2 := by exact_mod_cast F
    linarith
  let start := block (block 0 9 (m+1)) 6 (m+2)
  let ev := block (block (block (block start 8 1) 7 (m+1)) 8 (m+2)) 9 1
  let od := block (block (block (block (block start 9 2) 7 m) 6 1) 8 (m+2)) 9 1
  have good0 : good 0 := by
    intro i hi
    exact (not_lt_of_ge hi (by positivity)).elim
  have gs : good start := block_good (block_good good0 (by decide) (by decide) _) (by decide) (by decide) _
  have ge : good ev := by
    exact (block_good (block_good (block_good (block_good gs (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
  have go : good (block od 6 1) := by
    exact (block_good (block_good (block_good (block_good (block_good (block_good gs (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
  have ee : ev=K^2 := by
    apply Nat.cast_injective (R:=ℚ)
    push_cast; simp only [ev,start,block_val,FQ,pow_succ,Nat.cast_ofNat,Nat.cast_zero]; ring
  have oe : block od 6 1=(10*K+6)^2 := by
    apply Nat.cast_injective (R:=ℚ)
    push_cast; simp only [od,start,block_val,FQ,pow_succ,Nat.cast_ofNat,Nat.cast_zero]; ring
  have p : 10^(2*(m+2))=T^2 := by dsimp [T]; rw [Nat.mul_comm, Nat.pow_mul]
  have pred : 10*10^(2*(m+2)-1)=T^2 := by
    rw [← p,← Nat.pow_succ']; congr 1
  have low : T^2≤10*K := by
    have h := Nat.mul_le_mul_right T hT
    change 3*K+(5*T+1)=3*T^2 at F
    rw [pow_two] at F ⊢
    omega
  have up : K<T^2 := by omega
  refine ⟨⟨?_,?_,ee ▸ ge⟩,⟨?_,?_,oe ▸ go⟩⟩
  · change 10^(2*(m+2)-1)≤K; omega
  · simpa only [p] using up
  · simpa only [Nat.add_sub_cancel,p] using (show T^2≤10*K+6 by omega)
  · simp only [pow_succ,p]; change 10*K+6<T^2*10; omega

private lemma suffix_floor {x : ℕ} (g : good x) (k : ℕ) (hx : 10^k≤x) :
    2*(10^k-1) ≤ 3*(x%10^k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have pk : 0<10^k := by positivity
    rw [pow_succ] at hx ⊢
    have a := ih (by omega)
    have b := Nat.mul_le_mul_left (10^k) (g k (by omega))
    rw [Nat.mod_mul]
    omega

private lemma high_good {x : ℕ} (g : good x) (k : ℕ) : good (x/10^k) := by
  intro i hi
  have h := (Nat.le_div_iff_mul_le (by positivity : 0<10^k)).mp hi
  simpa only [Nat.div_div_eq_div_mul, ← pow_add] using
    g (k+i) (by rw [pow_add,mul_comm]; exact h)

private lemma residue {x M r a : ℤ} (hx : x=a*M+r) (lo : 0≤r) (hi : r<M) :
    x%M=r := by rw [hx,Int.mul_add_emod_self_right,Int.emod_eq_of_lt lo hi]

private lemma int_floor {x : ℕ} (g : good x) (k : ℕ) (hx : 10^k≤x) :
    2*((10:ℤ)^k-1)≤3*((x:ℤ)%10^k) := by
  have h := suffix_floor g k hx
  have hp : 1≤(10:ℕ)^k := Nat.one_le_pow _ _ (by decide)
  zify [hp] at h
  exact h

/-- The bottom 2n digits force the square of the deficit into one of three
unit intervals. The two lower intervals put a small digit in the top block. -/
private lemma quotient_two {T d q Y A : ℤ} (ht : 100≤T) (hd : 0≤d) (hq : 0≤q)
    (hdhi : 3*d≤5*T-2) (eq : d^2=q*T^2+Y) (ey : Y<T^2)
    (bot : 2*(T^2-1)≤3*Y) (ea : A=T^2-2*d+q)
    (top : 2*(T-1)≤3*(A%T)) : q=2 ∧ 8*T≤5*d := by
  have Ts : 10000≤T^2 := by nlinarith [mul_self_le_mul_self (by decide : (0:ℤ)≤100) ht]
  have ds := mul_self_le_mul_self (by linarith : 0≤3*d) (show 3*d≤5*T by omega)
  have qhi : q≤2 := by
    by_contra! h
    have := mul_le_mul_of_nonneg_right (show 3≤q by omega) (sq_nonneg T)
    nlinarith
  by_cases h0 : q=0
  · subst q
    have low : 4*T<5*d := by
      by_contra! h
      nlinarith [mul_self_le_mul_self (show 0≤5*d by omega) h]
    have high : d<T := by
      by_contra! h
      nlinarith [mul_self_le_mul_self (show 0≤T by omega) h]
    have rem := residue (x:=A) (M:=T) (a:=T-2) (r:=2*T-2*d) (by linarith [ea]) (by omega) (by omega)
    omega
  by_cases h1 : q=1
  · subst q
    have low : 5*T<4*d := by
      by_contra! h
      nlinarith [mul_self_le_mul_self (show 0≤4*d by omega) h]
    have high : 2*d<3*T := by
      by_contra! h
      nlinarith [mul_self_le_mul_self (show 0≤3*T by omega) h]
    have rem := residue (x:=A) (M:=T) (a:=T-3) (r:=3*T-2*d+1) (by nlinarith [ea]) (by omega) (by omega)
    omega
  have h : q=2 := by omega
  refine ⟨h,?_⟩
  subst q
  by_contra! h'
  nlinarith [mul_self_le_mul_self (show 0≤5*d by omega) h'.le]

private lemma even_exclude (n : ℕ) (hn : 5≤n) (T d q Y A : ℤ) (eT : T=(10:ℤ)^n)
    (hd : 0≤d) (hq : 0≤q) (hdhi : 3*d≤5*T-2)
    (eq : d^2=q*T^2+Y) (ey : Y<T^2) (ea : A=T^2-2*d+q)
    (low : ∀ k≤2*n, 2*((10:ℤ)^k-1) ≤ 3*(Y%10^k))
    (high : ∀ k≤n+1, 2*((10:ℤ)^k-1) ≤ 3*(A%10^k))
    (hy : 0≤Y) : False := by
  have ht : 100≤T := eT ▸ pow_le_pow_right₀ (by decide : (1:ℤ)≤10) (show 2≤n by omega)
  have hH : (10:ℤ)^(2*n)=T^2 := by rw [eT,Nat.mul_comm,pow_mul]
  have bot := low (2*n) le_rfl
  rw [hH,Int.emod_eq_of_lt hy ey] at bot
  have top := high n (by omega)
  rw [← eT] at top
  obtain ⟨rfl,dl⟩ := quotient_two ht hd hq hdhi eq ey bot ea top
  have tm : T%9=1 := by rw [eT]; exact_mod_cast tenmod n
  let E := (10*T-1)/3 - (2*d-3)
  have e : 3*E=10*T+8-6*d := by dsimp [E]; omega
  have epos : 4≤E := by omega
  have et : E<T := by omega
  let j := Nat.log 10 E.toNat
  let P : ℤ := 10^j
  have en : (E.toNat:ℤ)=E := Int.toNat_of_nonneg (by omega)
  have jp : P≤E := by
    rw [← en]; dsimp only [P,j]
    exact_mod_cast Nat.pow_log_le_self 10 (show E.toNat≠0 by omega)
  have jh : E<10*P := by
    rw [← en]; dsimp only [P,j]
    have := Nat.lt_pow_succ_log_self (b:=10) (by decide) E.toNat
    rw [pow_succ,mul_comm] at this
    exact_mod_cast this
  have jn : j<n := by
    apply (Nat.pow_lt_pow_iff_right (a:=10) (by decide)).mp
    have h : (10:ℤ)^j<10^n := by change P<_; omega
    exact_mod_cast h
  let J : ℤ := 10^(n-(j+1))
  have Jmod : J%9=1 := by dsimp only [J]; exact_mod_cast tenmod (n-(j+1))
  have tdec : T=10*P*J := by
    dsimp [P,J]; rw [eT,← pow_succ',← pow_add]; congr 1; omega
  have pp : 0<P := by dsimp [P]; positivity
  have pm : P%9=1 := by dsimp only [P]; exact_mod_cast tenmod j
  have scale : (10:ℤ)^(j+1)=10*P := pow_succ' _ _
  have topP := high (j+1) (by omega)
  rw [scale] at topP
  let B := (2*(10*P-1))/3
  have be : 3*B=2*(10*P-1) := by dsimp [B]; omega
  have ae : A=(T*J-(10*J-1)/3-1)*(10*P)+(B+E) := by
    have j3 : 3*((10*J-1)/3)=10*J-1 := by omega
    -- The top block is based at the word ending in repeated sixes.
    nlinarith only [ea,e,be,tdec,congrArg (fun x:ℤ=>x*T) tdec,
      congrArg (fun x:ℤ=>x*(10*P)) j3]
  have esmall : 3*E<10*P := by
    by_contra! bad
    have r := residue (a:=T*J-(10*J-1)/3) (r:=B+E-10*P) (M:=10*P) (x:=A)
      (by nlinarith [ae]) (by omega) (by omega)
    omega
  have pl : 10≤P := by
    by_cases z : j=0
    · simp [P,z] at esmall; omega
    · exact pow_le_pow_right₀ (by decide : (1:ℤ)≤10) (show 1≤j by omega)
  let G := 5*T-3*d
  have gl : 11*P ≤ 10*G := by dsimp [G]; omega
  have gh : G≤5*P := by dsimp [G]; omega
  have s1 : 19*T≤2*(5*T+3*d) := by omega
  have s2 : 5*T+3*d≤10*T := by omega
  have prodLow := mul_le_mul gl s1 (show 0≤19*T by omega) (show 0≤10*G by omega)
  have prodHigh := mul_le_mul gh s2 (show 0≤5*T+3*d by omega) (show 0≤5*P by omega)
  have pt : 1000≤P*T := by exact mul_le_mul pl ht (by decide) (by omega)
  let K := 7*((J-1)/9)
  have ke : 9*K=7*(J-1) := by dsimp [K]; omega
  have ee : 9*(Y-K*(10*P*T))=70*P*T-G*(5*T+3*d) := by
    dsimp only [G]
    nlinarith only [eq,congrArg (fun x:ℤ=>x*(10*P*T)) ke,congrArg (fun x:ℤ=>x*T) tdec]
  have gain := low (j+1+n) (by omega)
  have pexp : (10:ℤ)^(j+1+n)=10*P*T := by rw [pow_add,scale,← eT]
  rw [pexp] at gain
  have rem := residue (x:=Y) (M:=10*P*T) (a:=K) (r:=Y-K*(10*P*T)) (by ring)
    (by nlinarith only [prodHigh,ee,pt]) (by nlinarith only [prodLow,ee,pt])
  rw [rem] at gain
  nlinarith only [gain,ee,prodLow,pt]

private lemma even_upper (n : ℕ) (hn : 5≤n) (x : ℕ) (hx : eligible (2*n) x) :
    x≤evenValue n := by
  let T := 10^n
  let H := T^2
  let d := H-x
  let q := d^2/H
  let Y := d^2%H
  let A := x^2/H
  have Tbig : 100≤T := Nat.pow_le_pow_right (n:=10) (by decide) (show 2≤n by omega)
  have Hp : 0<H := by dsimp [H]; positivity
  have HH : 10^(2*n)=H := by dsimp [H,T]; rw [Nat.mul_comm,pow_mul]
  have xhi := hx.2.1
  rw [HH] at xhi
  have xd : x+d=H := by dsimp [d]; omega
  have f := formula n T (evenValue n) rfl rfl (by omega)
  by_contra! bigger
  have dh : 3*d≤5*T-2 := by change 3*evenValue n+(5*T+1)=3*H at f; omega
  have de : d^2=H*q+Y := (Nat.mod_add_div _ _).symm.trans (Nat.add_comm _ _)
  have yh : Y<H := Nat.mod_lt _ Hp
  have hth : 100*T≤H := by simpa only [H,pow_two] using Nat.mul_le_mul_right T Tbig
  have tdx : 2*d≤H := by omega
  have ex : x^2=H*(H-2*d+q)+Y := by
    have e := congrArg (fun v:ℕ=>v^2) xd
    have z := Nat.sub_add_cancel tdx
    nlinarith only [e,de,congrArg (fun v:ℕ=>H*v) z,congrArg (fun v:ℕ=>2*d*v) xd]
  have aeq : A=H-2*d+q := by
    change x^2/H=_
    rw [ex,Nat.mul_add_div Hp,Nat.div_eq_of_lt yh,Nat.add_zero]
  have xe : x^2=H*A+Y := by simpa only [aeq] using ex
  have calcBound (u v w z : ℕ) (hh : 100*u≤v) (hd : 3*w≤5*u-2) (hu : 100≤u) :
      10*u≤v-2*w+z := by omega
  have hl : 10*T≤A := by rw [aeq]; exact calcBound T H d q hth dh Tbig
  have AGood : good A := by dsimp only [A]; rw [← HH]; exact high_good hx.2.2 (2*n)
  have lowN (k : ℕ) (hk : k≤2*n) :
      2*((10:ℤ)^k-1)≤3*((Y:ℤ)%10^k) := by
    have psize : 10^k≤H := HH ▸ Nat.pow_le_pow_right (by decide) hk
    have xlarge : H≤x^2 := by
      have h := Nat.mul_le_mul_left H (show 1≤A by omega)
      omega
    have b := int_floor hx.2.2 k (psize.trans xlarge)
    have dv : 10^k ∣ H := HH ▸ Nat.pow_dvd_pow 10 hk
    have r : x^2%10^k=Y%10^k := by
      rw [xe,Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left dv A),Nat.zero_add,Nat.mod_mod]
    have ri := congrArg (fun u:ℕ=>(u:ℤ)) r
    push_cast at ri
    push_cast at b
    rwa [ri] at b
  have highN (k : ℕ) (hk : k≤n+1) :
      2*((10:ℤ)^k-1)≤3*((A:ℤ)%10^k) := by
    have h := Nat.pow_le_pow_right (n:=10) (by decide) hk
    rw [pow_succ'] at h
    exact int_floor AGood k (h.trans hl)
  apply even_exclude n hn T d q Y A (by dsimp [T]) (by positivity) (by positivity)
  · omega
  · change d^2=T^2*q+Y at de
    exact_mod_cast (by simpa [Nat.mul_comm] using de : d^2=q*T^2+Y)
  · exact_mod_cast yh
  · have h : A+2*d=H+q := by omega
    have h' : (A:ℤ)+2*d=(T:ℤ)^2+q := by exact_mod_cast h
    linarith
  · exact lowN
  · exact highN
  · positivity

theorem OMA.solution : OMA.R_oeis_a379603_R1.H1 := by
  intro n hn
  obtain ⟨ev,od⟩ := witnesses n hn
  exact ⟨⟨ev,even_upper n hn⟩,od⟩
