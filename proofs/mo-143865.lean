import OMAStatements.S_mo_143865

namespace MinRec
open OMA.S_mo_143865 Finset
noncomputable section

def cd (a : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => a*cd a n+2

def bd (a : ℝ) (n : ℕ) : ℝ :=
  if h : n=0 then 0 else a*bd a (n/2)+2*((((n+1)/2:ℕ):ℝ))
termination_by n
decreasing_by omega

def pref (d : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, d j
def comb (a : ℝ) := pref (cd a)
def bal (a : ℝ) := pref (bd a)

theorem pref_succ (d : ℕ → ℝ) (n : ℕ) : pref d (n+1)=pref d n+d n := sum_range_succ ..

theorem bd_even (a : ℝ) (k : ℕ) : bd a (2*k)=a*bd a k+2*(k:ℝ) := by
  cases k with
  | zero => simp [bd]
  | succ k =>
    rw [bd]; simp [show (2*(k+1)+1)/2=k+1 by omega]

theorem bd_odd (a : ℝ) (k : ℕ) : bd a (2*k+1)=a*bd a k+2*((k:ℝ)+1) := by
  rw [bd]; simp [show (2*k+1)/2=k by omega,show (2*k+1+1)/2=k+1 by omega]

theorem bd0 (a : ℝ) : bd a 0=0 := by rw [bd]; simp
theorem bal1 (a : ℝ) : bal a 1=0 := by simp [bal,pref,bd0]
theorem comb1 (a : ℝ) : comb a 1=0 := by simp [comb,pref,cd]

theorem bal_even (a : ℝ) (k : ℕ) : bal a (2*k)=2*a*bal a k+2*(k:ℝ)^2 := by
  induction k with
  | zero => simp [bal,pref]
  | succ k ih =>
    rw [show 2*(k+1)=(2*k+1)+1 by omega]
    change pref (bd a) ((2*k+1)+1)=_
    rw [pref_succ,pref_succ,bd_even,bd_odd]
    change bal a (2*k)+_+_=_
    rw [ih]; change _=2*a*pref (bd a) (k+1)+_
    rw [pref_succ]; push_cast; unfold bal; ring

theorem bal_odd (a : ℝ) (k : ℕ) : bal a (2*k+1)=cost a (bal a) k (k+1) := by
  change pref (bd a) (2*k+1)=_
  rw [pref_succ,bd_even]; change bal a (2*k)+_=_
  rw [bal_even]; unfold cost bal; rw [pref_succ]; push_cast; ring

theorem comb_rec (a : ℝ) {n : ℕ} (hn : 0 < n) : comb a (n+1)=a*comb a n+2*(n:ℝ) := by
  cases n with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simp [comb,pref,cd,sum_range_succ]
    | succ k ih =>
      have prev := ih (by omega)
      change pref (cd a) ((k+1+1)+1)=_
      rw [pref_succ]; change comb a (k+1+1)+cd a (k+1+1)=_
      rw [cd]; nth_rw 1 [prev]
      change _=a*pref (cd a) (k+1+1)+_
      rw [pref_succ]; push_cast; unfold comb; ring

theorem cd_second (a : ℝ) (k : ℕ) : cd a (k+1)-cd a k=2*a^k := by
  induction k with
  | zero => simp [cd]
  | succ k ih =>
    rw [cd]; change a*cd a (k+1)+2-cd a (k+1)=_
    have id : cd a (k+1)=a*cd a k+2 := rfl
    rw [pow_succ]; nlinarith only [id,congrArg (fun v : ℝ => a*v) ih]

theorem bd_second {a : ℝ} (ha : 1 ≤ a) (k : ℕ) : 2 ≤ bd a (k+1)-bd a k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases even : k%2=0
    · set j := k/2
      have id : k=2*j := by dsimp [j]; omega
      rw [id,bd_even,bd_odd]; ring_nf; rfl
    · set j := k/2
      have id : k=2*j+1 := by dsimp [j]; omega
      have sub := ih j (by omega)
      rw [id,show 2*j+1+1=2*(j+1) by omega,bd_even,bd_odd]
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_left sub (by linarith : 0 ≤ a),ha]

theorem bd_nonneg {a : ℝ} (ha : 1 ≤ a) (k : ℕ) : 0 ≤ bd a k := by
  induction k with
  | zero => rw [bd0]
  | succ k ih => linarith [bd_second ha k]

theorem bal_mono {a : ℝ} (ha : 1 ≤ a) : Monotone (bal a) := by
  apply monotone_nat_of_le_succ; intro k; unfold bal; rw [pref_succ]
  exact le_add_of_nonneg_right (bd_nonneg ha k)

theorem cost_symm (a : ℝ) (x : ℕ → ℝ) (i j : ℕ) : cost a x i j=cost a x j i := by
  unfold cost; ring

theorem exchange (a : ℝ) (d : ℕ → ℝ) (i j : ℕ) :
    cost a (pref d) i (j+1)-cost a (pref d) (i+1) j =
      a*(d j-d i)-2*((j:ℝ)-i) := by unfold cost; rw [pref_succ,pref_succ]; push_cast; ring

theorem balanced_exchange {a : ℝ} (ha : 1 < a) {i j : ℕ} (ij : i < j) :
    cost a (bal a) (i+1) j < cost a (bal a) i (j+1) := by
  have mono : Monotone (fun k : ℕ => bd a k-2*(k:ℝ)) := monotone_nat_of_le_succ (by
    intro k; push_cast; linarith [bd_second ha.le k])
  have inc : 2*((j:ℝ)-i) ≤ bd a j-bd a i := by have h := mono ij.le; dsimp at h; linarith
  have pos : (0:ℝ) < (j:ℝ)-i := sub_pos.mpr (by exact_mod_cast ij)
  have e := exchange a (bd a) i j
  change cost a (bal a) i (j+1)-cost a (bal a) (i+1) j=_ at e
  nlinarith only [e,mul_le_mul_of_nonneg_left inc (by linarith : 0 ≤ a),mul_pos (sub_pos.mpr ha) pos]

theorem comb_exchange {a : ℝ} (ap : 0 < a) (ha : a < 1) {i j : ℕ} (ij : i < j) :
    cost a (comb a) i (j+1) < cost a (comb a) (i+1) j := by
  have mono : Monotone (fun k : ℕ => 2*(k:ℝ)-cd a k) := monotone_nat_of_le_succ (by
    intro k; push_cast; linarith [cd_second a k,pow_le_one₀ ap.le ha.le (n:=k)])
  have inc : cd a j-cd a i ≤ 2*((j:ℝ)-i) := by have h := mono ij.le; dsimp at h; linarith
  have pos : (0:ℝ) < (j:ℝ)-i := sub_pos.mpr (by exact_mod_cast ij)
  have e := exchange a (cd a) i j
  change cost a (comb a) i (j+1)-cost a (comb a) (i+1) j=_ at e
  nlinarith only [e,mul_le_mul_of_nonneg_left inc ap.le,mul_pos (sub_pos.mpr ha) pos]

end
end MinRec

namespace MinRec
open OMA.S_mo_143865
noncomputable section

private theorem bal_pair {a : ℝ} (ha : 1 < a) (d : ℕ) : ∀ i : ℕ,
    bal a (i+(i+d)) ≤ cost a (bal a) i (i+d) ∧
    (bal a (i+(i+d))=cost a (bal a) i (i+d) ↔ d ≤ 1) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro i
    rcases d with _|d
    · have eq : bal a (i+i)=cost a (bal a) i i := by
        rw [show i+i=2*i by omega,bal_even]; unfold cost; ring
      simpa using (show bal a (i+i) ≤ cost a (bal a) i i ∧
        (bal a (i+i)=cost a (bal a) i i ↔ 0≤1) from ⟨eq.le,iff_of_true eq (by decide)⟩)
    rcases d with _|d
    · have eq : bal a (i+(i+1))=cost a (bal a) i (i+1) := by rw [show i+(i+1)=2*i+1 by omega,bal_odd]
      exact ⟨eq.le,iff_of_true eq (by decide)⟩
    · have prev := (ih d (by omega) (i+1)).1
      have ex := balanced_exchange (a:=a) (i:=i) (j:=i+1+d) ha (by omega)
      have strict : bal a (i+(i+(d+1+1))) < cost a (bal a) i (i+(d+1+1)) := by
        calc _ = bal a (i+1+(i+1+d)) := by congr 1; omega
             _ ≤ _ := prev
             _ < cost a (bal a) i (i+1+d+1) := ex
             _ = _ := by rw [show i+1+d+1=i+(d+1+1) by omega]
      exact ⟨strict.le,iff_of_false (ne_of_lt strict) (by omega)⟩

private theorem comb_pair {a : ℝ} (ap : 0 < a) (ha : a < 1) (k : ℕ) : ∀ j : ℕ, k+1 ≤ j →
    comb a (k+1+j) ≤ cost a (comb a) (k+1) j ∧
    (comb a (k+1+j)=cost a (comb a) (k+1) j ↔ k=0) := by
  induction k with
  | zero =>
    intro j hj
    have eq : comb a (1+j)=cost a (comb a) 1 j := by rw [Nat.add_comm,comb_rec _ hj]; simp [cost,comb1]
    exact ⟨eq.le,iff_of_true eq rfl⟩
  | succ k ih =>
    intro j hj
    have prev := (ih (j+1) (by omega)).1
    have ex := comb_exchange (a:=a) (i:=k+1) (j:=j) ap ha (by omega)
    have strict : comb a (k+1+1+j) < cost a (comb a) (k+1+1) j := by
      rw [show k+1+1+j=k+1+(j+1) by omega]
      exact prev.trans_lt ex
    exact ⟨strict.le,iff_of_false (ne_of_lt strict) (by omega)⟩

def quad (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)-1)
def model (a : ℝ) := if a<1 then comb a else if a=1 then quad else bal a

def chosen (a : ℝ) (i j : ℕ) : Prop :=
  (a < 1 ∧ (i=1 ∨ j=1)) ∨ a=1 ∨ (1 < a ∧ i ≤ j+1 ∧ j ≤ i+1)

private theorem left_pair {a : ℝ} (ap : 0 < a) {i j : ℕ} (ip : 0 < i) (ij : i ≤ j) :
    model a (i+j) ≤ cost a (model a) i j ∧
      (model a (i+j)=cost a (model a) i j ↔ chosen a i j) := by
  rcases lt_trichotomy a 1 with small|eq|big
  · have id : i-1+1=i := by omega
    have q := comb_pair ap small (i-1) j (by omega)
    rw [id] at q
    simp only [model,if_pos small]
    refine ⟨q.1,q.2.trans ?_⟩
    simp only [chosen,small,true_and,small.ne,lt_asymm small,false_and,or_false]; omega
  · subst a; simp only [model,lt_irrefl,if_false,if_true,chosen,true_or,or_true,iff_true]
    have eq : quad (i+j)=cost 1 quad i j := by unfold cost quad; push_cast; ring
    exact ⟨eq.le,eq⟩
  · have q := bal_pair big (j-i) i
    rw [show i+(j-i)=j by omega] at q
    simp only [model,if_neg (not_lt.mpr big.le),if_neg big.ne']
    refine ⟨q.1,q.2.trans ?_⟩
    simp only [chosen,not_lt.mpr big.le,false_and,big.ne',false_or,big,true_and]; omega

theorem all_pairs {a : ℝ} (ap : 0 < a) {i j : ℕ} (ip : 0 < i) (jp : 0 < j) :
    model a (i+j) ≤ cost a (model a) i j ∧
      (model a (i+j)=cost a (model a) i j ↔ chosen a i j) := by
  rcases le_total i j with h|h
  · exact left_pair ap ip h
  · rw [Nat.add_comm,cost_symm]
    have q := left_pair ap jp h
    refine ⟨q.1,q.2.trans ?_⟩
    unfold chosen; tauto

theorem model_rec {a : ℝ} (ap : 0 < a) : Recurs a (model a) := by
  constructor
  · unfold model; split_ifs <;> simp [quad,comb1,bal1]
  · intro n hn; constructor
    · rintro i j ip jp rfl; exact (all_pairs ap ip jp).1
    · by_cases small : a<1
      · have id : 1+(n-1)=n := by omega
        refine ⟨1,n-1,by omega,by omega,id,?_⟩
        conv_lhs => rw [←id]
        exact (all_pairs ap (by omega) (by omega)).2.mpr (Or.inl ⟨small,Or.inl rfl⟩)
      · let i := n/2
        let j := n-i
        have id : i+j=n := by dsimp [i,j]; omega
        refine ⟨i,j,by dsimp [i]; omega,by dsimp [i,j]; omega,id,?_⟩
        conv_lhs => rw [←id]
        apply (all_pairs ap (by dsimp [i]; omega) (by dsimp [i,j]; omega)).2.mpr
        rcases eq_or_lt_of_le (le_of_not_gt small) with eq|big
        · exact Or.inr (Or.inl eq.symm)
        · exact Or.inr (Or.inr ⟨big,by dsimp [i,j]; omega,by dsimp [i,j]; omega⟩)

theorem unique {a : ℝ} {x y : ℕ → ℝ} (hx : Recurs a x) (hy : Recurs a y) :
    ∀ n : ℕ, 0 < n → x n=y n := by
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro pos
    by_cases one : n=1
    · simp [one,hx.1,hy.1]
    have hn : 2 ≤ n := by omega
    have subs {i j : ℕ} (ip : 0 < i) (jp : 0 < j) (eq : i+j=n) : cost a x i j=cost a y i j := by
      unfold cost; rw [ih i (by omega) ip,ih j (by omega) jp]
    obtain ⟨i,j,ip,jp,eq,hit⟩ := (hx.2 n hn).2
    obtain ⟨k,l,kp,lp,eq',hit'⟩ := (hy.2 n hn).2
    exact le_antisymm (((hx.2 n hn).1 k l kp lp eq').trans_eq ((subs kp lp eq').trans hit'.symm))
      (((hy.2 n hn).1 i j ip jp eq).trans_eq ((subs ip jp eq).symm.trans hit.symm))

end
end MinRec

namespace MinRec
open OMA.S_mo_143865 Filter Topology Asymptotics
noncomputable section

theorem transfer {f g : ℕ → ℝ} (fm : Monotone f) (gm : Monotone g)
    (gp : ∀ n : ℕ, 2 ≤ n → 0 < g n) {D c C : ℝ} (dp : 0 < D) (cp : 0 < c) (Cp : 0 < C)
    (double : ∀ m : ℕ, 2 ≤ m → g (2*m) ≤ D*g m)
    (rows : ∀ k : ℕ, 1 ≤ k → c*g (2^k) ≤ f (2^k) ∧ f (2^k) ≤ C*g (2^k)) :
    OrderOf f g := by
  refine ⟨c/D/2,2*C*D,by positivity,by positivity,2,?_⟩
  intro n hn
  let k := Nat.log 2 n
  let m : ℕ := 2^k
  have kp : 1 ≤ k := Nat.log_pos (by decide) hn
  have km : 2 ≤ m := Nat.le_trans (by decide : 2 ≤ 2^1) (Nat.pow_le_pow_right (by decide) kp)
  have mn : m ≤ n := Nat.pow_log_le_self _ (by omega)
  have nm : n ≤ 2*m := by
    have h := Nat.lt_pow_succ_log_self (b:=2) (by decide) n
    change n < 2^(k+1) at h; rw [pow_succ,mul_comm] at h; exact h.le
  have s : g n ≤ D*g m := (gm nm).trans (double m km)
  have q : c/D*g n ≤ c*g m := by rw [div_mul_eq_mul_div,div_le_iff₀ dp]; nlinarith only [mul_le_mul_of_nonneg_left s cp.le]
  have r := (rows k kp).1.trans (fm mn)
  have vv : f n ≤ C*(D*g n) := by
    calc f n ≤ f (2^(k+1)) := fm (by simpa [m,pow_succ,mul_comm] using nm)
         _ ≤ _ := (rows (k+1) (by omega)).2
         _ ≤ C*(D*g n) := by
           apply mul_le_mul_of_nonneg_left _ Cp.le
           rw [pow_succ,mul_comm]; exact (double m km).trans (mul_le_mul_of_nonneg_left (gm mn) dp.le)
  have ng := gp n hn
  change c*g m ≤ f n at r
  constructor
  · nlinarith only [q,r,mul_pos (div_pos cp dp) ng]
  · nlinarith only [vv,mul_pos (mul_pos Cp dp) ng]

theorem power_transfer {f : ℕ → ℝ} (fm : Monotone f) {r c C : ℝ} (rp : 0 < r)
    (cp : 0 < c) (Cp : 0 < C)
    (rows : ∀ k : ℕ, 1 ≤ k → c*((2:ℝ)^r)^k ≤ f (2^k) ∧ f (2^k) ≤ C*((2:ℝ)^r)^k) :
    OrderOf f (fun n => (n:ℝ)^r) := by
  have mono : Monotone (fun n : ℕ => (n:ℝ)^r) :=
    fun i j h => Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) rp.le
  apply transfer fm mono (fun n hn => Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _)
    (D:=(2:ℝ)^r) (by positivity) cp Cp
  · intro n _; simp only [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : 0 ≤ (2:ℝ)) (Nat.cast_nonneg n),le_refl]
  · intro k hk
    have eq : (((2^k:ℕ):ℝ)^r)=((2:ℝ)^r)^k := by
      push_cast
      rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm,Real.rpow_mul_natCast (by norm_num)]
    simpa only [eq] using rows k hk

theorem order_congr {f g h : ℕ → ℝ} (eq : ∀ n, 0 < n → f n=g n) (ord : OrderOf g h) : OrderOf f h := by
  obtain ⟨c,C,cp,Cp,N,b⟩ := ord
  refine ⟨c,C,cp,Cp,max N 1,?_⟩
  intro n hn; rw [eq n (by omega)]; exact b n (by omega)

private theorem incompatible {x f g : ℕ → ℝ} (fpos : ∀ n, 2 ≤ n → 0 < g n)
    (lim : Tendsto (fun n => f n/g n) atTop (𝓝 0)) (hf : OrderOf x f) (hg : OrderOf x g) : False := by
  obtain ⟨_,C,_,Cp,N,F⟩ := hf
  obtain ⟨c,_,cp,_,M,G⟩ := hg
  have small := lim.eventually_lt_const (div_pos cp Cp)
  obtain ⟨n,hn,hit⟩ := ((eventually_ge_atTop (max 2 (max N M))).and small).exists
  have lt := (div_lt_iff₀ (fpos n (by omega))).mp hit
  have fin := mul_lt_mul_of_pos_left lt Cp
  have id : C*(c/C*g n)=c*g n := by field_simp
  rw [id] at fin
  linarith only [fin,(F n (by omega)).2,(G n (by omega)).1]

private theorem smaller {r s : ℝ} (rs : r < s) :
    Tendsto (fun n : ℕ => (n:ℝ)^r/(n:ℝ)^s) atTop (𝓝 0) := by
  have lim := (tendsto_rpow_neg_atTop (sub_pos.mpr rs)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply lim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  dsimp
  rw [show -(s-r)=r-s by ring,Real.rpow_sub (by exact_mod_cast (show 0<n by omega))]

theorem power_unique {x : ℕ → ℝ} {r s : ℝ}
    (h : OrderOf x (fun n => (n:ℝ)^r)) (j : OrderOf x (fun n => (n:ℝ)^s)) : r=s := by
  rcases lt_trichotomy r s with lt|eq|gt
  · exact False.elim (incompatible (fun n hn => Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _) (smaller lt) h j)
  · exact eq
  · exact False.elim (incompatible (fun n hn => Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _) (smaller gt) j h)

theorem critical_no_power {x : ℕ → ℝ} (hx : OrderOf x (fun n => (n:ℝ)^2*Real.log n)) (r : ℝ) :
    ¬OrderOf x (fun n => (n:ℝ)^r) := by
  intro hpow
  by_cases le : r ≤ 2
  · obtain ⟨c,_,cp,_,N,low⟩ := hx
    obtain ⟨_,C,_,Cp,M,up⟩ := hpow
    have big := ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (C/c))
    obtain ⟨n,hn,log⟩ := ((eventually_ge_atTop (max 2 (max M N))).and big).exists
    change C/c ≤ Real.log n at log
    have q := (div_le_iff₀ cp).mp log
    have t : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
    have p := Real.rpow_le_rpow_of_exponent_le t le
    norm_num at p
    nlinarith only [(low n (by omega)).1,(up n (by omega)).2,
      mul_le_mul_of_nonneg_left p Cp.le,mul_le_mul_of_nonneg_right q (sq_nonneg (n:ℝ))]
  · have pos : 0 < r-2 := by linarith
    have little := ((isLittleO_log_rpow_atTop pos).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    apply incompatible (fun n hn => Real.rpow_pos_of_pos (by exact_mod_cast (show 0<n by omega)) _) _ hx hpow
    apply little.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp
    have np : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
    rw [Real.rpow_sub np,Real.rpow_two,div_div_eq_mul_div]; ring

end
end MinRec

namespace MinRec
open OMA.S_mo_143865
noncomputable section

def bp (a : ℝ) (k : ℕ) := bal a (2^k)

theorem square_dyad (k : ℕ) : ((2^k:ℕ):ℝ)^2=(4:ℝ)^k := by
  push_cast; rw [pow_two,←mul_pow]; norm_num

theorem bp_next (a : ℝ) (k : ℕ) : bp a (k+1)=2*a*bp a k+2*(4:ℝ)^k := by
  unfold bp; rw [pow_succ,Nat.mul_comm,bal_even,square_dyad]

theorem bp_zero (a : ℝ) : bp a 0=0 := by simp [bp,bal1]
theorem bp_one (a : ℝ) : bp a 1=2 := by rw [bp_next,bp_zero]; ring

theorem bp_identity (a : ℝ) (k : ℕ) :
    (a-2)*bp a k=(2*a)^k-(4:ℝ)^k := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih => rw [bp_next,pow_succ,pow_succ]; nlinarith only [congrArg (fun v : ℝ => 2*a*v) ih]

theorem bp_critical (k : ℕ) : 2*bp 2 k=(k:ℝ)*4^k := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih => rw [bp_next,pow_succ (4:ℝ)]; push_cast; linarith only [ih]

theorem sub_rows {a : ℝ} (ha : 1 ≤ a) (small : a < 2) {k : ℕ} (kp : 1 ≤ k) :
    (1/2:ℝ)*4^k ≤ bp a k ∧ bp a k ≤ (1/(2-a))*4^k := by
  have id := bp_identity a k
  constructor
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have b : 0 ≤ bp a k := by
      have h := bal_mono ha (Nat.zero_le (2^k))
      simpa [bp,bal,pref] using h
    rw [bp_next,pow_succ (4:ℝ)]
    nlinarith only [mul_nonneg (by linarith : 0≤a) b]
  · rw [one_div_mul_eq_div,le_div_iff₀ (by linarith)]
    nlinarith only [id,pow_nonneg (by linarith : 0≤2*a) k]

theorem sup_rows {a : ℝ} (big : 2 < a) {k : ℕ} (kp : 1 ≤ k) :
    (1/a)*(2*a)^k ≤ bp a k ∧ bp a k ≤ (1/(a-2))*(2*a)^k := by
  constructor
  · induction k, kp using Nat.le_induction with
    | base => rw [bp_one,pow_one]; field_simp [ne_of_gt (by linarith : 0 < a)]; norm_num
    | succ k _ ih => rw [bp_next,pow_succ (2*a)]; nlinarith only [mul_le_mul_of_nonneg_right ih (by linarith : 0≤2*a),pow_nonneg (by norm_num : (0:ℝ)≤4) k]
  · rw [one_div_mul_eq_div,le_div_iff₀ (by linarith)]
    nlinarith only [bp_identity a k,pow_nonneg (by norm_num : (0:ℝ)≤4) k]

theorem comb_closed {a : ℝ} (_ha : a ≠ 1) {n : ℕ} (np : 0 < n) :
    (1-a)^2*comb a n=2*((n:ℝ)-1-(n:ℝ)*a+a^n) := by
  induction n, np using Nat.le_induction with
  | base => simp [comb1]
  | succ n h ih =>
    rw [comb_rec _ h,pow_succ a]; push_cast
    nlinarith only [congrArg (fun v : ℝ => a*v) ih]


end
end MinRec

namespace MinRec
open OMA.S_mo_143865
noncomputable section

theorem comb_order {a : ℝ} (ap : 0 < a) (small : a < 1) :
    OrderOf (comb a) (fun n => (n:ℝ)^(1:ℝ)) := by
  have dp : 0 < 1-a := by linarith
  have nonneg (n : ℕ) : 0 ≤ cd a n := by
    induction n with
    | zero => simp [cd]
    | succ k ih => change 0 ≤ a*cd a k+2; positivity
  have low (n : ℕ) (np : 0 < n) : 2*(n:ℝ) ≤ comb a (n+1) := by
    rw [comb_rec _ np]
    have v : 0 ≤ comb a n := by unfold comb pref; exact Finset.sum_nonneg (fun j _ => nonneg j)
    linarith [mul_nonneg ap.le v]
  have high (n : ℕ) (np : 0 < n) : (1-a)*comb a n ≤ 2*(n:ℝ) := by
    induction n, np using Nat.le_induction with
    | base => simp [comb1]
    | succ k kp ih =>
      rw [comb_rec _ kp]; push_cast
      nlinarith only [mul_le_mul_of_nonneg_left ih ap.le]
  refine ⟨1/2,3/(1-a),by norm_num,by positivity,2,?_⟩
  intro n hn
  have l := low (n-1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at l
  rw [Nat.cast_sub (by omega),Nat.cast_one] at l
  have nr : (2:ℝ) ≤ n := by exact_mod_cast hn
  simp only [Real.rpow_one]
  refine ⟨by linarith,?_⟩
  rw [div_mul_eq_mul_div,lt_div_iff₀ dp]
  linarith only [high n (by omega),nr]

theorem quad_order : OrderOf quad (fun n => (n:ℝ)^(2:ℝ)) := by
  refine ⟨1/4,2,by norm_num,by norm_num,2,?_⟩
  intro n hn; dsimp [quad]; rw [Real.rpow_two]
  have h : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  constructor <;> nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]

theorem sub_order {a : ℝ} (ha : 1 ≤ a) (small : a < 2) :
    OrderOf (bal a) (fun n => (n:ℝ)^(2:ℝ)) := by
  apply power_transfer (bal_mono ha) (by norm_num) (c:=1/2) (by norm_num) (C:=1/(2-a)) (one_div_pos.mpr (sub_pos.mpr small))
  intro k hk
  simpa only [bp,Real.rpow_two,show (2:ℝ)^2=4 by norm_num] using sub_rows ha small hk

theorem super_order {a : ℝ} (ha : 2 < a) :
    OrderOf (bal a) (fun n => (n:ℝ)^(1+Real.log a/Real.log 2)) := by
  have ap : 0 < a := by linarith
  have lp : 0 < Real.log a := Real.log_pos (by linarith)
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have eq : (2:ℝ)^(1+Real.log a/Real.log 2)=2*a := by
    rw [Real.rpow_add (by norm_num : 0<(2:ℝ)),Real.rpow_one]
    exact congrArg ((2:ℝ)*·) (Real.rpow_logb (by norm_num) (by norm_num) ap)
  apply power_transfer (bal_mono (by linarith : 1 ≤ a)) (by positivity) (c:=1/a) (by positivity)
    (C:=1/(a-2)) (one_div_pos.mpr (sub_pos.mpr ha))
  intro k hk; rw [eq]; exact sup_rows ha hk

theorem critical_order : OrderOf (bal 2) (fun n => (n:ℝ)^2*Real.log n) := by
  let g (n : ℕ) := (n:ℝ)^2*Real.log n
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have gm : Monotone g := by
    intro i j h
    by_cases z : i=0
    · subst i; simp [g]; exact mul_nonneg (sq_nonneg _) (Real.log_natCast_nonneg _)
    · have ip : 0 < (i:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero z)
      have le : (i:ℝ) ≤ j := by exact_mod_cast h
      exact mul_le_mul (pow_le_pow_left₀ ip.le le 2) (Real.log_le_log ip le) (Real.log_natCast_nonneg _) (sq_nonneg _)
  have gp (n : ℕ) (hn : 2 ≤ n) : 0 < g n := by
    have hh : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
    exact mul_pos (sq_pos_of_pos (by linarith)) (Real.log_pos hh)
  change OrderOf (bal 2) g
  apply transfer (bal_mono (by norm_num)) gm gp (D:=8) (by norm_num)
    (c:=1/(2*Real.log 2)) (by positivity) (C:=1/(2*Real.log 2)) (by positivity)
  · intro m hm; have h : (2:ℝ) ≤ m := by exact_mod_cast hm
    have mp : 0 < (m:ℝ) := by linarith
    dsimp [g]; push_cast; rw [Real.log_mul (by norm_num) mp.ne']
    nlinarith only [mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : 0<(2:ℝ)) h) (sq_nonneg (m:ℝ))]
  · intro k _
    have eq : (1/(2*Real.log 2))*g (2^k)=bp 2 k := by
      dsimp [g]; rw [square_dyad]; push_cast; rw [Real.log_pow]
      field_simp [l2.ne']; nlinarith only [bp_critical k]
    exact ⟨eq.le,eq.ge⟩

end
end MinRec

namespace MinRec
open OMA.S_mo_143865 Filter Topology
noncomputable section

/-- Consecutive second differences of the balanced model encode the
2-adic valuations of consecutive positive integers. -/
theorem curvature (a : ℝ) (n : ℕ) : bd a (n+1)-bd a n=2*a^((n+1).factorization 2) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let k := n/2
    by_cases even : n%2=0
    · have id : n=2*k := by dsimp [k]; omega
      have nd : ¬2 ∣ (2*k+1) := by omega
      rw [id,bd_odd,bd_even,Nat.factorization_eq_zero_of_not_dvd nd]; ring
    · have id : n=2*k+1 := by dsimp [k]; omega
      have sub := ih k (by omega)
      have p : (2*(k+1)).factorization 2=(k+1).factorization 2+1 := by
        rw [Nat.factorization_mul (by decide) (by omega)]
        simp [Nat.prime_two.factorization_self,add_comm]
      rw [id,show 2*k+1+1=2*(k+1) by omega,bd_even,bd_odd,p,pow_succ]
      push_cast; nlinarith only [congrArg (fun v : ℝ => a*v) sub]

private def atom (a : ℝ) (k : ℕ) : ℝ := if k=0 then 0 else 2*a^(k.factorization 2)

private theorem prefix_atom (a : ℝ) (n : ℕ) :
    bd a n=∑ j ∈ Finset.range (n+1), atom a j := by
  induction n with
  | zero => simp [bd0,atom]
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih,atom,if_neg (by omega)]
    linarith only [curvature a n]

/-- A direct finite formula for all problem sizes in the balanced regime. -/
theorem exact_sum (a : ℝ) (n : ℕ) :
    bal a n=∑ j ∈ Finset.range n, ((n:ℝ)-(j:ℝ))*(if j=0 then 0 else 2*a^(j.factorization 2)) := by
  change bal a n=∑ j ∈ Finset.range n, ((n:ℝ)-(j:ℝ))*atom a j
  induction n with
  | zero => simp [bal,pref]
  | succ n ih =>
    change pref (bd a) (n+1)=_
    rw [pref_succ]; change bal a n+bd a n=_
    rw [ih,prefix_atom,Finset.sum_range_succ,Finset.sum_range_succ]
    push_cast
    have term (k : ℕ) : ((n:ℝ)+1-(k:ℝ))*atom a k=((n:ℝ)-(k:ℝ))*atom a k+atom a k := by ring
    simp only [term,Finset.sum_add_distrib]; ring

theorem ray_exact (a : ℝ) (m k : ℕ) : bal a (m*2^k)=(2*a)^k*bal a m+(m:ℝ)^2*bp a k := by
  induction k with
  | zero => simp [bp_zero]
  | succ k ih =>
    rw [show m*2^(k+1)=2*(m*2^k) by rw [pow_succ]; ring,bal_even,ih,bp_next,pow_succ (2*a)]
    push_cast
    have sq := square_dyad k
    push_cast at sq
    rw [mul_pow (m:ℝ) ((2:ℝ)^k),sq]; ring

def powerIndex (a : ℝ) := 1+Real.logb 2 a

theorem base_index {a : ℝ} (ap : 0 < a) : (2:ℝ)^(powerIndex a)=2*a := by
  unfold powerIndex; rw [Real.rpow_add (by norm_num),Real.rpow_one,Real.rpow_logb (by norm_num) (by norm_num) ap]

/-- Each sequence with a fixed positive integer mantissa has an exact limiting
normalized cost in the supercritical range. -/
theorem ray_limit {a : ℝ} (big : 2 < a) (m : ℕ) (mp : 0 < m) :
    Tendsto (fun k : ℕ => bal a (m*2^k)/((m*2^k:ℕ):ℝ)^(powerIndex a))
      atTop (𝓝 ((bal a m+(m:ℝ)^2/(a-2))/(m:ℝ)^(powerIndex a))) := by
  have ap : 0<a := by linarith
  have tp : 0<2*a := by linarith
  have mr : 0 < (m:ℝ) := by exact_mod_cast mp
  have z : Tendsto (fun k : ℕ => (4/(2*a))^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one tp).mpr (by linarith))
  have conv := ((tendsto_const_nhds (x:=bal a m) (f:=atTop)).add
    (((tendsto_const_nhds (x:=(m:ℝ)^2) (f:=atTop)).mul ((tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub z)).div_const (a-2))).div_const ((m:ℝ)^(powerIndex a))
  simp only [sub_zero,mul_one] at conv
  apply conv.congr
  intro k
  have id := bp_identity a k
  have nth : (((2:ℝ)^k)^(powerIndex a))=(2*a)^k := by
    rw [←Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num),base_index ap]
  rw [ray_exact]; push_cast
  rw [Real.mul_rpow mr.le (by positivity),nth,div_pow]
  field_simp [ne_of_gt (sub_pos.mpr big),ne_of_gt (pow_pos tp k),(Real.rpow_pos_of_pos mr (powerIndex a)).ne']
  nlinarith only [congrArg (fun t : ℝ => (m:ℝ)^2*t) id]

private theorem third_gap {a : ℝ} (big : 2 < a) : (3:ℝ)^(powerIndex a) < 1+2*a^2 := by
  let q := Real.logb 2 a
  have qbig : 1 < q := by
    rw [show q=Real.log a/Real.log 2 by rfl,one_lt_div (Real.log_pos (by norm_num))]
    exact Real.log_lt_log (by norm_num) big
  have strict := (strictConvexOn_rpow qbig).slope_strict_mono_adjacent
    (x:=(1:ℝ)) (y:=3) (z:=4) (by simp) (by simp) (by norm_num) (by norm_num)
  have q4 : (4:ℝ)^q=a^2 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.mul_rpow (by norm_num) (by norm_num)]
    rw [show (2:ℝ)^q=a from Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]; ring
  change (3:ℝ)^(1+q) < _
  rw [Real.rpow_add (by norm_num),Real.rpow_one]
  rw [Real.one_rpow,q4] at strict
  norm_num at strict
  linarith

/-- The supercritical Theta estimate cannot be replaced by a single
asymptotic equivalent L*n^r for any constant L. -/
theorem no_leading_constant {a : ℝ} (big : 2 < a) (L : ℝ) :
    ¬Tendsto (fun n : ℕ => bal a n/(n:ℝ)^(powerIndex a)) atTop (𝓝 L) := by
  intro limit
  have ray (m : ℕ) (mp : 0 < m) : Tendsto (fun k : ℕ => m*2^k) atTop atTop := by
    apply tendsto_atTop_mono (f:=fun k : ℕ => 2^k) (fun k => by simpa using Nat.mul_le_mul_right (2^k) mp)
    exact tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have eq (m : ℕ) (mp : 0 < m) : L=(bal a m+(m:ℝ)^2/(a-2))/(m:ℝ)^(powerIndex a) :=
    tendsto_nhds_unique (limit.comp (ray m mp)) (ray_limit big m mp)
  have one := eq 1 (by decide)
  have three := eq 3 (by decide)
  have id : bal a 3=2*a+4 := by
    have v := bal_odd a 1
    have two := bp_one a
    change bal a 2=2 at two
    norm_num [cost,bal1,two] at v; linarith
  rw [bal1] at one
  norm_num at one
  rw [id] at three
  norm_num only [Nat.cast_ofNat] at three
  rw [one] at three
  rw [←one_div] at three
  have mul := (div_eq_div_iff (ne_of_gt (sub_pos.mpr big)) (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) _).ne').mp three
  have inv : (a-2)*(9/(a-2))=9 := by field_simp [ne_of_gt (sub_pos.mpr big)]
  nlinarith only [mul,third_gap big,inv]

end
end MinRec

namespace MinRec
open OMA.S_mo_143865 Filter Topology
noncomputable section

private theorem half_eq (a : ℝ) (n : ℕ) :
    bal a n=cost a (bal a) (n/2) ((n+1)/2) := by
  by_cases par : n%2=0
  · let k := n/2
    have id : n=2*k := by dsimp [k]; omega
    have h : (n+1)/2=k := by dsimp [k]; omega
    calc _ = bal a (2*k) := congrArg _ id
         _ = _ := by rw [bal_even,h]; change _=cost a (bal a) k k; unfold cost; ring
  · let k := n/2
    have id : n=2*k+1 := by dsimp [k]; omega
    have h : (n+1)/2=k+1 := by dsimp [k]; omega
    calc _ = bal a (2*k+1) := congrArg _ id
         _ = _ := by rw [bal_odd,h]

private def err (a : ℝ) (n : ℕ) := (n:ℝ)^2-(2-a)*bal a n

private theorem err_split (a : ℝ) (n : ℕ) : let i := n/2; let j := (n+1)/2
    err a n=a*(err a i+err a j)-(a-1)*((j:ℝ)-i)^2 := by
  intro i j
  have add : (n:ℝ)=(i:ℝ)+j := by exact_mod_cast (show n=i+j by dsimp [i,j]; omega)
  unfold err; rw [half_eq a n,add]; change _-(2-a)*cost a (bal a) i j=_; unfold cost; ring

private theorem sub_error {a : ℝ} (ha : 1 ≤ a) (h : ℕ) : ∀ n : ℕ, 0 < n → n ≤ 2^h →
    1 ≤ err a n ∧ err a n ≤ (2*a)^h := by
  induction h with
  | zero =>
    intro n pos small; have id : n=1 := by simp at small; omega
    simp [id,err,bal1]
  | succ h ih =>
    intro n pos bound
    by_cases one : n=1
    · subst n; simp [err,bal1]
      exact one_le_pow₀ (by linarith : 1≤2*a)
    let i := n/2
    let j := (n+1)/2
    rw [pow_succ] at bound
    have l := ih i (by dsimp [i]; omega) (by dsimp [i]; omega)
    have r := ih j (by dsimp [j]; omega) (by dsimp [j]; omega)
    have hdiff : (j:ℝ)-(i:ℝ)=0 ∨ (j:ℝ)-(i:ℝ)=1 := by
      have : j=i ∨ j=i+1 := by dsimp [i,j]; omega
      rcases this with z|z <;> simp [z]
    have eq : err a n=a*(err a i+err a j)-(a-1)*((j:ℝ)-i)^2 := err_split a n
    rw [eq,pow_succ (2*a)]
    have ml := mul_le_mul_of_nonneg_left (add_le_add l.1 r.1) (by linarith : 0≤a)
    have mr := mul_le_mul_of_nonneg_left (add_le_add l.2 r.2) (by linarith : 0≤a)
    rcases hdiff with z|z <;> rw [z] <;> constructor <;> nlinarith only [ml,mr,ha]

theorem subcritical_limit {a : ℝ} (ha : 1 ≤ a) (small : a < 2) :
    Tendsto (fun n : ℕ => bal a n/(n:ℝ)^2) atTop (𝓝 (1/(2-a))) := by
  have dp : 0<2-a := by linarith
  have ap : 0 < 2*a := by linarith
  have van := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0≤a/2) (by linarith : a/2<1)
  have logtop : Tendsto (Nat.log 2) atTop atTop := by
    apply tendsto_atTop.mpr; intro t
    filter_upwards [eventually_ge_atTop (2^t)] with n hn
    exact Nat.le_log_of_pow_le (by decide) hn
  have shrinking := (van.comp logtop).const_mul (2*a)
  simp only [mul_zero] at shrinking
  have eg : Tendsto (fun n : ℕ => err a n/(n:ℝ)^2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ shrinking
    filter_upwards [eventually_ge_atTop 1] with n np
    let k := Nat.log 2 n
    have low := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have high := Nat.lt_pow_succ_log_self (by decide : 1<2) n
    have errb := sub_error ha (k+1) n np high.le
    have nr : 0 < (n:ℝ) := by exact_mod_cast np
    have le : (4:ℝ)^k ≤ (n:ℝ)^2 := by rw [←square_dyad]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast low) _
    rw [Real.norm_of_nonneg (div_nonneg (by linarith [errb.1]) (sq_nonneg _))]
    change _ ≤ (2*a)*(a/2)^k
    apply (div_le_iff₀ (sq_pos_of_pos nr)).mpr
    calc _ ≤ (2*a)^(k+1) := errb.2
         _ = ((2*a)*(a/2)^k)*4^k := by
           rw [mul_assoc,←mul_pow,show a/2*4=2*a by ring,pow_succ]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left le (by positivity)
  have c := ((tendsto_const_nhds (f:=atTop) (x:=(1:ℝ))).sub eg).div_const (2-a)
  simp only [sub_zero] at c
  apply c.congr'
  filter_upwards [eventually_ge_atTop 1] with n np
  dsimp [err]; field_simp [dp.ne',show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega)]; ring

private def critErr (h n : ℕ) := 2*bal 2 n-(h:ℝ)*(n:ℝ)^2

private theorem critical_box (h : ℕ) : ∀ n : ℕ, n ≤ 2^h →
    |critErr h n| ≤ (4:ℝ)^h-2^h := by
  induction h with
  | zero =>
    intro n bound; simp at bound; interval_cases n <;> simp [critErr,bal,pref,bd0]
  | succ h ih =>
    intro n bound
    let i := n/2
    let j := (n+1)/2
    rw [pow_succ] at bound
    have l := abs_le.mp (ih i (by dsimp [i]; omega))
    have r := abs_le.mp (ih j (by dsimp [j]; omega))
    have sum : (n:ℝ)=(i:ℝ)+j := by exact_mod_cast (show n=i+j by dsimp [i,j]; omega)
    have diff : (j:ℝ)-(i:ℝ)=0 ∨ (j:ℝ)-(i:ℝ)=1 := by
      have : j=i ∨ j=i+1 := by dsimp [i,j]; omega
      rcases this with z|z <;> simp [z]
    have eq : critErr (h+1) n=2*(critErr h i+critErr h j)+((h:ℝ)-1)*((j:ℝ)-i)^2 := by
      unfold critErr; rw [half_eq 2 n,sum]; push_cast
      change 2*cost 2 (bal 2) i j-_=_
      unfold cost; ring
    have hp : (h:ℝ) < (2:ℝ)^h := by exact_mod_cast (Nat.lt_two_pow_self (n:=h))
    have powp : 1 ≤ (2:ℝ)^h := one_le_pow₀ (by norm_num)
    rw [eq,pow_succ (4:ℝ),pow_succ (2:ℝ),abs_le]
    rcases diff with z|z <;> rw [z] <;> constructor <;> nlinarith only [l.1,l.2,r.1,r.2,hp,powp,Nat.cast_nonneg h (α:=ℝ)]

/-- Uniform remainder in the logarithmically corrected critical estimate. -/
theorem critical_remainder {n : ℕ} (np : 0 < n) :
    |2*bal 2 n-(n:ℝ)^2*(Real.logb 2 n)| ≤ 5*(n:ℝ)^2 := by
  let k := Nat.log 2 n
  have l : 2^k ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h : n < 2^(k+1) := Nat.lt_pow_succ_log_self (by decide) n
  have q := abs_le.mp (critical_box (k+1) n h.le)
  have d : (4:ℝ)^k ≤ (n:ℝ)^2 := by
    rw [←square_dyad]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast l) _
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have nr : 0 < (n:ℝ) := by exact_mod_cast np
  have logs : (k:ℝ) ≤ Real.logb 2 n ∧ Real.logb 2 n ≤ (k:ℝ)+1 := by
    unfold Real.logb
    constructor
    · apply (le_div_iff₀ l2).mpr
      rw [←Real.log_pow]; apply Real.log_le_log (by positivity); exact_mod_cast l
    · apply (div_le_iff₀ l2).mpr
      have t := Real.log_le_log nr (by exact_mod_cast h.le : (n:ℝ) ≤ (2:ℝ)^(k+1))
      rw [Real.log_pow] at t; push_cast at t; exact t
  change -_ ≤ 2*bal 2 n-((k+1:ℕ):ℝ)*(n:ℝ)^2 ∧ _ at q
  unfold critErr at q
  push_cast at q
  rw [pow_succ (4:ℝ)] at q
  rw [abs_le]
  constructor <;> nlinarith only [q.1,q.2,d,mul_le_mul_of_nonneg_left logs.1 (sq_nonneg (n:ℝ)),
    mul_le_mul_of_nonneg_left logs.2 (sq_nonneg (n:ℝ)),pow_nonneg (by norm_num : (0:ℝ)≤2) (k+1)]

end
end MinRec

namespace MinRec
open OMA.S_mo_143865 Filter Topology
noncomputable section

theorem comb_limit {a : ℝ} (ap : 0<a) (small : a<1) :
    Tendsto (fun n : ℕ => comb a n/(n:ℝ)) atTop (𝓝 (2/(1-a))) := by
  have dp : 0<1-a := by linarith
  have z := tendsto_pow_atTop_nhds_zero_of_lt_one ap.le small
  have inv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have c := ((tendsto_const_nhds (f:=atTop) (x:=2/(1-a))).add
    (((z.sub (tendsto_const_nhds (x:=(1:ℝ)))).mul inv).const_mul (2/(1-a)^2)))
  simp only [zero_sub,mul_zero,add_zero] at c
  apply c.congr'
  filter_upwards [eventually_ge_atTop 1] with n np
  dsimp
  field_simp [dp.ne',show (n:ℝ)≠0 by exact_mod_cast (show n≠0 by omega)]
  nlinarith only [comb_closed small.ne np]

theorem critical_limit :
    Tendsto (fun n : ℕ => bal 2 n/((n:ℝ)^2*Real.log n)) atTop (𝓝 (1/(2*Real.log 2))) := by
  let A := 1/(2*Real.log 2)
  let f (n : ℕ) := bal 2 n/((n:ℝ)^2*Real.log n)
  have vanish := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))).const_mul (5/2:ℝ)
  simp only [mul_zero] at vanish
  have e : Tendsto (fun n => f n-A) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ vanish
    filter_upwards [eventually_ge_atTop 2] with n hn
    have nr : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have lp := Real.log_pos nr
    have l2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    have np : 0<(n:ℝ)^2 := sq_pos_of_pos (by linarith)
    have eq : f n-A=(2*bal 2 n-(n:ℝ)^2*Real.logb 2 n)/(2*(n:ℝ)^2*Real.log n) := by
      dsimp [f,A,Real.logb]
      field_simp [lp.ne',l2.ne',show (n:ℝ)≠0 by linarith]
    rw [Real.norm_eq_abs,eq,abs_div,abs_of_pos (show 0 < 2*(n:ℝ)^2*Real.log n by positivity)]
    change _ ≤ (5/2:ℝ)*(Real.log n)⁻¹
    apply (div_le_iff₀ (by positivity)).mpr
    calc _ ≤ 5*(n:ℝ)^2 := critical_remainder (by omega)
         _ = _ := by field_simp
  have lim := e.add (tendsto_const_nhds (f:=atTop) (x:=A))
  simpa [f,A] using lim

end
end MinRec

namespace MinRec
open OMA.S_mo_143865
noncomputable section

theorem classification (a : ℝ) (ap : 0 < a) : (∃ x, Recurs a x) ∧ ∀ x, Recurs a x →
    (∀ r : ℝ, 0 < r → (OrderOf x (fun n => (n:ℝ)^r) ↔
      (a < 1 ∧ r=1) ∨ (1 ≤ a ∧ a < 2 ∧ r=2) ∨
        (2 < a ∧ r=1+Real.log a/Real.log 2))) ∧
    (a=2 → OrderOf x (fun n => (n:ℝ)^2*Real.log n)) ∧
    (∀ i j : ℕ, 0 < i → 0 < j →
      (x (i+j)=cost a x i j ↔ chosen a i j)) := by
  have valid := model_rec ap
  refine ⟨⟨model a,valid⟩,?_⟩
  intro x hx
  have eq := unique hx valid
  have critical (a2 : a=2) : OrderOf x (fun n => (n:ℝ)^2*Real.log n) := by
    subst a; apply order_congr eq; simpa [model] using critical_order
  refine ⟨?_,critical,?_⟩
  · intro r _
    rcases lt_trichotomy a 1 with sm|one|gr
    · have h : OrderOf x (fun n => (n:ℝ)^(1:ℝ)) := order_congr eq (by simpa [model,sm] using comb_order ap sm)
      have na : ¬2<a := by linarith
      simp only [sm,true_and,not_le.mpr sm,false_and,na,or_false]
      exact ⟨fun hr => power_unique hr h,fun e => e ▸ h⟩
    · subst a
      have h : OrderOf x (fun n => (n:ℝ)^(2:ℝ)) := order_congr eq (by simpa [model] using quad_order)
      norm_num
      exact ⟨fun hr => power_unique hr h,fun e => e ▸ h⟩
    · rcases lt_trichotomy a 2 with sm|two|big
      · have h : OrderOf x (fun n => (n:ℝ)^(2:ℝ)) := order_congr eq (by simpa [model,gr.ne',not_lt.mpr gr.le] using sub_order gr.le sm)
        simp only [not_lt.mpr gr.le,false_and,gr.le,sm,true_and,not_lt.mpr sm.le,or_false,false_or]
        exact ⟨fun hr => power_unique hr h,fun e => e ▸ h⟩
      · subst a; norm_num; exact critical_no_power (critical rfl) r
      · have h : OrderOf x (fun n => (n:ℝ)^(1+Real.log a/Real.log 2)) := order_congr eq (by simpa [model,gr.ne',not_lt.mpr gr.le] using super_order big)
        simp only [not_lt.mpr gr.le,false_and,big,not_lt.mpr big.le,and_false,true_and,false_or]
        exact ⟨fun hr => power_unique hr h,fun e => e ▸ h⟩
  · intro i j ip jp
    have costeq : cost a x i j=cost a (model a) i j := by unfold cost; rw [eq _ ip,eq _ jp]
    rw [eq _ (by omega),costeq]; exact (all_pairs ap ip jp).2

end
end MinRec

namespace MinRec
open OMA.S_mo_143865 Filter Topology
noncomputable section

/-- Leading-term behavior for every solution of the minimum recurrence. -/
theorem asymptotic_profile {a : ℝ} (ap : 0 < a) {x : ℕ → ℝ} (hx : Recurs a x) :
    (a < 1 → Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (2 / (1-a)))) ∧
    (1 ≤ a → a < 2 → Tendsto (fun n : ℕ => x n / (n : ℝ)^2) atTop (𝓝 (1 / (2-a)))) ∧
    (a = 2 → Tendsto (fun n : ℕ => x n / ((n : ℝ)^2 * Real.log n)) atTop (𝓝 (1 / (2*Real.log 2)))) ∧
    (2 < a → ∀ L : ℝ, ¬Tendsto (fun n : ℕ => x n / (n : ℝ)^(powerIndex a)) atTop (𝓝 L)) := by
  have eq := unique hx (model_rec ap)
  have bal_eq (ha : 1 < a) (n : ℕ) (hn : 1 ≤ n) : x n = bal a n := by
    simpa [model, not_lt.mpr ha.le, ha.ne'] using eq n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ha
    apply (comb_limit ap ha).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [eq n hn, model, ha]
  · intro lo hi
    rcases lo.eq_or_lt with one | upper
    · subst a
      have inv := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      have lim := (tendsto_const_nhds (f := atTop) (x := (1 : ℝ))).sub inv
      norm_num at lim ⊢
      apply lim.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [eq n hn]
      simp only [model, lt_irrefl, if_false, if_true, quad]
      field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega)]
    · apply (subcritical_limit lo hi).congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [bal_eq upper n hn]
  · intro ha
    subst a
    apply critical_limit.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [bal_eq (by norm_num) n hn]
  · intro big L lim
    apply no_leading_constant big L
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [bal_eq (by linarith) n hn]

end
end MinRec

theorem OMA.solution : type_of% @OMA.S_mo_143865.main := MinRec.classification
