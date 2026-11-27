import OMAStatements.S_mo_333090
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

open OMA.S_mo_333090 Filter
namespace PrefixGraph

private theorem path_reaches {k M : ℕ} {s : ℕ → Fin M} {d : ℕ → Fin k}
    (h : ∀ n, edge k M (s n) (d n) (s (n+1))) {i j : ℕ} (hij : i ≤ j) :
    reaches k M (s i) (s j) := by
  intro S hs hc
  induction j, hij using Nat.le_induction with
  | base => exact hs
  | succ n _ ih => exact hc _ ih _ _ (h n)

private theorem forced_period {k M : ℕ} {s : ℕ → Fin M} {d : ℕ → Fin k}
    (h : ∀ n, edge k M (s n) (d n) (s (n+1))) (hn : ¬ branching k M) :
    ∃ i j : ℕ, i < j ∧ ∀ t, d (i+t) = d (j+t) := by
  classical
  have eventual : ∀ᶠ n in atTop, ∀ v : Fin M, s n = v → ∃ᶠ j in atTop, s j = v := by
    apply eventually_all.mpr
    intro v
    by_cases hv : ∃ᶠ j in atTop, s j = v
    · exact Eventually.of_forall (fun _ _ => hv)
    · filter_upwards [not_frequently.mp hv] with n hn' using fun eq => (hn' eq).elim
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventual
  have back (i : ℕ) (hi : N ≤ i) : reaches k M (s (i+1)) (s i) := by
    obtain ⟨j,hj,hv⟩ := frequently_atTop.mp (hN i hi _ rfl) (i+1)
    exact hv ▸ path_reaches h hj
  have unique (i j : ℕ) (hi : N ≤ i) (hj : N ≤ j) (he : s i = s j) : d i = d j := by
    by_contra hd
    exact hn ⟨s i, s (i+1), s (j+1), d i, d j, hd, h i, back i hi, he ▸ h j, he ▸ back j hj⟩
  obtain ⟨a,b,hab,hs⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun i : ℕ => s (N+i)) (fun _ => Set.mem_univ _)
  refine ⟨N+a,N+b,by omega,?_⟩
  have states (t : ℕ) : s (N+a+t) = s (N+b+t) := by
    induction t with
    | zero => simpa using hs
    | succ t ih =>
      have hd := unique _ _ (by omega) (by omega) ih
      have h₁ := (h (N+a+t)).2.2
      have h₂ := (h (N+b+t)).2.2
      rw [ih, hd] at h₁
      exact Fin.ext (h₁.symm.trans h₂)
  intro t
  exact unique _ _ (by omega) (by omega) (states t)

private noncomputable def pref (k : ℕ) (x : ℝ) (n : ℕ) := ⌊(k:ℝ)^n*x⌋₊

private theorem pref_div {k : ℕ} (hk : 0 < k) (x : ℝ) (n : ℕ) :
    pref k x (n+1) / k = pref k x n := by
  unfold pref
  rw [← Nat.floor_div_natCast, pow_succ]
  congr 1
  field_simp

private theorem irrational_digits {k : ℕ} (hk : 1 < k) {x : ℝ} (hx : 0 < x)
    (hir : Irrational x) {i j : ℕ} (hij : i < j)
    (digits : ∀ t, pref k x (i+t+1) % k = pref k x (j+t+1) % k) : False := by
  let f (n : ℕ) : ℝ := (k:ℝ)^n*x - pref k x n
  have bounds (n : ℕ) : 0 ≤ f n ∧ f n < 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)), by
      simpa [f, pref, sub_lt_iff_lt_add, add_comm] using (Nat.lt_floor_add_one ((k:ℝ)^n*x))⟩
  have step_frac (n : ℕ) : f (n+1) = (k:ℝ)*f n - (pref k x (n+1) % k : ℕ) := by
    have h := Nat.mod_add_div (pref k x (n+1)) k
    rw [pref_div (by omega)] at h
    have H : ((pref k x (n+1) % k : ℕ):ℝ) + k * pref k x n = pref k x (n+1) := by exact_mod_cast h
    dsimp [f]
    rw [pow_succ]
    linear_combination H
  have diff (t : ℕ) : f (i+t)-f (j+t) = (k:ℝ)^t*(f i-f j) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show i+(t+1)=i+t+1 by omega, show j+(t+1)=j+t+1 by omega, step_frac, step_frac, digits t, pow_succ]
      linear_combination (k:ℝ)*ih
  have same : f i=f j := by
    by_contra ne
    have hp : 0 < |f i-f j| := abs_pos.mpr (sub_ne_zero.mpr ne)
    obtain ⟨t,ht⟩ := pow_unbounded_of_one_lt (1/|f i-f j|) (show (1:ℝ) < k by exact_mod_cast hk)
    have big := (div_lt_iff₀ hp).mp ht
    have eq := congrArg abs (diff t)
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (k:ℝ)^t by positivity)] at eq
    have lt : |f (i+t)-f (j+t)| < 1 := abs_lt.mpr ⟨by linarith [(bounds (i+t)).1,(bounds (j+t)).2],
      by linarith [(bounds (i+t)).2,(bounds (j+t)).1]⟩
    linarith
  have hp : k^i < k^j := pow_lt_pow_right₀ hk hij
  have hc := hir.mul_intCast (m := ((k^j:ℕ):ℤ) - ((k^i:ℕ):ℤ)) (by omega)
  apply hc.ne_int (((pref k x j:ℕ):ℤ) - ((pref k x i:ℕ):ℤ))
  push_cast
  dsimp [f] at same
  linear_combination -same

private theorem necessary {k M : ℕ} (hk : 2 < k) (hM : 0 < M) {x : ℝ} (hx : 0 < x)
    (hir : Irrational x) (hgood : ∀ n : ℕ, 0 < n → (pref k x n).Coprime M) : branching k M := by
  let y := (k:ℝ)*x
  let p := pref k y
  have good (n : ℕ) : (p n).Coprime M := by
    simpa only [p,y,pref,pow_succ,mul_assoc] using hgood (n+1) (by omega)
  let s (n : ℕ) : Fin M := ⟨p n%M,Nat.mod_lt _ hM⟩
  let d (n : ℕ) : Fin k := ⟨p (n+1)%k,Nat.mod_lt _ (by omega)⟩
  have eg (n : ℕ) : edge k M (s n) (d n) (s (n+1)) := by
    have c (i : ℕ) : (s i).val.Coprime M := by
      simpa [s,Nat.Coprime,Nat.gcd_rec M (p i), Nat.gcd_comm] using good i
    refine ⟨c _,c _,?_⟩
    change (k*(p n%M)+ (p (n+1)%k))%M = p (n+1)%M
    have h := Nat.mod_add_div (p (n+1)) k
    rw [show p (n+1)/k = p n from pref_div (by omega) _ _] at h
    calc
      _ = (k*p n + (p (n+1)%k))%M := by simp [Nat.add_mod, Nat.mul_mod]
      _ = _ := by rw [Nat.add_comm, h]
  by_contra hn
  obtain ⟨i,j,hij,hd⟩ := forced_period eg hn
  exact irrational_digits (x:=y) (by omega : 1 < k) (by dsimp [y]; positivity)
    (hir.natCast_mul (m:=k) (by omega)) hij (fun t => congrArg Fin.val (hd t))


private inductive Trail (k M : ℕ) : Fin M → List (Fin k) → Fin M → Prop where
  | nil (s) : Trail k M s [] s
  | cons {s u t d w} : edge k M s d u → Trail k M u w t → Trail k M s (d::w) t

private theorem Trail.join {k M : ℕ} {s u t : Fin M} {a b : List (Fin k)}
    (p : Trail k M s a u) (q : Trail k M u b t) : Trail k M s (a++b) t := by
  induction p with
  | nil => exact q
  | cons e _ ih => exact .cons e (ih q)

private theorem trail_of_reaches {k M : ℕ} {s t : Fin M} (h : reaches k M s t) :
    ∃ w, Trail k M s w t := by
  classical
  let S := Finset.univ.filter (fun v : Fin M => ∃ w, Trail k M s w v)
  have mem (v) : v ∈ S ↔ ∃ w, Trail k M s w v := by simp [S]
  apply (mem t).mp
  apply h S ((mem s).mpr ⟨[],.nil s⟩)
  intro u hu d v he
  obtain ⟨w,hw⟩ := (mem u).mp hu
  exact (mem v).mpr ⟨w++[d],hw.join (.cons he (.nil _))⟩

private def code {k : ℕ} : List (Fin k) → ℕ
  | [] => 0
  | d::w => k^w.length*d.val+code w

private theorem code_lt {k : ℕ} (_hk : 0 < k) (w : List (Fin k)) : code w < k^w.length := by
  induction w with
  | nil => simp [code]
  | cons d w ih =>
    simp only [code, List.length_cons, pow_succ]
    calc
      _ < k^w.length*d.val + k^w.length := by omega
      _ = k^w.length*(d.val+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ d.isLt

private theorem code_head {k : ℕ} (hk : 0 < k) (d : Fin k) (w : List (Fin k)) :
    code (d::w)/k^w.length = d.val := by
  rw [code, Nat.mul_add_div (pow_pos hk _), Nat.div_eq_of_lt (code_lt hk w), Nat.add_zero]

private theorem pref_div_pow {k : ℕ} (hk : 0 < k) (x : ℝ) (n l : ℕ) :
    pref k x (n+l) / k^l = pref k x n := by
  unfold pref
  rw [← Nat.floor_div_natCast, Nat.cast_pow, pow_add]
  congr 1
  field_simp

private theorem coprime_of_mod {M a r : ℕ} (hm : a%M = r) (hc : r.Coprime M) :
    a.Coprime M := by
  subst r
  simpa [Nat.Coprime,Nat.gcd_rec M a,Nat.gcd_comm] using hc

private theorem replay {k M : ℕ} (hk : 0 < k) {s t : Fin M} {w : List (Fin k)}
    (hw : Trail k M s w t) (x : ℝ) (n : ℕ) (hs : pref k x n % M = s.val)
    (hc : s.val.Coprime M)
    (hend : pref k x (n+w.length) = k^w.length*pref k x n + code w) :
    pref k x (n+w.length) % M = t.val ∧
      ∀ i ≤ w.length, (pref k x (n+i)).Coprime M := by
  induction hw generalizing n with
  | nil =>
    simpa using And.intro hs (coprime_of_mod hs hc)
  | @cons s u t d w e _ ih =>
    have hn : n + (d::w).length = (n+1)+w.length := by simp; omega
    have hwhole : pref k x ((n+1)+w.length) =
        k^w.length*(k*pref k x n+d.val) + code w := by
      rw [← hn, hend]
      simp only [List.length_cons, pow_succ, code]
      ring
    have hnext : pref k x (n+1) = k*pref k x n+d.val := by
      rw [← pref_div_pow hk x (n+1) w.length, hwhole, Nat.mul_add_div (pow_pos hk _),
        Nat.div_eq_of_lt (code_lt hk w), Nat.add_zero]
    have hu : pref k x (n+1)%M = u.val := by
      rw [hnext, ← e.2.2]
      calc
        _ = (k*(pref k x n%M)+d.val)%M := by simp [Nat.add_mod,Nat.mul_mod]
        _ = _ := by rw [hs]
    obtain ⟨ht,hi⟩ := ih (n+1) hu e.2.1 (by rw [hnext]; exact hwhole)
    refine ⟨hn ▸ ht,?_⟩
    intro i hb
    cases i with
    | zero => simpa using coprime_of_mod hs hc
    | succ i =>
      simpa only [Nat.add_right_comm n 1 i, Nat.add_assoc] using hi i (by simpa using hb)

private noncomputable def tailValue (B a b : ℕ) (f : ℕ → Bool) : ℝ :=
  a / ((B:ℝ)-1) + ((b:ℝ)-a)/B * Cardinal.cantorFunction (B:ℝ)⁻¹ f

private theorem values {B a b : ℕ} (hB : 2 < B) (hab : a < b) (hb : b < B) :
    (∀ f, 0 ≤ tailValue B a b f ∧ tailValue B a b f ≤ 1) ∧
    (∀ f, (B:ℝ)*tailValue B a b f =
      (if f 0 then (b:ℝ) else a) + tailValue B a b (fun i => f (i+1))) ∧
    ∃ f, Irrational (tailValue B a b f) := by
  have B2 : 2 < (B:ℝ) := by exact_mod_cast hB
  have B0 : 0 < (B:ℝ) := by linarith
  have B1 : 0 < (B:ℝ)-1 := by linarith
  have h0 : 0 < (B:ℝ)⁻¹ := inv_pos.mpr B0
  have h1 : (B:ℝ)⁻¹ < 1 := (inv_lt_one₀ B0).mpr (by linarith)
  have ab : (a:ℝ) < b := by exact_mod_cast hab
  have coeff : 0 < ((b:ℝ)-a)/B := div_pos (by linarith) B0
  refine ⟨?_,?_,?_⟩
  · intro f
    have lo : 0 ≤ Cardinal.cantorFunction (B:ℝ)⁻¹ f :=
      tsum_nonneg (fun _ => Cardinal.cantorFunctionAux_nonneg h0.le)
    have hi : Cardinal.cantorFunction (B:ℝ)⁻¹ f ≤ (1-(B:ℝ)⁻¹)⁻¹ := by
      rw [← tsum_geometric_of_lt_one h0.le h1]
      apply (Cardinal.summable_cantor_function f h0.le h1).tsum_le_tsum _ (summable_geometric_of_lt_one h0.le h1)
      intro n
      cases he : f n <;> simp [Cardinal.cantorFunctionAux,he]
    unfold tailValue
    refine ⟨add_nonneg (div_nonneg (Nat.cast_nonneg _) B1.le) (mul_nonneg coeff.le lo),?_⟩
    calc
      _ ≤ (a:ℝ)/(B-1) + ((b:ℝ)-a)/B * (1-(B:ℝ)⁻¹)⁻¹ := by gcongr
      _ = (b:ℝ)/(B-1) := by field_simp; ring
      _ ≤ 1 := (div_le_one B1).mpr (by have h' : (b:ℝ)+1 ≤ B := by exact_mod_cast hb
                                       linarith)
  · intro f
    unfold tailValue
    rw [Cardinal.cantorFunction_succ f h0.le h1]
    cases f 0 <;> simp <;> field_simp <;> ring
  · by_contra! h
    choose q hq using fun f => exists_rat_of_not_irrational (h f)
    let : Uncountable (ℕ → Bool) := by
      apply (uncountable_iff_forall_not_surjective).mpr
      intro g sur
      obtain ⟨n,hn⟩ := sur (fun i => !(g i i))
      have hbad := congrFun hn n
      cases v : g n n <;> simp [v] at hbad
    apply not_injective_uncountable_countable q
    intro f g hfg
    have eq : tailValue B a b f = tailValue B a b g := by rw [hq f,hq g,hfg]
    apply Cardinal.cantorFunction_injective h0 (by rw [inv_eq_one_div,div_lt_div_iff₀ B0 (by norm_num)]; linarith)
    exact (mul_right_inj' coeff.ne').mp (add_left_cancel eq)

private theorem from_blocks {k M : ℕ} (hk : 2 < k) {s : Fin M} (hc : s.val.Coprime M)
    {U V : List (Fin k)} (hU : Trail k M s U s) (hV : Trail k M s V s)
    (hlen : V.length = U.length) (hlenpos : 0 < U.length) (hc_lt : code U < code V) :
    ∃ x : ℝ, 0 < x ∧ Irrational x ∧ ∀ n : ℕ, 0 < n → (pref k x n).Coprime M := by
  let L := U.length
  let B := k^L
  have hL : 0 < L := hlenpos
  have hB : 2 < B := lt_of_lt_of_le hk (Nat.le_self_pow (by omega) k)
  have hvB : code V < B := by simpa [B,L,hlen] using code_lt (by omega) V
  obtain ⟨bound,shift,f,hir⟩ := values hB hc_lt hvB
  let T (j : ℕ) := tailValue B (code U) (code V) (fun i => f (i+j))
  let W (j : ℕ) := if f j then V else U
  have wlen (j : ℕ) : (W j).length = L := by dsimp [W,L]; split <;> simp_all
  have trail (j : ℕ) : Trail k M s (W j) s := by dsimp [W]; split <;> assumption
  have turn (j : ℕ) : (B:ℝ)*T j = (code (W j):ℝ)+T (j+1) := by
    simpa [T,W,apply_ite,Nat.add_right_comm,Nat.add_assoc, Nat.add_left_comm] using
      shift (fun i => f (i+j))
  let x : ℝ := s.val + T 0
  have hT : Irrational (T 0) := by simpa [T] using hir
  have hx : Irrational x := hT.natCast_add _
  have xpos : 0 < x := lt_of_le_of_ne (add_nonneg (Nat.cast_nonneg _) (bound _).1) hx.ne_zero.symm
  let z : ℕ → ℕ := Nat.rec (motive := fun _ => ℕ) s.val (fun j p => B*p + code (W j))
  have expand (j : ℕ) : (k:ℝ)^(j*L)*x = (@Nat.cast ℝ _ (z j)) + T j := by
    induction j with
    | zero => simp [z,x]
    | succ j ih =>
      rw [Nat.succ_mul,pow_add,mul_right_comm,ih]
      change ((@Nat.cast ℝ _ (z j))+T j)*(k:ℝ)^L = ((B*z j+code (W j):ℕ):ℝ)+T (j+1)
      have eq := turn j
      have powB : (k:ℝ)^L = B := by dsimp [B]; norm_cast
      rw [powB]; push_cast; linear_combination eq
  have atBlock (j : ℕ) : pref k x (j*L) = z j := by
    have irr := hx.natCast_mul (m:=k^(j*L)) (by positivity)
    have olt : T j < 1 := lt_of_le_of_ne (bound _).2 (by
      intro er
      apply irr.ne_nat (z j+1)
      push_cast
      rw [expand,er])
    unfold pref
    rw [expand]
    apply (Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg _) (bound _).1)).mpr
    constructor <;> linarith [(bound (fun i => f (i+j))).1]
  have next (j : ℕ) : pref k x (j*L+(W j).length) =
      k^(W j).length*pref k x (j*L)+code (W j) := by
    rw [wlen,← Nat.succ_mul,atBlock,atBlock]
  have residue (j : ℕ) : pref k x (j*L)%M = s.val := by
    induction j with
    | zero => rw [atBlock]; exact Nat.mod_eq_of_lt s.isLt
    | succ j ih =>
      simpa only [wlen,Nat.succ_mul] using (replay (by omega) (trail j) x (j*L) ih hc (next j)).1
  refine ⟨x,xpos,hx,?_⟩
  intro n _
  have valid := (replay (by omega) (trail (n/L)) x _ (residue _) hc (next _)).2 (n%L)
    (by rw [wlen]; exact (Nat.mod_lt _ hL).le)
  simpa only [Nat.div_add_mod'] using valid

end PrefixGraph

theorem OMA.solution : type_of% @OMA.S_mo_333090.main := by
  intro k M hk _ hM
  constructor
  · rintro ⟨x,hx,hi,hg⟩
    exact PrefixGraph.necessary hk hM hx hi hg
  · rintro ⟨s,u,v,d,e,de,edu,us,eev,vs⟩
    obtain ⟨a,ha⟩ := PrefixGraph.trail_of_reaches us
    obtain ⟨b,hb⟩ := PrefixGraph.trail_of_reaches vs
    have A := PrefixGraph.Trail.cons edu ha
    have B := PrefixGraph.Trail.cons eev hb
    have AB := A.join B
    have BA := B.join A
    have len : ((e::b)++(d::a)).length = ((d::a)++(e::b)).length := by simp only [List.length_append,List.length_cons]; omega
    have diff : PrefixGraph.code ((d::a)++(e::b)) ≠ PrefixGraph.code ((e::b)++(d::a)) := by
      intro eq
      apply de
      apply Fin.ext
      rw [← PrefixGraph.code_head (by omega) d (a++(e::b)),← PrefixGraph.code_head (by omega) e (b++(d::a))]
      change PrefixGraph.code ((d::a)++(e::b)) / _ = PrefixGraph.code ((e::b)++(d::a)) / _
      rw [eq]
      simp [Nat.add_left_comm]
    rcases lt_or_gt_of_ne diff with h|h
    · exact PrefixGraph.from_blocks hk edu.1 AB BA len (by simp) h
    · exact PrefixGraph.from_blocks hk edu.1 BA AB len.symm (by simp) h
