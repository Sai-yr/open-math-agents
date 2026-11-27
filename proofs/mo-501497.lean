import OMAStatements.S_mo_501497

/-!
# Contraction across a common terminal interval

The quantity (x−y)²/(xy) never increases under x ↦ ax+1/x. In two
consecutive steps at least one of the products xy is at least 1. On a block
of order n steps with remaining horizon comparable to n this yields a relative
decrease of order 1/√n per pair. The input range grows only polynomially.
-/

open OMA.S_mo_501497 Filter
open scoped Topology

private noncomputable def F (a x : ℝ) := a*x + 1/x
private noncomputable def distQ (x y : ℝ) := (x-y)^2/(x*y)

private lemma fp {a x : ℝ} (ha : 0<a) (hx : 0<x) : 0 < F a x := by
  unfold F; positivity

private lemma f_sq {a x : ℝ} (hx : x≠0) : (F a x)^2 = a^2*x^2 + 2*a + (1/x)^2 := by
  unfold F; field_simp; ring

private lemma f_lower {a x : ℝ} (ha : 0<a) (hx : 0<x) : 2*Real.sqrt a ≤ F a x := by
  have he : F a x = (a*x^2+1)/x := by unfold F;field_simp
  rw [he]
  apply (le_div_iff₀ hx).2
  nlinarith [sq_nonneg (Real.sqrt a*x-1),
    (show (Real.sqrt a*x)^2 = a*x^2 by rw [mul_pow,Real.sq_sqrt ha.le])]

private lemma distQ_nonneg {x y : ℝ} (hx : 0<x) (hy : 0<y) : 0 ≤ distQ x y :=
  div_nonneg (sq_nonneg _) (mul_pos hx hy).le

private lemma dist_identity {a x y : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) :
    distQ (F a x) (F a y) =
      distQ x y * ((a*(x*y)-1)^2/((1+a*x^2)*(1+a*y^2))) := by
  have hx' : 0 < a*x^2+1 := by positivity
  have hy' : 0 < a*y^2+1 := by positivity
  unfold distQ F
  field_simp [hx.ne',hy.ne',hx'.ne',hy'.ne',add_comm 1 (a*x^2),add_comm 1 (a*y^2)]
  ring

private lemma dist_factor {a x y : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) :
    distQ (F a x) (F a y) ≤ distQ x y * ((a*(x*y)-1)^2/(1+a*(x*y))^2) := by
  rw [dist_identity ha hx hy]
  apply mul_le_mul_of_nonneg_left _ (distQ_nonneg hx hy)
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [mul_nonneg ha.le (sq_nonneg (x-y))]

private lemma q_nonexpansive {a x y : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) :
    distQ (F a x) (F a y) ≤ distQ x y := by
  apply (dist_factor ha hx hy).trans
  apply mul_le_of_le_one_right (distQ_nonneg hx hy)
  apply (div_le_one (by positivity)).2
  nlinarith [mul_pos ha (mul_pos hx hy)]

private lemma after_pair {a x y : ℝ} (ha : 0<a) (hx : 0<x) (hy : 0<y) :
    1 ≤ x*y ∨ 1 ≤ F a x * F a y := by
  by_cases h : 1 ≤ x*y
  · exact Or.inl h
  · right
    calc
      1 ≤ 1/(x*y) := (one_le_div (mul_pos hx hy)).2 (le_of_not_ge h)
      _ = (1/x)*(1/y) := by ring
      _ ≤ F a x * F a y := by unfold F; apply mul_le_mul <;> first | positivity | linarith [mul_pos ha hx,mul_pos ha hy]

private def box (A B : ℝ) (m : ℕ) (x : ℝ) : Prop :=
  0<x ∧ x^2 ≤ B*((m:ℝ)+1) ∧ (1/x)^2 ≤ A*((m:ℝ)+1)

private lemma positive_finish {c x : ℝ} (hc : 0<c) (hx : 0<x) (m : ℕ) :
    0 < finish c m x := by
  induction m generalizing x with
  | zero => exact hx
  | succ m ih => exact ih (fp (by positivity) hx)

private lemma nonexpansive_finish {c x y : ℝ} (hc : 0<c) (hx : 0<x) (hy : 0<y) (m : ℕ) :
    distQ (finish c m x) (finish c m y) ≤ distQ x y := by
  induction m generalizing x y with
  | zero => exact le_rfl
  | succ m ih =>
    have ha : 0<c/Real.sqrt ((m:ℝ)+1) := by positivity
    exact (ih (fp ha hx) (fp ha hy)).trans (q_nonexpansive ha hx hy)

private lemma initial_box {A B b : ℝ} (hb : 0<b) (hA : (1/b)^2 ≤ A) (hB : b^2 ≤ B) (m : ℕ) :
    box A B m (b * Real.sqrt (Real.sqrt ((m:ℝ)+1))) := by
  let v := (m:ℝ)+1
  have hv : 1 ≤ v := by dsimp [v]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hs : 1 ≤ Real.sqrt v := by simpa using Real.sqrt_le_sqrt hv
  have ht : 1 ≤ Real.sqrt (Real.sqrt v) := by simpa using Real.sqrt_le_sqrt hs
  have hz : 0 < Real.sqrt (Real.sqrt v) := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · change (b*Real.sqrt (Real.sqrt v))^2 ≤ B*v
    rw [mul_pow,Real.sq_sqrt (Real.sqrt_nonneg _)]
    apply mul_le_mul hB _ (Real.sqrt_nonneg _) (le_trans (sq_nonneg _) hB)
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ v),mul_nonneg (sub_nonneg.mpr hs) (Real.sqrt_nonneg v)]
  · change (1/(b*Real.sqrt (Real.sqrt v)))^2 ≤ A*v
    have hdiv : 1/(b*Real.sqrt (Real.sqrt v)) ≤ 1/b :=
      one_div_le_one_div_of_le hb (by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr ht)])
    calc
      _ ≤ (1/b)^2 := by gcongr
      _ ≤ A := hA
      _ ≤ A*v := le_mul_of_one_le_right ((sq_nonneg _).trans hA) hv

private lemma step_box {A B c : ℝ} {m : ℕ} {x : ℝ}
    (hc : 0<c) (hA : 1/(4*c) ≤ A) (hAB : 4*A ≤ B)
    (hK : 2*c^2*B+2*c ≤ B/2*((m:ℝ)+1)) (hx : box A B (m+1) x) :
    box A B m (F (c/Real.sqrt ((m:ℝ)+1)) x) := by
  let w := (m:ℝ)+1
  have hw : 1 ≤ w := by dsimp [w]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hwp : 0<w := by linarith
  have hR := Real.sqrt_pos.2 hwp
  have hR1 : 1 ≤ Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
  have hRle : Real.sqrt w ≤ w := by
    nlinarith [Real.sq_sqrt hwp.le, mul_nonneg hR.le (sub_nonneg.mpr hR1)]
  have hAp : 0<A := (by positivity : 0<1/(4*c)).trans_le hA
  have hBp : 0<B := by linarith
  obtain ⟨hxp, hx2, hxi⟩ := hx
  push_cast at hx2 hxi
  change x^2 ≤ B*(w+1) at hx2
  change (1/x)^2 ≤ A*(w+1) at hxi
  let a := c/Real.sqrt w
  have ha : 0<a := div_pos hc hR
  have hac : a ≤ c := div_le_self hc.le hR1
  have hsq : a^2*w = c^2 := by dsimp [a];rw [div_pow,Real.sq_sqrt hwp.le];field_simp
  refine ⟨fp ha hxp, ?_, ?_⟩
  · change (F a x)^2 ≤ B*w
    rw [f_sq hxp.ne']
    have h1 : a^2*x^2 ≤ 2*c^2*B := calc
      _ ≤ a^2*(B*(2*w)) := mul_le_mul_of_nonneg_left (hx2.trans (by nlinarith [mul_nonneg hBp.le (sub_nonneg.mpr hw)])) (sq_nonneg a)
      _ = _ := by linear_combination 2*B*hsq
    change 2*c^2*B+2*c ≤ B/2*w at hK
    nlinarith [
      mul_nonneg (sub_nonneg.mpr hAB) hwp.le,mul_nonneg hAp.le (sub_nonneg.mpr hw)]
  · change (1/F a x)^2 ≤ A*w
    have hh := f_lower ha hxp
    have hpow := pow_le_pow_left₀ (show 0 ≤ 2*Real.sqrt a by positivity) hh 2
    have hs : 4*a ≤ (F a x)^2 := by nlinarith [Real.sq_sqrt ha.le]
    rw [div_pow,one_pow]
    calc
      1/(F a x)^2 ≤ 1/(4*a) := one_div_le_one_div_of_le (by positivity) hs
      _ = (1/(4*c))*Real.sqrt w := by dsimp [a];field_simp
      _ ≤ A*w := mul_le_mul hA hRle hR.le hAp.le

private lemma factor_gap {z δ : ℝ} (hz : 0<z) (hδ : 0 ≤ δ) (hlo : δ ≤ z) (hhi : δ*z ≤ 1) :
    (z-1)^2/(1+z)^2 ≤ 1-δ := by
  apply (div_le_iff₀ (by positivity)).2
  have hh : δ*(1+z)^2 ≤ 4*z := by
    by_cases h : z ≤ 1
    · calc
        _ ≤ δ*4 := by gcongr; nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 3+z by linarith)]
        _ ≤ _ := by linarith
    · calc
        _ ≤ δ*(4*z^2) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          nlinarith [mul_nonneg (by linarith : 0 ≤ z-1) (by linarith : 0 ≤ 3*z+1)]
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hz.le]
  nlinarith

private noncomputable def update (c : ℝ) (m : ℕ) := F (c/Real.sqrt ((m:ℝ)+1))

private lemma gain {A B c η : ℝ} {n m : ℕ} {x y : ℝ} (hc : 0<c) (hB : 0<B) (hη : 0<η)
    (hηc : η ≤ c) (hηB : η*(2*c*B) ≤ 1) (hn : 0<n) (hm : m+1 ≤ 9*n)
    (hx : box A B (m+1) x) (hy : box A B (m+1) y) (hxy : 1 ≤ x*y) :
    distQ (update c m x) (update c m y) ≤ (1-η/(3*Real.sqrt n))*distQ x y := by
  let w := (m:ℝ)+1
  let a := c/Real.sqrt w
  have hw : 1 ≤ w := by dsimp [w];linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hwp : 0<w := by linarith
  have hR := Real.sqrt_pos.2 hwp
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hS := Real.sqrt_pos.2 hn'
  have hW : w ≤ 9*(n:ℝ) := by dsimp [w];exact_mod_cast hm
  have hRS : Real.sqrt w ≤ 3*Real.sqrt n := by
    nlinarith [Real.sq_sqrt hwp.le,Real.sq_sqrt hn'.le]
  obtain ⟨hxp,hx2,-⟩ := hx
  obtain ⟨hyp,hy2,-⟩ := hy
  push_cast at hx2 hy2
  change x^2 ≤ B*(w+1) at hx2
  change y^2 ≤ B*(w+1) at hy2
  have hprod : x*y ≤ 2*B*w := by nlinarith [sq_nonneg (x-y),mul_nonneg hB.le (sub_nonneg.mpr hw)]
  have ha : 0<a := div_pos hc hR
  have hl : η/(3*Real.sqrt n) ≤ a*(x*y) := by
    calc
      _ ≤ c/Real.sqrt w := div_le_div₀ hc.le hηc hR hRS
      _ ≤ _ := le_mul_of_one_le_right ha.le hxy
  have hu : a*(x*y) ≤ (2*c*B)*(3*Real.sqrt n) := by
    calc
      _ ≤ a*(2*B*w) := mul_le_mul_of_nonneg_left hprod ha.le
      _ = (2*c*B)*Real.sqrt w := by dsimp [a];field_simp;rw [Real.sq_sqrt hwp.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left hRS (by positivity)
  have hfac : η/(3*Real.sqrt n)*(a*(x*y)) ≤ 1 := by
    calc
      _ ≤ (η/(3*Real.sqrt n))*((2*c*B)*(3*Real.sqrt n)) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = η*(2*c*B) := by field_simp
      _ ≤ 1 := hηB
  apply (dist_factor ha hxp hyp).trans
  rw [mul_comm (1-_)]
  apply mul_le_mul_of_nonneg_left _ (distQ_nonneg hxp hyp)
  exact factor_gap (mul_pos ha (mul_pos hxp hyp)) (by positivity) hl hfac

private def stable (A B c : ℝ) (K : ℕ) : Prop :=
  ∀ m, K ≤ m → ∀ x, box A B (m+1) x → box A B m (update c m x)

private lemma align {A B c : ℝ} {K m N : ℕ} (hkeep : stable A B c K) (hK : K ≤ m)
    (hNm : m ≤ N) {x : ℝ} (hx : box A B N x) :
    ∃ z, box A B m z ∧ finish c N x = finish c m z := by
  induction N generalizing x with
  | zero =>
    obtain rfl : m=0 := by omega
    exact ⟨x,hx,rfl⟩
  | succ N ih =>
    by_cases h : m=N+1
    · subst m;exact ⟨x,hx,rfl⟩
    · exact ih (by omega) (hkeep N (by omega) x hx)

private lemma pairs {A B c η : ℝ} {n K : ℕ} (hc : 0<c) (hB : 0<B) (hη : 0<η)
    (hηc : η ≤ c) (hηB : η*(2*c*B) ≤ 1) (hn : 0<n)
    (hδ : 0 ≤ 1-η/(3*Real.sqrt n)) (hkeep : stable A B c K) (j k : ℕ)
    (hk : K ≤ k) (hm : 2*j+k ≤ 9*n) {x y : ℝ}
    (hx : box A B (2*j+k) x) (hy : box A B (2*j+k) y) :
    distQ (finish c (2*j+k) x) (finish c (2*j+k) y) ≤ 
      (1-η/(3*Real.sqrt n))^j * distQ x y := by
  induction j generalizing x y with
  | zero => simpa using nonexpansive_finish hc hx.1 hy.1 k
  | succ j ih =>
    let m := 2*j+k
    have hindex : 2*(j+1)+k=m+2 := by dsimp [m];omega
    rw [hindex] at hx hy hm ⊢
    have hmK : K ≤ m := by dsimp [m];omega
    let u := update c (m+1) x
    let v := update c (m+1) y
    let u' := update c m u
    let v' := update c m v
    have hu : box A B (m+1) u := hkeep _ (by omega) x hx
    have hv : box A B (m+1) v := hkeep _ (by omega) y hy
    have hu' : box A B m u' := hkeep _ hmK _ hu
    have hv' : box A B m v' := hkeep _ hmK _ hv
    let α := 1-η/(3*Real.sqrt n)
    have hp : distQ u' v' ≤ α*distQ x y := by
      obtain h | h := after_pair (a := c/Real.sqrt ((m+1:ℕ)+1:ℝ)) (by positivity) hx.1 hy.1
      · exact (q_nonexpansive (by positivity) hu.1 hv.1).trans (gain hc hB hη hηc hηB hn hm hx hy h)
      · have h' : 1 ≤ u*v := h
        exact (gain hc hB hη hηc hηB hn (by omega) hu hv h').trans
          (mul_le_mul_of_nonneg_left (q_nonexpansive (by positivity) hx.1 hy.1) hδ)
    calc
      _ ≤ α^j*distQ u' v' := ih (by omega) hu' hv'
      _ ≤ α^j*(α*distQ x y) := mul_le_mul_of_nonneg_left hp (pow_nonneg hδ _)
      _ = _ := by rw [pow_succ];ring

private lemma box_dist {A B x y : ℝ} {m : ℕ} (hx : box A B m x) (hy : box A B m y) :
    distQ x y ≤ (A+B)*((m:ℝ)+1) := by
  obtain ⟨hxp,hx,hxi⟩ := hx
  obtain ⟨hyp,hy,hyi⟩ := hy
  have he : distQ x y = x*(1/y)+y*(1/x)-2 := by unfold distQ;field_simp;ring
  rw [he]
  nlinarith [sq_nonneg (x-1/y),sq_nonneg (y-1/x)]

private lemma power_bound {n : ℕ} {η : ℝ} (hn : 0<n) (hη : 0<η)
    (hδ : 0 ≤ 1-η/(3*Real.sqrt n)) :
    (1-η/(3*Real.sqrt n))^(4*n) ≤ 81/(η^4*(n:ℝ)^2) := by
  let δ := η/(3*Real.sqrt n)
  have hp : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hs := Real.sqrt_pos.2 hp
  have hd : 0<δ := by dsimp [δ];positivity
  have hsum : 0<1+δ := by linarith
  have h1 : (1-δ)^n ≤ 1/((n:ℝ)*δ) := by
    apply (le_div_iff₀ (mul_pos hp hd)).2
    calc
      _ ≤ (1-δ)^n*(1+δ)^n := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
        linarith [one_add_mul_le_pow (by linarith : -2 ≤ δ) n]
      _ = ((1-δ)*(1+δ))^n := (mul_pow ..).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg hδ hsum.le) (by nlinarith [sq_nonneg δ])
  have hfact : (n:ℝ)*δ=η*Real.sqrt n/3 := by
    dsimp [δ];field_simp;rw [Real.sq_sqrt hp.le]
  change (1-δ)^(4*n) ≤ _
  rw [Nat.mul_comm 4 n,pow_mul]
  calc
    _ ≤ (1/((n:ℝ)*δ))^4 := pow_le_pow_left₀ (pow_nonneg hδ _) h1 _
    _ = _ := by
      rw [hfact]
      field_simp
      nlinarith [show (Real.sqrt n)^4 = (n:ℝ)^2 by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt hp.le]]

private noncomputable def line (b c : ℝ) (m : ℕ) :=
  finish c m (b*Real.sqrt (Real.sqrt ((m:ℝ)+1)))

private lemma terminal_difference {A B c η b : ℝ} {K n i j : ℕ}
    (hc : 0<c) (hb : 0<b) (hA : 0<A) (hB : 0<B) (hiA : (1/b)^2 ≤ A)
    (hiB : b^2 ≤ B) (hη : 0<η) (hη1 : η ≤ 1) (hηc : η ≤ c) (hηB : η*(2*c*B) ≤ 1)
    (hkeep : stable A B c K) (hn : 0<n) (hKn : K ≤ n) (hi : 9*n ≤ i) (hj : 9*n ≤ j) :
    distQ (line b c i) (line b c j) ≤ (810*(A+B)/η^4)/(n:ℝ) := by
  obtain ⟨x,hx,hix⟩ := align hkeep (m:=9*n) (by omega) hi (initial_box hb hiA hiB i)
  obtain ⟨y,hy,hjy⟩ := align hkeep (m:=9*n) (by omega) hj (initial_box hb hiA hiB j)
  unfold line
  rw [hix,hjy]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0<(n:ℝ) := by linarith
  have hS : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hn1
  have hδ : 0 ≤ 1-η/(3*Real.sqrt n) := by
    have := (div_le_one (by positivity : 0<3*Real.sqrt n)).2 (show η ≤ 3*Real.sqrt n by linarith)
    linarith
  have hd := power_bound hn hη hδ
  have hix' : 2*(4*n)+n=9*n := by omega
  have hz := pairs hc hB hη hηc hηB hn hδ hkeep (4*n) n hKn hix'.le
    (hix' ▸ hx) (hix' ▸ hy)
  rw [hix'] at hz
  have hxy : distQ x y ≤ (A+B)*(10*(n:ℝ)) := by
    apply (box_dist hx hy).trans
    push_cast
    gcongr
    linarith
  calc
    _ ≤ _ := hz
    _ ≤ (81/(η^4*(n:ℝ)^2))*((A+B)*(10*(n:ℝ))) :=
      mul_le_mul hd hxy (distQ_nonneg hx.1 hy.1) (by positivity)
    _ = _ := by field_simp;ring

private lemma cauchy_of_distQ {u : ℕ → ℝ} (hu : ∀ n, 0<u n)
    (hclose : ∀ ε>0, ∃ N : ℕ, ∀ i≥N, ∀ j≥N, distQ (u i) (u j)<ε) : CauchySeq u := by
  obtain ⟨N,hN⟩ := hclose 1 zero_lt_one
  let M := 3*u N
  have hM : 0<M := by dsimp [M];positivity [hu N]
  have hbound (i : ℕ) (hi : N ≤ i) : u i ≤ M := by
    have h := (div_lt_iff₀ (mul_pos (hu i) (hu N))).mp (hN i hi N le_rfl)
    dsimp [M]
    by_contra! h'
    nlinarith [mul_nonneg (hu i).le (sub_nonneg.mpr h'.le),sq_nonneg (u N)]
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨L,hL⟩ := hclose ((ε/M)^2) (by positivity)
  refine ⟨max N L, ?_⟩
  intro i hi j hj
  have h := (div_lt_iff₀ (mul_pos (hu i) (hu j))).mp (hL i (by omega) j (by omega))
  have hm : u i*u j ≤ M*M := mul_le_mul (hbound i (by omega)) (hbound j (by omega)) (hu j).le hM.le
  have hs : (u i-u j)^2 < ε^2 := calc
    _ < _ := h
    _ ≤ (ε/M)^2*(M*M) := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
    _ = _ := by field_simp
  rw [Real.dist_eq]
  simpa [abs_of_pos hε] using (sq_lt_sq.mp hs)

private lemma lower_finish {c x : ℝ} (hc : 0<c) (hx : 0<x) (n : ℕ) :
    2*Real.sqrt c ≤ finish c (n+1) x := by
  induction n generalizing x with
  | zero => simpa [finish,F] using f_lower hc hx
  | succ n ih => exact ih (fp (by positivity) hx)

private lemma line_tendsto {b c : ℝ} (hb : 0<b) (hc : 0<c) :
    ∃ u : ℝ, 2*Real.sqrt c ≤ u ∧ Tendsto (line b c) atTop (𝓝 u) := by
  let A := 1+1/(4*c)+(1/b)^2+b^2
  let B := 4*A
  have hA : 0<A := by dsimp [A];positivity
  have hB : 0<B := by dsimp [B];positivity
  have hAi : (1/b)^2 ≤ A := by dsimp [A]; nlinarith [sq_nonneg b,show 0<1/(4*c) by positivity]
  have hBi : b^2 ≤ B := by dsimp [A,B];nlinarith [sq_nonneg b,sq_nonneg (1/b),show 0<1/(4*c) by positivity]
  have hAc : 1/(4*c) ≤ A := by dsimp [A];nlinarith [sq_nonneg b,sq_nonneg (1/b)]
  obtain ⟨K,hK⟩ := exists_nat_ge ((2*c^2*B+2*c)/(B/2))
  have hkeep : stable A B c K := by
    intro m hm x hx
    apply step_box hc hAc (le_refl B) _ hx
    have hh := (div_le_iff₀ (by positivity : 0<B/2)).mp hK
    have hm' : (K:ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hm')]
  let η := min 1 (min c (1/(2*c*B)))
  have hη : 0<η := by dsimp [η];positivity
  have hη1 : η ≤ 1 := min_le_left .. 
  have hηc : η ≤ c := (min_le_right ..).trans (min_le_left ..)
  have hηB : η*(2*c*B) ≤ 1 := (le_div_iff₀ (by positivity)).mp ((min_le_right ..).trans (min_le_right ..))
  let E := 810*(A+B)/η^4
  have hE : 0<E := by dsimp [E];positivity
  have hu (i : ℕ) : 0<line b c i := positive_finish hc (by positivity) i
  have hclose : ∀ ε>0, ∃ N : ℕ, ∀ i≥N, ∀ j≥N, distQ (line b c i) (line b c j)<ε := by
    intro ε he
    obtain ⟨m,hm⟩ := exists_nat_gt (E/ε)
    let n := max K (m+1)
    have hn : 0<n := by dsimp [n];omega
    have hp : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    have hmn : (m:ℝ) ≤ n := by exact_mod_cast (show m ≤ n by dsimp [n];omega)
    refine ⟨9*n,fun i hi j hj => ?_⟩
    apply (terminal_difference hc hb hA hB hAi hBi hη hη1 hηc hηB hkeep hn (le_max_left ..) hi hj).trans_lt
    change E/(n:ℝ)<ε
    apply (div_lt_iff₀ hp).2
    nlinarith [(div_lt_iff₀ he).mp hm,mul_nonneg he.le (sub_nonneg.mpr hmn)]
  obtain ⟨u,hlim⟩ := cauchySeq_tendsto_of_complete (cauchy_of_distQ hu hclose)
  refine ⟨u, ?_, hlim⟩
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1] with i hi
  cases i with
  | zero => omega
  | succ i => exact lower_finish hc (by positivity) i

theorem OMA.solution : type_of% @OMA.S_mo_501497.main := by
  intro R L hR hL
  obtain ⟨u,hu,hlim⟩ := line_tendsto (b:=Real.sqrt (L/R)/2) (c:=R/L) (by positivity) (by positivity)
  refine ⟨u,hu,(tendsto_add_atTop_iff_nat 1).mp ?_⟩
  change Tendsto (fun n : ℕ => finish (R/L) n (Real.sqrt (L/R)/2 * Real.sqrt (Real.sqrt ((n:ℝ)+1)))) atTop (𝓝 u) at hlim
  simpa [terminal] using hlim
